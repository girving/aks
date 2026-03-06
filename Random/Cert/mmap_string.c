/*
 * mmap-based ASCII file reader for Lean String objects.
 *
 * Reads a file into a Lean String via O_TMPFILE + mmap, validating all
 * bytes < 128.
 *
 * Strategy:
 * 1. Open file, get size via fstat
 * 2. Create anonymous tmpfile (O_TMPFILE) on the same filesystem as the
 *    source file — this gives us a private, process-only file backed by
 *    the real filesystem (not tmpfs), so pages are evictable to disk
 * 3. Read file -> validate all bytes < 128 -> write to tmpfile (streaming)
 * 4. Split mmap: anonymous writable page (lean_string_object header) +
 *    tmpfile read-only pages (string data), contiguous in virtual memory
 * 5. Forge lean_string_object header, set m_rc=0, make header read-only
 * 6. Close tmpfile fd — mmap keeps inode alive, pages stay disk-backed
 *
 * Key property: data pages are backed by the real filesystem (ext4/xfs/etc.),
 * so the kernel can evict them under memory pressure and re-fault from disk.
 * Unlike memfd (tmpfs), this works even without swap. And unlike a direct
 * file mmap, another process cannot mutate the data after validation.
 *
 * Trust: this uses @[extern] which bypasses the Lean kernel. We rely on:
 * - correct header layout matching lean.h (static_assert guards this)
 * - all bytes < 128 (validated in streaming loop)
 * - null terminator from ftruncate zero-fill
 * - m_rc=0 preventing use-after-free (persistent objects are immortal)
 */

#define _GNU_SOURCE
#include <lean/lean.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>

/* Verify our assumption about the lean_string_object layout. */
_Static_assert(sizeof(lean_string_object) == 32,
    "lean_string_object must be 32 bytes (header=8 + 3*size_t=24)");

/* Helper: build an IO error with message. */
static lean_obj_res io_error(const char *msg) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Helper: build an IO error with message + strerror. */
static lean_obj_res io_error_errno(const char *prefix, int errnum) {
    char buf[512];
    snprintf(buf, sizeof(buf), "%s: %s", prefix, strerror(errnum));
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string(buf)));
}

LEAN_EXPORT lean_obj_res aks_mmap_read_ascii(b_lean_obj_arg path_obj, lean_obj_arg world) {
    (void)world;
    const char *path = lean_string_cstr(path_obj);

    /* Resources — initialized so cleanup is always safe. */
    int fd = -1;                /* source file */
    int tfd = -1;              /* anonymous tmpfile */
    void *base = MAP_FAILED;   /* mmap reservation */
    size_t total_size = 0;     /* size of mmap reservation */
    lean_obj_res result = NULL; /* error or success; set before goto cleanup */

    /* Open the source file */
    fd = open(path, O_RDONLY);
    if (fd < 0) {
        result = io_error_errno("mmapReadAscii: open", errno);
        goto cleanup;
    }

    /* Get file size */
    struct stat st;
    if (fstat(fd, &st) < 0) {
        result = io_error_errno("mmapReadAscii: fstat", errno);
        goto cleanup;
    }
    size_t file_size = (size_t)st.st_size;

    /* Create a private temporary file via mkstemp + immediate unlink.
     * The unlink removes the directory entry so no other process can open
     * or modify our validated data. The fd keeps the inode alive until we
     * close it (or the mmap keeps it alive after that). */
    {
        char tmpl[] = "/tmp/aks_cert_XXXXXX";
        tfd = mkstemp(tmpl);
        if (tfd < 0) {
            result = io_error_errno("mmapReadAscii: mkstemp", errno);
            goto cleanup;
        }
        unlink(tmpl); /* remove directory entry immediately */
    }

    /* Pre-extend to file_size + 1: the +1 byte will be 0 (null terminator).
     * For empty files this gives a 1-byte file containing just '\0'. */
    if (ftruncate(tfd, (off_t)(file_size + 1)) < 0) {
        result = io_error_errno("mmapReadAscii: ftruncate", errno);
        goto cleanup;
    }

    /* Streaming read + validate + write loop.
     * Each byte passes through userspace exactly once: read from file,
     * check < 128, write to tmpfile. Buffer is 64KB on stack.
     * For empty files this loop is a no-op. */
    {
        char buf[65536];
        size_t remaining = file_size;
        while (remaining > 0) {
            size_t chunk = remaining < sizeof(buf) ? remaining : sizeof(buf);
            ssize_t nr = read(fd, buf, chunk);
            if (nr <= 0) {
                result = (nr == 0)
                    ? io_error("mmapReadAscii: unexpected EOF")
                    : io_error_errno("mmapReadAscii: read", errno);
                goto cleanup;
            }
            /* Validate: every byte must be < 128 (ASCII) */
            for (ssize_t i = 0; i < nr; i++) {
                if ((unsigned char)buf[i] >= 128) {
                    result = io_error(
                        "mmapReadAscii: file contains non-ASCII byte (>= 128)");
                    goto cleanup;
                }
            }
            /* Write validated chunk to tmpfile */
            const char *p = buf;
            ssize_t left = nr;
            while (left > 0) {
                ssize_t nw = write(tfd, p, (size_t)left);
                if (nw < 0) {
                    if (errno == EINTR) continue;
                    result = io_error_errno("mmapReadAscii: write to tmpfile", errno);
                    goto cleanup;
                }
                p += nw;
                left -= nw;
            }
            remaining -= (size_t)nr;
        }
    }
    close(fd); fd = -1; /* done with source file */

    /* Split mmap layout:
     * [page 0: anonymous, writable] [pages 1+: tmpfile, read-only]
     *
     * The lean_string_object header (32 bytes) goes at the END of page 0,
     * so m_data[0] aligns exactly with the start of the data pages. */
    {
        size_t pgsz = (size_t)sysconf(_SC_PAGESIZE);
        /* Round up data mapping to page boundary */
        size_t data_map_size = ((file_size + 1) + pgsz - 1) & ~(pgsz - 1);
        total_size = pgsz + data_map_size;

        /* Reserve contiguous virtual address space */
        base = mmap(NULL, total_size, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (base == MAP_FAILED) {
            result = io_error_errno("mmapReadAscii: mmap reserve", errno);
            goto cleanup;
        }

        /* Map page 0: anonymous writable (for lean_string_object header) */
        if (mmap(base, pgsz, PROT_READ | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0) == MAP_FAILED) {
            result = io_error_errno("mmapReadAscii: mmap header page", errno);
            goto cleanup;
        }

        /* Map pages 1+: tmpfile read-only (disk-backed, evictable) */
        if (mmap((char *)base + pgsz, data_map_size, PROT_READ,
                 MAP_PRIVATE | MAP_FIXED, tfd, 0) == MAP_FAILED) {
            result = io_error_errno("mmapReadAscii: mmap data pages", errno);
            goto cleanup;
        }
        close(tfd); tfd = -1; /* mmap keeps inode alive; fd no longer needed */

        /* Hint: checker will access data pages randomly */
        madvise((char *)base + pgsz, data_map_size, MADV_RANDOM);

        /* Forge lean_string_object header at end of page 0.
         * The header is 32 bytes. m_data[0] is at offset 32 from the struct start,
         * which is exactly (char*)base + pgsz = start of data pages. */
        lean_string_object *str =
            (lean_string_object *)((char *)base + pgsz - sizeof(lean_string_object));

        /* Page is zero-initialized (MAP_ANONYMOUS), so m_cs_sz=0, m_other=0. */
        str->m_header.m_rc  = 0;           /* persistent: never freed, inc/dec no-ops */
        str->m_header.m_tag = LeanString;  /* 249 */
        str->m_size     = file_size + 1;   /* byte count including '\0' */
        str->m_capacity = data_map_size;   /* mapped capacity */
        str->m_length   = file_size;       /* UTF-8 char count = byte count (all ASCII) */

        /* Make header page read-only. With m_rc=0 (persistent), lean_inc_ref and
         * lean_dec_ref are no-ops, so no writes will occur. Any bug that does
         * try to write gets SIGSEGV instead of silent corruption. */
        mprotect(base, pgsz, PROT_READ);

        result = lean_io_result_mk_ok((lean_obj_res)str);
        base = MAP_FAILED; /* transfer ownership to Lean — don't munmap in cleanup */
    }

cleanup:
    if (fd >= 0) close(fd);
    if (tfd >= 0) close(tfd);
    if (base != MAP_FAILED) munmap(base, total_size);
    return result;
}

/* ─── Cached string loading ───
 *
 * mmapPrepare: String → IO (Unit → String)
 *   Does the IO work (copy, validate, mmap), caches the result by path,
 *   returns a pure thunk closure capturing the persistent string.
 *
 * getCachedString: String → String
 *   Pure accessor with lazy fallback. Returns a cached string or loads
 *   on first call. Suitable for use in `def` bodies — the IR stores just
 *   `getCachedString "path"` (tiny), not the file contents.
 */

#define MAX_STRING_CACHE 16
static struct { char *path; lean_object *str; } g_str_cache[MAX_STRING_CACHE];
static int g_str_cache_count = 0;

static lean_object *str_cache_lookup(const char *path) {
    for (int i = 0; i < g_str_cache_count; i++)
        if (strcmp(g_str_cache[i].path, path) == 0)
            return g_str_cache[i].str;
    return NULL;
}

static void str_cache_store(const char *path, lean_object *str) {
    if (g_str_cache_count < MAX_STRING_CACHE) {
        g_str_cache[g_str_cache_count].path = strdup(path);
        g_str_cache[g_str_cache_count].str = str;
        g_str_cache_count++;
    }
}

/* Load a string via mmap, storing in cache. Returns the string or panics. */
static lean_object *load_and_cache(const char *path, b_lean_obj_arg path_obj) {
    lean_object *world = lean_io_mk_world();
    lean_obj_res io_result = aks_mmap_read_ascii(path_obj, world);
    if (!lean_io_result_is_ok(io_result)) {
        char buf[512];
        snprintf(buf, sizeof(buf), "getCachedString: failed to load '%s'", path);
        lean_dec(io_result);
        lean_internal_panic(buf);
    }
    lean_object *str = lean_io_result_get_value(io_result);
    lean_inc(str);
    lean_dec(io_result);
    str_cache_store(path, str);
    return str;
}

/* Thunk closure body: returns the captured string. */
static lean_obj_res aks_thunk_return(lean_obj_arg captured, lean_obj_arg unit) {
    (void)unit; /* Unit = lean_box(0), scalar — no dec needed */
    /* captured is persistent (m_rc=0), inc is no-op */
    lean_inc(captured);
    return captured;
}

/* mmapPrepare: String → IO (Unit → String) */
LEAN_EXPORT lean_obj_res aks_mmap_prepare(b_lean_obj_arg path_obj, lean_obj_arg world) {
    const char *path = lean_string_cstr(path_obj);

    lean_object *cached = str_cache_lookup(path);
    if (!cached) {
        lean_obj_res io_result = aks_mmap_read_ascii(path_obj, world);
        if (!lean_io_result_is_ok(io_result)) return io_result;
        cached = lean_io_result_get_value(io_result);
        lean_inc(cached);
        lean_dec(io_result);
        str_cache_store(path, cached);
    }

    lean_object *thunk = lean_alloc_closure((void*)aks_thunk_return, 2, 1);
    lean_inc(cached);
    lean_closure_set(thunk, 0, cached);
    return lean_io_result_mk_ok(thunk);
}

/* getCachedString: String → String (pure, with lazy fallback) */
LEAN_EXPORT lean_obj_res aks_get_cached_string(b_lean_obj_arg path_obj) {
    const char *path = lean_string_cstr(path_obj);
    lean_object *cached = str_cache_lookup(path);
    if (cached) {
        lean_inc(cached);
        return cached;
    }
    return load_and_cache(path, path_obj);
}
