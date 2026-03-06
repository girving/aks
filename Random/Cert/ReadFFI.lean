module
/-
  # mmap-based ASCII File Reader (FFI)

  `mmapReadAscii` reads a file via `memfd` + split mmap, validating all bytes
  are ASCII (< 128). The returned `String` is backed by read-only mmap'd pages
  with `m_rc = 0` (persistent), so it is never heap-allocated and never freed.

  **Trust:** uses `@[extern]` (C FFI), bypassing the Lean kernel. See
  `c/mmap_string.c` for the full trust story.
-/

@[expose] public section

@[extern "aks_mmap_read_ascii"]
opaque mmapReadAscii (path : @& String) : IO String

/-- Read a certificate data file at runtime via mmap. Zero-copy. -/
def loadAsciiFile (path : System.FilePath) : IO String :=
  mmapReadAscii path.toString

/-- Prepare a file for pure access: does the IO work (copy, validate, mmap),
    caches the result, returns a pure thunk `Unit → String` capturing the
    persistent mmap'd string. -/
@[extern "aks_mmap_prepare"]
opaque mmapPrepare (path : @& String) : IO (Unit → String)

/-- Pure accessor for cached mmap'd strings. Returns a cached string or lazily
    loads via mmap on first call. Use in `def` bodies — the IR stores just
    `cachedString "path"` (tiny), not the file contents. -/
@[extern "aks_get_cached_string"]
opaque cachedString (path : @& String) : String

end
