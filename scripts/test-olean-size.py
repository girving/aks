#!/usr/bin/env python3
"""Test whether private defs, opaque defs, module keyword, etc. keep data out of .oleans."""

import subprocess, tempfile, os, sys

# Generate a ~1MB string literal
BIG = "A" * (1024 * 1024)

MODULE_HEADER = 'module\n'

SMALL = "A" * 100  # small string for fast native_decide

VARIANTS = {
    "baseline_empty": "def empty : Nat := 0",
    # expose public section: everything visible + unfoldable
    "mod_expose_pub": MODULE_HEADER + f"""
@[expose] public section
def bigString : String := "{BIG}"
end
""",
    # public section only (no expose): visible but not unfoldable
    "mod_pub_only": MODULE_HEADER + f"""
public section
def bigString : String := "{BIG}"
end
""",
    # default (private): not visible or unfoldable
    "mod_default": MODULE_HEADER + f"""
def bigString : String := "{BIG}"
""",
    # mixed: public (no expose) for data, expose pub for rest
    "mod_mixed": MODULE_HEADER + f"""
public section
def bigString : String := "{BIG}"
end
@[expose] public section
def smallThing : Nat := bigString.length
theorem smallCheck : smallThing = 1048576 := by native_decide
end
""",
}

def compile_and_measure(name, code):
    """Compile a .lean file and return the .olean size."""
    with tempfile.TemporaryDirectory(dir="/home/ubuntu/aks") as tmpdir:
        lean_file = os.path.join(tmpdir, "Test.lean")
        olean_file = os.path.join(tmpdir, "Test.olean")
        ilean_file = os.path.join(tmpdir, "Test.ilean")

        with open(lean_file, "w") as f:
            f.write(code + "\n")

        result = subprocess.run(
            ["lake", "env", "lean", lean_file,
             "-o", olean_file,
             "-i", ilean_file],
            capture_output=True, text=True,
            cwd="/home/ubuntu/aks",
            timeout=120
        )

        if result.returncode != 0:
            err = (result.stderr + result.stdout).strip()
            # Truncate but show useful info
            lines = err.split('\n')
            msg = '; '.join(l.strip() for l in lines if l.strip())[:300]
            return name, -1, msg

        if os.path.exists(olean_file):
            size = os.path.getsize(olean_file)
            return name, size, "ok"
        else:
            return name, -1, "no .olean produced"

print(f"String literal size: {len(BIG)} bytes (~1 MB)")
print(f"{'Variant':<25} {'olean size':>12}  Status")
print("-" * 60)

for name, code in sorted(VARIANTS.items()):
    name_result, size, status = compile_and_measure(name, code)
    if size >= 0:
        print(f"{name:<25} {size:>12,}  {status}")
    else:
        print(f"{name:<25} {'ERROR':>12}  {status}")
