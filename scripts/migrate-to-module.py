#!/usr/bin/env python3
"""Migrate .lean files to use the `module` keyword.

For standard files: adds `module` as first line, converts imports to
`public import`, adds `@[expose] public section` after imports, `end` at end.

Special files (data files, non-module files, lakefile) are skipped.
"""

import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Files to skip entirely (handled manually or stay non-module)
SKIP_FILES = {
    'lakefile.lean',
    # Non-module files (host #guard_msgs or are root imports)
    'AKS.lean',
    'AKS/Seiferas.lean',
    'Random/Axioms.lean',
    # Data files (already migrated with per-def annotations)
    'Random/Random65536.lean',
    'Random/Random16.lean',
    'Random/Random1728.lean',
    'Random/Random20736.lean',
    'Random/Test65536.lean',
    'Random/TestOpaqueData.lean',
}


def find_lean_files(root):
    """Find all .lean files, excluding .lake directory."""
    result = []
    for dirpath, dirnames, filenames in os.walk(root):
        if '.lake' in dirnames:
            dirnames.remove('.lake')
        for f in sorted(filenames):
            if f.endswith('.lean'):
                result.append(os.path.join(dirpath, f))
    return sorted(result)


def migrate_standard(filepath):
    """Add module + public import + @[expose] public section ... end."""
    with open(filepath) as f:
        lines = f.readlines()

    # Find last import line index, convert imports to public import
    last_import = -1
    for i, line in enumerate(lines):
        stripped = line.lstrip()
        if stripped.startswith('import '):
            lines[i] = line.replace('import ', 'public import ', 1)
            last_import = i

    # Build new content
    result = ['module\n']

    if last_import >= 0:
        result.extend(lines[:last_import + 1])
        result.append('\n@[expose] public section\n')
        result.extend(lines[last_import + 1:])
    else:
        result.append('\n@[expose] public section\n')
        result.extend(lines)

    # Ensure trailing newline
    if result and not result[-1].endswith('\n'):
        result[-1] += '\n'

    # Add end
    result.append('\nend\n')

    with open(filepath, 'w') as f:
        f.writelines(result)


def main():
    lean_files = find_lean_files(ROOT)

    migrated = []
    skipped = []

    for filepath in lean_files:
        relpath = os.path.relpath(filepath, ROOT)
        if relpath in SKIP_FILES:
            skipped.append(relpath)
            continue
        # Skip files that already start with 'module'
        with open(filepath) as f:
            first_line = f.readline()
        if first_line.strip() == 'module':
            skipped.append(f'{relpath} (already module)')
            continue
        migrated.append(relpath)
        migrate_standard(filepath)

    print(f"Migrated {len(migrated)} files:")
    for f in migrated:
        print(f"  {f}")
    print(f"\nSkipped {len(skipped)} files:")
    for f in skipped:
        print(f"  {f}")


if __name__ == '__main__':
    main()
