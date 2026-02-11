# Slow Commands Log

Track commands that exceeded expected time. Each entry should include:
- Date, command, expected time, actual time
- Root cause (if identified)
- Fix applied (if any)

## Baselines

| Operation | Expected | Notes |
|---|---|---|
| `rg` through Mathlib | ~0.2s | 86MB, 7516 .lean files |
| `lean-check` warm edit near end | 0.2-2s | Persistent language server |
| `lean-check` cold first open | 20-30s | Imports + full elaboration |
| `lake build` (cached) | ~1.6s | No changes |
| `lake build` (one file changed) | ~20s | Re-elaborates from scratch |

## Log

(No entries yet)
