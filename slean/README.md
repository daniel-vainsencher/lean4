# SLean audit working directory

This directory holds exploratory analyses and reproducers related to
the Lean runtime. Not intended for upstream merge in its current
form.

## Contents

- `AUDIT-is_scalar.md` — audit taxonomy and findings on all `lean_is_scalar`
  branches in `src/runtime/` and `src/include/lean/`. In-source audit tags
  (`SLEAN-AUDIT:` comments) use the letters A/B/C/D/E/Y/Z defined there.
- `repros/` — self-contained reproducers, each with its own `run.sh`.
