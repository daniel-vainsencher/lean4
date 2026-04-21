# Reproducers: `lean_is_scalar` branches that rely on the small-⇒-scalar invariant

Each reproducer in this directory exercises one or more branches in the
Lean runtime that read `lean_is_scalar` to choose an implementation,
under conditions where the "non-scalar Nat ⇒ value > LEAN_MAX_SMALL_NAT"
invariant is violated by a minimal C helper.

## Shared infrastructure

- `mkboxed.c` — the helper: exports
  `mk_boxed_small_nat(size_t n) : Nat`, which uses `lean_alloc_mpz` to
  return a Nat of value `n` in the non-scalar (mpz) representation,
  regardless of how small `n` is. Intended to model a buggy plugin.
- `run.sh` — builds and runs the combined test binary using
  `leanc` from the installed toolchain.

## Organisation

- `Test.lean` is the top-level entry point. It imports / uses the
  reproducer modules listed below, prints per-finding output, and
  exits cleanly so the output can be diffed against
  `expected-output.txt`.

Per-class reproducer modules are added alongside this README as each
finding is documented. See `../../AUDIT-is_scalar.md` for the class
labels (A/B/C/D/E/Y/Z).

## Running

```
./run.sh
```

Each section of the output consists of a "scalar …" row showing the
baseline behaviour and one or more additional rows showing wrong
behaviour under invariant violation. Expected output for every
currently-documented finding is kept in `expected-output.txt`.
