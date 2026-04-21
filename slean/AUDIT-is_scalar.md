# Audit: `lean_is_scalar` branches in the runtime

This document defines a shared taxonomy for classifying branches on
`lean_is_scalar` found in `src/runtime/` and `src/include/lean/`, and
lists known findings. In-source `SLEAN-AUDIT:` comments refer to
this taxonomy by letter without restating it.

## Background

In the Lean 4 runtime, a `Nat`-valued `lean_object *` is represented
in one of two ways:

- **scalar**: a tagged pointer `(v << 1) | 1` directly encoding `v`,
  valid only for `v <= LEAN_MAX_SMALL_NAT` (defined as `SIZE_MAX >> 1`,
  so `2^63 - 1` on 64-bit targets, `2^31 - 1` on 32-bit / wasm32).
- **non-scalar**: a pointer to a heap-allocated mpz object holding a
  bignum value.

The runtime assumes the invariant **"non-scalar representation
implies value `> LEAN_MAX_SMALL_NAT`"**, which is maintained by
convention across every `Nat`-producing primitive (they call
`mpz_to_nat` to canonicalize small mpz values to scalars). The
invariant is checked only by `lean_assert`, compiled out in release
builds.

Many runtime primitives branch on `lean_is_scalar` to choose an
implementation. Most such branches are fine. Some rely on the
invariant for correctness; if the invariant is broken (e.g. by a
C plugin allocating an mpz of value 5 via `lean_alloc_mpz`), those
primitives can return wrong answers.

## Taxonomy

Classifications are applied **first-match, more severe first**:
assign a site to the first bucket whose description fits.

- **A**: wrong answers on easily achievable Lean inputs. Not related
  to the small-⇒-scalar invariant; reachable from pure Lean without
  any FFI.
- **B**: wrong answers reachable in principle, but the small-⇒-scalar
  invariant makes violations difficult from Lean. Still not impossible
  (e.g. if artificial limitations on wasm32 are removed, or on
  hypothetical 16-bit ports).
- **C**: wrong answers reachable from C code that disrespects
  small-⇒-scalar or other assumed invariants, and does not assert the
  invariant. Can happen with a wrong plugin, silent even in debug
  builds.
- **D**: like C, but asserts the invariant, therefore fails loudly in
  debug builds.
- **E**: like C or D, but not a wrong-answer bug itself — instead,
  breaks invariant propagation (produces a non-canonical object, which
  can then feed Class B/C/D downstream).
- **Y**: no known silent wrong-answer or invariant-propagation issue,
  but the loud-failure shape imposes unnecessary proof obligations
  (e.g. "argument < 2^32") on verified calling code.
- **Z**: like Y, but with no new verification complications beyond
  what was already necessary.

Code we have not looked at in enough depth to classify remains
implicitly uncategorized (colloquially "class ?") and is not
documented here.

## Known findings

Each row lists the class, the site, and either a one-line MWE or a
pointer to a reproducer. All findings tested against Lean
4.30.0-rc2 (commit `3dc1a088b6`) on x86_64-linux unless otherwise
noted. In-source `SLEAN-AUDIT:` tags match each row.

### Class A — pure-Lean reachable wrong answers

| Site | MWE |
|---|---|
| `lean_string_utf8_extract` (`src/runtime/object.cpp`) | `String.Pos.Raw.extract "L∃∀N" ⟨2^63⟩ ⟨2^63 + 1⟩` returns `"L∃∀N"`; `String.Pos.Raw.extract "L∃∀N" ⟨100⟩ ⟨200⟩` returns `""`. Reference implementation returns `""` for both. |

### Class B — wrong answers, not reachable from 64-bit pure Lean today

These sites' non-scalar branches return a hard-coded "out-of-bounds"
default without consulting the object. Their "guessed" default happens
to match what the reference semantics would return at an OOB scalar
input, so a pure-Lean call with a scalar Lean literal ≥ 2^63 (which is
automatically mpz-boxed) cannot distinguish them — it returns the same
answer the scalar OOB branch would return. They are nonetheless
reachable as Class C (see next section) via a C plugin that violates
the small-⇒-scalar invariant, and would be directly reachable on 32-bit
platforms where `LEAN_MAX_SMALL_NAT = 2^31 - 1` is within the physical
size of a string or array.

| Site | Non-scalar branch returns |
|---|---|
| `lean_string_utf8_get` | `'A'` (default char) |
| `lean_string_utf8_get_opt` | `none` |
| `lean_string_utf8_next` | `i + 1` |
| `lean_string_is_valid_pos` | `false` |
| `lean_string_utf8_at_end` | `true` |
| `lean_string_utf8_prev` | `i - 1` |
| `lean_string_utf8_set` | `s` (no write) |
| `lean_byte_array_get` | `0` |
| `lean_byte_array_set` | `a` (no write) |
| `lean_float_array_get` | `0.0` |
| `lean_float_array_set` | `a` (no write) |
| `lean_array_swap` | `a` (no swap) |

### Class C — C-reachable wrong answers, silent even in debug

All Class B sites are also Class C: a C `@[extern]` helper that
produces a non-scalar `Nat` with small value (e.g. by calling
`lean_alloc_mpz(mpz::of_size_t(n))`) makes each of them return the
wrong answer. None have a value-assert inside the shortcut branch,
so the violation is silent even with asserts enabled. See
`slean/repros/string-utf8-nonscalar/` for a reproducer of all of them.

Additional Class C sites found in the Nat arithmetic layer:

| Site | MWE |
|---|---|
| `lean_nat_big_mod` | `5 % boxed(3)` returns `5`; correct answer is `2` |
| `lean_nat_big_shiftr` | `(2^40) >>> boxed(5)` returns `0`; correct answer is `2^35` |

### Class D — C-reachable wrong answers, loud in debug

Inside the scalar-vs-non-scalar shortcut branch, a `lean_assert` on
the actual values (not just on the classification) would fire in
debug if the invariant is violated. Silent in release.

| Site | MWE |
|---|---|
| `lean_nat_big_sub` | `5 - boxed(3)` returns `0`; correct answer is `2` |
| `lean_nat_big_div` | `5 / boxed(3)` returns `0`; correct answer is `1` |
| `lean_nat_big_div_exact` | same branch returns `0`; correct answer may differ |
| `lean_nat_big_eq` | `5 = boxed(5)` returns `false`; correct is `true` |
| `lean_nat_big_le` | `5 ≤ boxed(4)` returns `true`; correct is `false` |
| `lean_nat_big_lt` | `5 < boxed(5)` returns `true`; correct is `false` |

### Class E — invariant propagation (non-canonicalizing output)

These produce the correct local value but write it out with
`mpz_to_nat_core` (which does not canonicalize small values back to
the scalar representation), unlike sibling ops that use `mpz_to_nat`.
Under invariant violation the local answer is correct, but the
representation is non-canonical and feeds downstream Class B/C/D.

| Site | MWE |
|---|---|
| `lean_nat_big_add` | `let r := 5 + boxed 3` has value 8 but `decide (r = 8)` returns `false` via `lean_nat_big_eq`. |
| `lean_nat_big_succ` | same pattern (code inspection; not separately reproduced) |

### Class Y — loud fails imposing new proof obligations

These raise an error for any non-scalar input. Under the invariant
they only fire for values beyond addressable memory, so in practice
they never fire — but a verified caller has to discharge that
obligation ("value < 2^63 on 64-bit") in order to use them from a
total function.

| Site | Non-scalar action |
|---|---|
| `lean_mk_empty_array_with_capacity` (`lean.h`) | `lean_internal_panic_out_of_memory()` |
| `lean_mk_empty_byte_array` (`lean.h`) | same |
| `lean_mk_empty_float_array` (`lean.h`) | same |
| `lean_array_get` (`lean.h`) | falls through to `lean_array_get_panic` |
| `lean_array_get_borrowed` (`lean.h`) | same |
| `lean_array_set` (`lean.h`) | falls through to `lean_array_set_panic` |
| `lean_string_utf8_get_bang` (`object.cpp`) | `lean_panic_fn("invalid String.Pos at String.get!")` |
| `lean_nat_pow` (`object.cpp`) | `lean_internal_panic("Nat.pow exponent is too big")` |
| `lean_nat_shiftl` (`object.cpp`) | `lean_internal_panic("Nat.shiftl exponent is too big")` |

### Class Z — loud fails without new obligations

None identified so far.

## Deliberately not enumerated

Sites that are genuinely invariant-independent (they compute the
correct value from either scalar or non-scalar input, with any
reasonable value, and canonicalize their output via `mpz_to_nat`)
are not listed above. Examples: `lean_nat_big_mul`, `_land`, `_lor`,
`_xor`, `_gcd`, `_log2`, `lean_uint*_of_nat`, `lean_nat_to_size_t`,
`lean_mk_array`, `lean_inc`/`lean_dec`, List/Option iterators,
`lean_is_scalar`-as-nil-discriminator in compact/sharecommon/apply.

Non-trivial code we have not analyzed deeply remains implicitly
unclassified (class ?).
