/* Helper for reproducers in this directory.
 *
 * Exports `mk_boxed_small_nat(size_t n) : Nat` which returns a Nat
 * whose value is `n` but whose runtime representation is always an
 * mpz-boxed heap object, regardless of how small `n` is. This
 * deliberately violates the Lean runtime invariant that non-scalar
 * Nats have value > LEAN_MAX_SMALL_NAT, to exercise the non-scalar
 * branches of `@[extern]`-bound runtime primitives at arbitrary
 * positions.
 */
#include <gmp.h>
#include <lean/lean.h>
#include <lean/lean_gmp.h>

LEAN_EXPORT lean_object * mk_boxed_small_nat(size_t n) {
    mpz_t v;
    mpz_init_set_ui(v, (unsigned long)n);
    lean_object * r = lean_alloc_mpz(v);
    mpz_clear(v);
    return r;
}
