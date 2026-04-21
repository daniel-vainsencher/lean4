-- Top-level test harness for runtime-primitive reproductions where the
-- small-⇒-scalar Nat invariant is violated from C. See README.md for
-- the directory overview and ../../AUDIT-is_scalar.md for the taxonomy.
--
-- Additional findings are wired in as they are added. This file is
-- kept light: one `section` per finding, containing a header line and
-- a comparison of correct-branch vs buggy-branch behaviour.

/-- FFI-built Nat with small value in non-scalar (mpz) representation. -/
@[extern "mk_boxed_small_nat"]
opaque mkBoxedSmallNat (n : @& USize) : Nat

/-- Produces a Nat of the given value, always mpz-boxed. -/
def boxed (n : Nat) : Nat := mkBoxedSmallNat n.toUSize

def section_ (name : String) : IO Unit := do
  IO.println ""
  IO.println s!"=== {name} ==="

def main : IO Unit := do
  -- Per-finding sections are added in their own commits.
  return ()
