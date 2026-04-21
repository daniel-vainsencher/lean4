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

-- Class A: lean_string_utf8_extract non-scalar branch returns `s`
-- while the scalar OOB branch returns "". Reference semantics: OOB
-- extract returns "". `2^63` is automatically mpz-boxed (no FFI
-- needed) because it exceeds `LEAN_MAX_SMALL_NAT` on 64-bit.
def testExtract : IO Unit := do
  section_ "String.Pos.Raw.extract (lean_string_utf8_extract)"
  let s := "L∃∀N"
  IO.println s!"  extract s ⟨100⟩  ⟨200⟩        = {repr (String.Pos.Raw.extract s ⟨100⟩ ⟨200⟩)}  (scalar OOB; reference: \"\")"
  IO.println s!"  extract s ⟨2^63⟩ ⟨2^63 + 1⟩   = {repr (String.Pos.Raw.extract s ⟨2^63⟩ ⟨2^63 + 1⟩)}  (non-scalar OOB; reference: \"\")"

def main : IO Unit := do
  testExtract
