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

-- Class B/C: index/position primitives whose non-scalar branch
-- returns a hard-coded out-of-bounds default without consulting the
-- object. Reachable here by feeding a non-scalar Nat whose value is
-- small (via the FFI helper `boxed`).
def testIndexPositionCluster : IO Unit := do
  let s := "L∃∀N"  -- 8 bytes: L(1) ∃(3) ∀(3) N(1)
  let ba : ByteArray  := ⟨#[10, 20, 30, 40]⟩
  let fa : FloatArray := ⟨#[1.5, 2.5, 3.5, 4.5]⟩

  section_ "String.Pos.Raw.next (lean_string_utf8_next)"
  IO.println s!"  scalar @1         = {(String.Pos.Raw.next s ⟨1⟩).byteIdx}  (expected 4)"
  IO.println s!"  boxed  @1         = {(String.Pos.Raw.next s ⟨boxed 1⟩).byteIdx}  (expected 4)"

  section_ "String.Pos.Raw.prev (lean_string_utf8_prev)"
  IO.println s!"  scalar @4         = {(String.Pos.Raw.prev s ⟨4⟩).byteIdx}  (expected 1)"
  IO.println s!"  boxed  @4         = {(String.Pos.Raw.prev s ⟨boxed 4⟩).byteIdx}  (expected 1)"

  section_ "String.Pos.Raw.get (lean_string_utf8_get)"
  IO.println s!"  scalar @1         = {String.Pos.Raw.get s ⟨1⟩}  (expected '∃')"
  IO.println s!"  boxed  @1         = {String.Pos.Raw.get s ⟨boxed 1⟩}  (expected '∃')"

  section_ "String.Pos.Raw.get? (lean_string_utf8_get_opt)"
  IO.println s!"  scalar @1         = {repr (String.Pos.Raw.get? s ⟨1⟩)}  (expected some '∃')"
  IO.println s!"  boxed  @1         = {repr (String.Pos.Raw.get? s ⟨boxed 1⟩)}  (expected some '∃')"

  section_ "String.Pos.Raw.isValid (lean_string_is_valid_pos)"
  IO.println s!"  scalar @1         = {String.Pos.Raw.isValid s ⟨1⟩}  (expected true)"
  IO.println s!"  boxed  @1         = {String.Pos.Raw.isValid s ⟨boxed 1⟩}  (expected true)"

  section_ "String.Pos.Raw.atEnd (lean_string_utf8_at_end)"
  IO.println s!"  scalar @1         = {String.Pos.Raw.atEnd s ⟨1⟩}  (expected false)"
  IO.println s!"  boxed  @1         = {String.Pos.Raw.atEnd s ⟨boxed 1⟩}  (expected false)"

  section_ "String.Pos.Raw.set (lean_string_utf8_set)"
  let t := "abcd"
  IO.println s!"  scalar @1 := 'Z'  = {repr (String.Pos.Raw.set t ⟨1⟩ 'Z')}  (expected \"aZcd\")"
  IO.println s!"  boxed  @1 := 'Z'  = {repr (String.Pos.Raw.set t ⟨boxed 1⟩ 'Z')}  (expected \"aZcd\")"

  section_ "ByteArray.get! (lean_byte_array_get)"
  IO.println s!"  scalar @2         = {ba.get! 2}  (expected 30)"
  IO.println s!"  boxed  @2         = {ba.get! (boxed 2)}  (expected 30)"

  section_ "ByteArray.set! (lean_byte_array_set)"
  IO.println s!"  scalar @2 := 99   = {(ba.set! 2 99).toList}  (expected [10,20,99,40])"
  IO.println s!"  boxed  @2 := 99   = {(ba.set! (boxed 2) 99).toList}  (expected [10,20,99,40])"

  section_ "FloatArray.get! (lean_float_array_get)"
  IO.println s!"  scalar @2         = {fa.get! 2}  (expected 3.5)"
  IO.println s!"  boxed  @2         = {fa.get! (boxed 2)}  (expected 3.5)"

  section_ "FloatArray.set! (lean_float_array_set)"
  IO.println s!"  scalar @2 := 9.5  = {(fa.set! 2 9.5).data.toList}  (expected [1.5,2.5,9.5,4.5])"
  IO.println s!"  boxed  @2 := 9.5  = {(fa.set! (boxed 2) 9.5).data.toList}  (expected [1.5,2.5,9.5,4.5])"

  section_ "Array.swapIfInBounds (lean_array_swap)"
  let arr : Array Nat := #[10, 20, 30, 40]
  IO.println s!"  scalar swap(0,2)  = {(arr.swapIfInBounds 0 2).toList}  (expected [30,20,10,40])"
  IO.println s!"  boxed  swap(b0,b2)= {(arr.swapIfInBounds (boxed 0) (boxed 2)).toList}  (expected [30,20,10,40])"

-- Class C/D/E: Nat arithmetic primitives whose mixed scalar/non-scalar
-- branches short-circuit based on the scalar/non-scalar classification
-- alone, and assume small-⇒-scalar. Under invariant violation these
-- either return wrong answers (sub/div/div_exact/mod/eq/le/lt/shiftr)
-- or produce non-canonical results (add/succ) that break downstream
-- comparisons.
def testNatArithCluster : IO Unit := do
  let a : Nat := 5
  let b : Nat := boxed 3

  section_ "lean_nat_big_add (propagates non-canonical representation)"
  let r := a + b
  IO.println s!"  value of 5 + boxed(3)  = {r}  (expected 8)"
  IO.println s!"  decide (r = 8)         = {decide (r = 8)}  (expected true; wrong because r is mpz-boxed of value 8)"

  section_ "lean_nat_big_sub (scalar - non-scalar short-circuits to 0)"
  IO.println s!"  5 - boxed(3)           = {a - b}  (expected 2)"

  section_ "lean_nat_big_div (scalar / non-scalar short-circuits to 0)"
  IO.println s!"  5 / boxed(3)           = {a / b}  (expected 1)"

  section_ "lean_nat_big_mod (scalar % non-scalar short-circuits to a1)"
  IO.println s!"  5 %%% boxed(3)         = {a % b}  (expected 2)"

  section_ "lean_nat_big_eq (mixed scalar/non-scalar short-circuits to false)"
  IO.println s!"  5 = boxed(5)           = {decide ((5 : Nat) = boxed 5)}  (expected true)"

  section_ "lean_nat_big_lt (mixed scalar/non-scalar short-circuits by classification)"
  IO.println s!"  5 < boxed(5)           = {decide ((5 : Nat) < boxed 5)}  (expected false)"

  section_ "lean_nat_big_le (mixed scalar/non-scalar short-circuits by classification)"
  IO.println s!"  5 <= boxed(4)          = {decide ((5 : Nat) <= boxed 4)}  (expected false)"

  section_ "lean_nat_big_shiftr (non-scalar shift amount short-circuits to 0)"
  let big : Nat := 2^40
  let sm  : Nat := boxed 5
  IO.println s!"  (2^40) >>> boxed(5)    = {big >>> sm}  (expected 2^35 = 34359738368)"

def main : IO Unit := do
  testExtract
  testIndexPositionCluster
  testNatArithCluster
