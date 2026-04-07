/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Internal.Order.Basic
public import Init.Internal.Order.MonadTail
import Init.Classical

set_option linter.missingDocs true

public section

namespace Lean.Order

/-- Every CCPO has at least one element (the bottom element). -/
noncomputable scoped instance CCPO.instNonempty [CCPO α] : Nonempty α := ⟨bot⟩

/--
A fixpoint combinator for functions `f : α → α` that is opaque (i.e., `partial`).
This is the runtime implementation of `extrinsicFix`.
-/
@[specialize]
partial def opaqueFix {α : Sort u} [Nonempty α] (f : α → α) : α :=
  f (opaqueFix f)

open _root_.Classical in
/--
An extrinsic fixpoint combinator for CCPO-valued functions.

`extrinsicFix f` computes the fixpoint of `f : α → α`. At runtime, it simply iterates `f`.
Logically, if there exists a CCPO on `α` making `f` monotone, `extrinsicFix f` equals the
CCPO least fixpoint, enabling verification.

If no such CCPO exists, `extrinsicFix f` is opaque and cannot be reasoned about.
-/
@[cbv_opaque, implemented_by opaqueFix]
def extrinsicFix {α : Sort u} [Nonempty α] (f : α → α) : α :=
  if h : ∃ (inst : CCPO α), (letI := inst; monotone f) then
    @fix α h.choose f h.choose_spec
  else
    opaqueFix f

section theorems

attribute [local instance] CCPO.instNonempty

/--
The fixpoint equation for `extrinsicFix`: given a CCPO instance and monotonicity of `f`,
`extrinsicFix f = f (extrinsicFix f)`.
-/
theorem extrinsicFix_eq [inst : CCPO α] {f : α → α}
    (hf : monotone f) :
    extrinsicFix f = f (extrinsicFix f) := by
  have h : ∃ inst' : CCPO α, (letI := inst'; monotone f) := ⟨inst, hf⟩
  simp only [extrinsicFix, dif_pos h]
  exact @fix_eq α h.choose f h.choose_spec

/--
Fixpoint induction for `extrinsicFix`: an admissible predicate holds for `extrinsicFix f`
if it is preserved by `f`.

The admissibility hypothesis is universally quantified over all CCPO instances because
`extrinsicFix` uses classical choice to select a CCPO, which may differ from the caller's
instance.
-/
theorem extrinsicFix_induct [inst : CCPO α] {f : α → α}
    (hf : monotone f)
    (motive : α → Prop) (hadm : ∀ (inst' : CCPO α), @admissible α inst' motive)
    (h : ∀ x, motive x → motive (f x)) : motive (extrinsicFix f) := by
  have hex : ∃ inst' : CCPO α, (letI := inst'; monotone f) := ⟨inst, hf⟩
  simp only [extrinsicFix, dif_pos hex]
  exact @fix_induct α hex.choose f hex.choose_spec motive (hadm hex.choose) h

end theorems

end Lean.Order
