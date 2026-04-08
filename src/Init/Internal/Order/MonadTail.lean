/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Internal.Order.Basic
import all Init.System.ST  -- for EST.bind in MonadTail instance

set_option linter.missingDocs true

public section

namespace Lean.Order

class LiftRel (f : Type u → Type v) where
  /-- Lift a relation on values to a relation on transformed values. -/
  liftRel {α : Type u} : (α → α → Prop) → f α → f α → Prop
  /-- `liftRel` preserves reflexivity: if `R` is reflexive, then `liftRel R` is reflexive. -/
  liftRel_refl {α : Type u} {R : α → α → Prop} : (∀ x, R x x) → ∀ (fx : f α), liftRel R fx fx

/--
`MonadTail m` provides a way to lift relations on values to relations on monadic computations,
together with proofs that the lifting preserves reflexivity and that `>>=` preserves lifted relations
in the continuation argument.
-/
class MonadTail (m : Type u → Type v) [Bind m] [LiftRel m] where
  /-- `>>=` preserves `liftRel` in the continuation argument. -/
  bind_preserves_liftRel {α β : Type u} {R : β → β → Prop} (hR : ∀ x, R x x)
    {a : m α} {f₁ f₂ : α → m β} :
    (∀ x, LiftRel.liftRel R (f₁ x) (f₂ x)) → LiftRel.liftRel R (a >>= f₁) (a >>= f₂)

class LiftCCPO (m : Type u → Type v) extends LiftRel m where
  instCCPO α [CCPO α] : CCPO (m α)
  rel_eq_liftRel_rel α [inst : CCPO α] : (instCCPO α).rel = LiftRel.liftRel inst.rel

attribute [implicit_reducible] LiftCCPO.instCCPO
attribute [instance] LiftCCPO.instCCPO

theorem MonadTail.bind_mono_right
    (m : Type u → Type v) [Bind m] [LiftCCPO m] [MonadTail m]
    {α β : Type u} [CCPO β] {a : m α} {f₁ f₂ : α → m β}
    (h : ∀ x, f₁ x ⊑ f₂ x) : a >>= f₁ ⊑ a >>= f₂ := by
  change (LiftCCPO.instCCPO (m := m) β).rel _ _
  rw [LiftCCPO.rel_eq_liftRel_rel]
  apply MonadTail.bind_preserves_liftRel (fun _ => PartialOrder.rel_refl)
  intro x
  have hx := h x
  change (LiftCCPO.instCCPO (m := m) β).rel _ _ at hx
  rw [LiftCCPO.rel_eq_liftRel_rel] at hx
  exact hx

@[scoped partial_fixpoint_monotone]
theorem MonadTail.monotone_bind_right
    (m : Type u → Type v) [Bind m] [LiftCCPO m] [MonadTail m]
    {α β : Type u} [CCPO β]
    {γ : Sort w} [PartialOrder γ]
    (f : m α) (g : γ → α → m β)
    (hmono : monotone g) :
    monotone (fun (x : γ) => f >>= g x) :=
  fun _ _ h => MonadTail.bind_mono_right m (hmono _ _ h)

/-! ## `LiftRel` instances -/

instance : LiftRel Id where
  liftRel := id
  liftRel_refl := id

instance [LiftRel m] : LiftRel (StateT σ m) where
  liftRel R mx my := ∀ s, LiftRel.liftRel (fun p q => R p.1 q.1 ∧ p.2 = q.2) (mx s) (my s)
  liftRel_refl hR mx s := LiftRel.liftRel_refl (fun ⟨a, _⟩ => ⟨hR a, rfl⟩) (mx s)

instance [LiftRel m] : LiftRel (ExceptT ε m) where
  liftRel R :=
    LiftRel.liftRel (f := m) (fun x y => match x, y with
      | .ok a, .ok b => R a b
      | .error e₁, .error e₂ => e₁ = e₂
      | _, _ => False)
  liftRel_refl hR mx := by
    apply LiftRel.liftRel_refl (f := m)
    intro x; cases x with
    | ok a => exact hR a
    | error => exact rfl

instance : LiftRel (Except ε) where
  liftRel := fun R x y => match x, y with
    | .ok a, .ok b => R a b
    | .error e₁, .error e₂ => e₁ = e₂
    | _, _ => False
  liftRel_refl := fun hR x => by cases x with
    | ok a => exact hR a
    | error => exact rfl

instance [LiftRel m] : LiftRel (OptionT m) where
  liftRel R mx my :=
    LiftRel.liftRel (f := m) (fun x y => match x, y with
      | some a, some b => R a b
      | none, none => True
      | _, _ => False) mx my
  liftRel_refl hR mx := by
    apply LiftRel.liftRel_refl (f := m)
    intro x; cases x with
    | some a => exact hR a
    | none => trivial

instance : LiftRel Option where
  liftRel := fun R x y => match x, y with
    | some a, some b => R a b
    | none, none => True
    | _, _ => False
  liftRel_refl := fun hR x => by cases x with
    | some a => exact hR a
    | none => trivial

instance : LiftRel (ST σ) where
  liftRel R mx my := ∀ s, (R (mx s).val (my s).val ∧ (mx s).state = (my s).state)
  liftRel_refl hR _ _ := ⟨hR _, rfl⟩

instance : LiftRel (EST ε σ) where
  liftRel R mx my := ∀ s, match mx s, my s with
    | .ok a s₁, .ok b s₂ => R a b ∧ s₁ = s₂
    | .error e₁ s₁, .error e₂ s₂ => e₁ = e₂ ∧ s₁ = s₂
    | _, _ => False
  liftRel_refl := by
    sorry

/-! ## `LiftCCPO` instances -/

instance : LiftCCPO Id where
  instCCPO α := inferInstanceAs (CCPO α)
  rel_eq_liftRel_rel α inst := by rfl

instance [LiftCCPO m] [CCPO σ] : LiftCCPO (StateT σ m) where
  instCCPO α := inferInstanceAs (CCPO (σ → m (α × σ)))
  rel_eq_liftRel_rel α inst := by sorry

instance [LiftCCPO m] [CCPO]: LiftCCPO (ExceptT ε m) where
  liftRel R :=
    LiftCCPO.liftRel (f := m) (fun x y => match x, y with
      | .ok a, .ok b => R a b
      | .error e₁, .error e₂ => e₁ = e₂
      | _, _ => False)
  liftRel_refl hR mx := by
    apply LiftCCPO.liftRel_refl (f := m)
    intro x; cases x with
    | ok a => exact hR a
    | error => exact rfl

instance : LiftCCPO (Except ε) where
  liftRel := fun R x y => match x, y with
    | .ok a, .ok b => R a b
    | .error e₁, .error e₂ => e₁ = e₂
    | _, _ => False
  liftRel_refl := fun hR x => by cases x with
    | ok a => exact hR a
    | error => exact rfl

instance [LiftCCPO m] : LiftCCPO (OptionT m) where
  liftRel R mx my :=
    LiftCCPO.liftRel (f := m) (fun x y => match x, y with
      | some a, some b => R a b
      | none, none => True
      | _, _ => False) mx my
  liftRel_refl hR mx := by
    apply LiftCCPO.liftRel_refl (f := m)
    intro x; cases x with
    | some a => exact hR a
    | none => trivial

instance : LiftCCPO Option where
  liftRel := fun R x y => match x, y with
    | some a, some b => R a b
    | none, none => True
    | _, _ => False
  liftRel_refl := fun hR x => by cases x with
    | some a => exact hR a
    | none => trivial

instance : LiftCCPO (ST σ) where
  liftRel R mx my := ∀ s, (R (mx s).val (my s).val ∧ (mx s).state = (my s).state)
  liftRel_refl hR _ _ := ⟨hR _, rfl⟩

instance : LiftCCPO (EST ε σ) where
  liftRel R mx my := ∀ s, match mx s, my s with
    | .ok a s₁, .ok b s₂ => R a b ∧ s₁ = s₂
    | .error e₁ s₁, .error e₂ s₂ => e₁ = e₂ ∧ s₁ = s₂
    | _, _ => False
  liftRel_refl := by
    sorry

/-! ## `MonadTail` instances -/

instance : MonadTail Id where
  bind_preserves_liftRel := by intro _ _ _ _ _ _ _ h; exact h _

instance {σ : Type u} {m : Type u → Type v} [Monad m] [LiftRel m] [MonadTail m] [Nonempty σ] :
    MonadTail (StateT σ m) where
  bind_preserves_liftRel := by
    intro _ _ _ hR _ _ _ h s
    show LiftRel.liftRel _ (StateT.bind _ _ s) (StateT.bind _ _ s)
    simp only [StateT.bind]
    apply MonadTail.bind_preserves_liftRel (m := m) (fun ⟨a, s⟩ => ⟨hR a, rfl⟩)
    intro ⟨x, s'⟩
    exact h x s'

instance {ε : Type u} {m : Type u → Type v} [Monad m] [LiftRel m] [MonadTail m] :
    MonadTail (ExceptT ε m) where
  bind_preserves_liftRel := by
    intro _ _ _ hR _ _ _ h
    apply MonadTail.bind_preserves_liftRel (m := m) (fun x => by cases x with | ok a => exact hR a | error => exact rfl)
    intro x; cases x with
    | error => apply LiftRel.liftRel_refl (f := m); intro x; cases x with | ok a => exact hR a | error => exact rfl
    | ok a => exact h a

instance : MonadTail (Except ε) where
  liftRel {α} R x y :=
    (∃ _ : Nonempty (Except ε α), x = Classical.ofNonempty) ∨
    match x, y with
    | .ok a, .ok b => R a b
    | .error e₁, .error e₂ => e₁ = e₂
    | _, _ => False
  liftRel_refl hR x := by
    exact Or.inr (by cases x with | ok a => exact hR a | error => exact rfl)
  bind_preserves_liftRel := by
    intro _ _ _ _ a _ _ h
    cases a with
    | error e => exact Or.inr rfl
    | ok x => exact h x

instance {m : Type u → Type v} [Monad m] [MonadTail m] :
    MonadTail (OptionT m) where
  liftRel R mx my :=
    LiftRel.liftRel (α := Option _) (fun x y => match x, y with
      | some a, some b => R a b
      | none, none => True
      | _, _ => False) mx my
  liftRel_refl hR mx := by
    apply LiftRel.liftRel_refl (α := Option _)
    intro x; cases x with
    | some a => exact hR a
    | none => trivial
  bind_preserves_liftRel := by
    intro _ _ _ hR _ _ _ h
    apply MonadTail.bind_preserves_liftRel (m := m) (α := Option _) (fun x => by cases x with | some a => exact hR a | none => trivial)
    intro x; cases x with
    | none => apply LiftRel.liftRel_refl (α := Option _); intro x; cases x with | some a => exact hR a | none => trivial
    | some a => exact h a

instance : MonadTail Option where
  liftRel R x y := match x with
    | none => True
    | some a => match y with
      | some b => R a b
      | none => False
  liftRel_refl hR x := by cases x with | some a => exact hR a | none => trivial
  bind_preserves_liftRel := by
    intro _ _ _ _ a _ _ h
    cases a with
    | none => trivial
    | some x => exact h x

instance {ρ : Type u} {m : Type u → Type v} [Monad m] [MonadTail m] :
    MonadTail (ReaderT ρ m) where
  liftRel R mx my := ∀ r, LiftRel.liftRel R (mx r) (my r)
  liftRel_refl hR mx r := LiftRel.liftRel_refl hR (mx r)
  bind_preserves_liftRel := by
    intro _ _ _ hR _ _ _ h r
    show LiftRel.liftRel _ (ReaderT.bind _ _ r) (ReaderT.bind _ _ r)
    simp only [ReaderT.bind]
    exact MonadTail.bind_preserves_liftRel hR (fun x => h x r)

set_option linter.missingDocs false in
noncomputable def ST.bot' [Nonempty α] (s : Void σ) : @FlatOrder (ST.Out σ α) (.mk Classical.ofNonempty (Classical.choice ⟨s⟩)) :=
  .mk Classical.ofNonempty (Classical.choice ⟨s⟩)

instance : MonadTail (ST σ) where
  liftRel {α} R mx my := ∀ s, (R (mx s).val (my s).val ∧ (mx s).state = (my s).state)
  liftRel_refl hR mx s := ⟨hR _, rfl⟩
  bind_preserves_liftRel := by
    intro _ _ R _ a f₁ f₂ h s
    exact h (a s).val (a s).state

instance : MonadTail BaseIO :=
  inferInstanceAs (MonadTail (ST IO.RealWorld))

instance [Nonempty ε] : MonadTail (EST ε σ) where
  liftRel {α} R mx my := ∀ s,
    mx s = EST.bot s ∨
    match mx s, my s with
    | .ok a s₁, .ok b s₂ => R a b ∧ s₁ = s₂
    | .error e₁ s₁, .error e₂ s₂ => e₁ = e₂ ∧ s₁ = s₂
    | _, _ => False
  liftRel_refl hR mx s := by
    exact Or.inr (by cases mx s with | ok a _ => exact ⟨hR a, rfl⟩ | error _ _ => exact ⟨rfl, rfl⟩)
  bind_preserves_liftRel := by
    intro _ _ R hR a f₁ f₂ h s
    show EST.bind a f₁ s = EST.bot s ∨
      match EST.bind a f₁ s, EST.bind a f₂ s with
      | .ok a s₁, .ok b s₂ => R a b ∧ s₁ = s₂
      | .error e₁ s₁, .error e₂ s₂ => e₁ = e₂ ∧ s₁ = s₂
      | _, _ => False
    simp only [EST.bind]
    split
    · next x s' _ => -- a s = .ok x s'
      cases h x s' with
      | inl hbot => left; rw [hbot, EST.bot_const]
      | inr hrel => right; exact hrel
    · next e s' _ => -- a s = .error e s'
      right; exact ⟨rfl, rfl⟩

instance [Nonempty ε] : MonadTail (EIO ε) :=
  inferInstanceAs (MonadTail (EST ε IO.RealWorld))

instance : MonadTail IO :=
  inferInstanceAs (MonadTail (EIO IO.Error))

instance {ω : Type} {σ : Type} {m : Type → Type} [Monad m] [MonadTail m] :
    MonadTail (StateRefT' ω σ m) :=
  inferInstanceAs (MonadTail (ReaderT (ST.Ref ω σ) m))

/-! ## `MonadTail` instances -/

instance : MonadTail Id where
  instCCPO _ := inferInstanceAs (CCPO (FlatOrder Classical.ofNonempty))
  bind_mono_right h := h _

instance {σ : Type u} {m : Type u → Type v} [Monad m] [MonadTail m] [Nonempty σ] :
    MonadTail (StateT σ m) where
  instCCPO β := by
    intro
    haveI : Nonempty (β × σ) := instNonemptyProd
    exact inferInstanceAs (CCPO (σ → m (β × σ)))
  bind_mono_right h s := by
    show (StateT.bind _ _ s) ⊑ (StateT.bind _ _ s)
    simp only [StateT.bind]
    exact MonadTail.bind_mono_right (fun ⟨x, s'⟩ => h x s')

instance {ε : Type u} {m : Type u → Type v} [Monad m] [MonadTail m] :
    MonadTail (ExceptT ε m) where
  instCCPO β := by
    intro
    haveI : Nonempty (Except ε β) := ⟨.ok Classical.ofNonempty⟩
    exact inferInstanceAs (CCPO (m (Except ε β)))
  bind_mono_right h := by
    apply MonadTail.bind_mono_right (m := m)
    intro x; cases x with
    | ok a => exact h a
    | error => exact PartialOrder.rel_refl

instance {m : Type u → Type v} [Monad m] [MonadTail m] :
    MonadTail (OptionT m) where
  instCCPO β := by
    intro
    haveI : Nonempty (Option β) := ⟨some Classical.ofNonempty⟩
    exact inferInstanceAs (CCPO (m (Option β)))
  bind_mono_right h := by
    apply MonadTail.bind_mono_right (m := m)
    intro x; cases x with
    | some a => exact h a
    | none => exact PartialOrder.rel_refl

instance : MonadTail Option where
  instCCPO _ := inferInstance
  bind_mono_right h := by
    cases ‹Option _›
    · exact FlatOrder.rel.refl
    · exact h _

instance : MonadTail (Except ε) where
  instCCPO _ := inferInstanceAs (CCPO (FlatOrder Classical.ofNonempty))
  bind_mono_right h := by
    cases ‹Except ε _›
    · exact FlatOrder.rel.refl
    · exact h _

instance : MonadTail (ST σ) where
  instCCPO _ := inferInstance
  bind_mono_right h := by
    intro s
    show FlatOrder.rel (ST.bind _ _ s) (ST.bind _ _ s)
    simp only [ST.bind]
    exact h _ _

instance : MonadTail BaseIO :=
  inferInstanceAs (MonadTail (ST IO.RealWorld))

instance [Nonempty ε] : MonadTail (EST ε σ) where
  instCCPO _ := inferInstance
  bind_mono_right h w := by
    change FlatOrder.rel (EST.bind _ _ w) (EST.bind _ _ w)
    simp only [EST.bind]
    split
    · apply h
    · exact .refl

instance [Nonempty ε] : MonadTail (EIO ε) :=
  inferInstanceAs (MonadTail (EST ε IO.RealWorld))

instance : MonadTail IO :=
  inferInstanceAs (MonadTail (EIO IO.Error))

instance {ρ : Type u} {m : Type u → Type v} [Monad m] [MonadTail m] :
    MonadTail (ReaderT ρ m) where
  instCCPO _ := inferInstance
  bind_mono_right h r := by
    show (ReaderT.bind _ _ r) ⊑ (ReaderT.bind _ _ r)
    simp only [ReaderT.bind]
    exact MonadTail.bind_mono_right (fun x => h x r)

instance {ω : Type} {σ : Type} {m : Type → Type} [Monad m] [MonadTail m] :
    MonadTail (StateRefT' ω σ m) :=
  inferInstanceAs (MonadTail (ReaderT (ST.Ref ω σ) m))

end Lean.Order
