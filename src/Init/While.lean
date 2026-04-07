/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Core
public import Init.Internal.Order.ExtrinsicFix

public section

/-!
# Notation for `while` and `repeat` loops.
-/

namespace Lean

/-! # `repeat` and `while` notation -/

inductive Loop where
  | mk

open Lean.Order in
@[inline]
def Loop.forIn {β : Type u} {m : Type u → Type v} [Monad m]
    (_ : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  haveI : Nonempty (β → m β) := ⟨fun b => pure b⟩
  Lean.Order.extrinsicFix (fun (cont : β → m β) (b : β) => do
    match ← f () b with
    | .done val => pure val
    | .yield val => cont val) init

instance [Monad m] : ForIn m Loop Unit where
  forIn := Loop.forIn

open Lean.Order in
theorem Loop.forIn_eq [Monad m] [MonadTail m]
    {l : Loop} {b : β} {f : Unit → β → m (ForInStep β)} :
    Loop.forIn l b f = (do
      match ← f () b with
      | .done val => pure val
      | .yield val => Loop.forIn l val f) := by
  haveI : Nonempty β := ⟨b⟩
  simp only [Loop.forIn]
  apply congrFun
  apply extrinsicFix_eq
  intro cont₁ cont₂ h b'
  apply MonadTail.bind_mono_right
  intro r
  cases r with
  | done => exact PartialOrder.rel_refl
  | yield val => exact h val

syntax (name := doRepeat) "repeat " doSeq : doElem

macro_rules
  | `(doElem| repeat $seq) => `(doElem| for _ in Loop.mk do $seq)

syntax "while " ident " : " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| while $h : $cond do $seq) => `(doElem| repeat if $h:ident : $cond then $seq else break)

syntax "while " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| while $cond do $seq) => `(doElem| repeat if $cond then $seq else break)

syntax "repeat " doSeq ppDedent(ppLine) "until " term : doElem

macro_rules
  | `(doElem| repeat $seq until $cond) => `(doElem| repeat do $seq:doSeq; if $cond then break)

end Lean
