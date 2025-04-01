/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core
import Init.Classical
import Init.Ext
import Init.NotationExtra
import Init.TacticsExtra

variable {α : Type u} {β : Type v}

/-
- How to inherit `Finite` instances
- Enable `if _ : it.has_next then ... it.next ...`
- Bundling
- Is bundling still efficient?

Options:
- double down on bundling and include a flag in the type that determines the finiteness
  (what are the consequences for codegen?)
- let α be a type family parameterized by such a flag
- have `Finite α`; sad: user needs to prove closedness under succession
- have bundled type (not class) `Iterator α β p`, where `p` is a succession invariant

-/

inductive IterStep (α β) where
| yield : (a : α) → β → IterStep α β
| skip : (a : α) → IterStep α β
| done : IterStep α β

variable {p} in
def IterStep.successor : IterStep α β → Option α
  | .yield it _ => some it
  | .skip it => some it
  | .done => none

class Iterator (α : Type u) (β : outParam (Type v)) where
  step : α → IterStep α β

def terminatesAfter [Iterator α β] (it : α) : Nat → Bool
  | 0 => match Iterator.step it with
    | .done => true
    | _ => false
  | n + 1 => (Iterator.step it).successor.elim true (terminatesAfter · n)


noncomputable def Nat.inf (p : Nat → Prop) : Option Nat := by
  if h : ∃ n, p n ∧ ∀ m, p m → n ≤ m then
    exact some (h.choose)
  else
    exact none

@[simp]
theorem Nat.inf_ge (n : Nat) :
    Nat.inf (fun m => n ≤ m) = some n := by
  rw [Nat.inf]
  split <;> rename_i h
  · simp only [Option.some.injEq]
    have hle := h.choose_spec.2 n (Nat.le_refl n)
    have hge := h.choose_spec.1
    exact Nat.le_antisymm (h.choose_spec.2 n (Nat.le_refl n)) h.choose_spec.1
  · simp only [not_exists, not_and, Classical.not_forall, not_imp, Nat.not_le] at h
    exfalso
    obtain ⟨m, hle, hgt⟩ := h n (Nat.le_refl n)
    rw [Nat.lt_iff_le_not_le] at hgt
    simp_all

@[simp]
theorem Nat.inf_true :
    Nat.inf (fun _ => true) = some 0 := by
  simpa using Nat.inf_ge 0

noncomputable def stepsRemaining? [Iterator α β] (it : α) : Option Nat :=
  Nat.inf fun n => terminatesAfter it n

theorem terminatesAfter_step [Iterator α β] {it it' : α} (h : (Iterator.step it).successor = some it') :
    terminatesAfter it' = fun n => terminatesAfter it (n + 1) := by
  simp only [terminatesAfter, IterStep.successor]
  split <;> simp_all [Option.elim, IterStep.successor]

theorem stepsRemaining?_step [Iterator α β] {it it' : α} (h : (Iterator.step it).successor = some it') :
    stepsRemaining? it' = (stepsRemaining? it).map (· - 1) := by
  simp only [stepsRemaining?, terminatesAfter_step h]
  sorry

class Finite [Iterator α β] (it : α) where
  finite : (stepsRemaining? it).isSome

theorem Finite.yield [Iterator α β] {it it' : α} [Finite it] {x} (h : Iterator.step it = .yield it' x) :
    Finite it' := by sorry

theorem Finite.skip [Iterator α β] {it it' : α} [Finite it] (h : Iterator.step it = .skip it') :
    Finite it' := by sorry

noncomputable def stepsRemaining [Iterator α β] (it : α) [Finite it] : Nat :=
  stepsRemaining? it |>.get Finite.finite
