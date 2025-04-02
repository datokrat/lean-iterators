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
import Iterator.MonadSatisfying

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

Inductive definition of monadic termination?
- the empty iterator terminates
- an iterator that always produces terminating successors terminates

example :
1) read bytes from disk
2) print each byte

This execution can be arbitrarily long, but it is terminating!

def. empty iterator: it.step >>= f = it.step >>= g whenever f .stop = g.stop

bounded iterators: empty after n steps, for some n -> terminating

example:
1) read file
2) do something for each byte
3) then read another file
4) do something for each byte

A priori, you can't say that the number of remaining steps will be known after `n` steps.
Only after reading the second file, which can be arbitrarily far in the future.

def. terminating successor: there's a WF relation _in_ the monad? What does this mean?

it.successorM.suffices fun it' => it' < it
-/

inductive IterStep (α β) (yield_prop : α → β → Prop) (skip_prop : α → Prop) where
| yield : (it : α) → (b : β) → yield_prop it b → IterStep α β yield_prop skip_prop
| skip : (a : α) → skip_prop a → IterStep α β yield_prop skip_prop
| done : IterStep α β yield_prop skip_prop

variable {yp sp} in
def IterStep.successor : IterStep α β yp sp → Option α
  | .yield it _ _ => some it
  | .skip it _ => some it
  | .done => none

class Iterator (α : Type u) (m : outParam (Type (max u v) → Type (max u v))) (β : outParam (Type v)) where
  yield_rel : α → α → β → Prop
  skip_rel : α → α → Prop
  step : (a : α) → m (IterStep α β (yield_rel a) (skip_rel a))

section Finite

structure FiniteIteratorWF (α : Type u) [Iterator α m β] where
  inner : α

def FiniteIteratorWF.lt {α m β} [Iterator α m β] (x y : FiniteIteratorWF α) : Prop :=
  (∃ b, Iterator.yield_rel y.inner x.inner b) ∨ Iterator.skip_rel y.inner x.inner

def finiteIteratorWF {α m β} [Iterator α m β] (it : α) : FiniteIteratorWF α :=
  ⟨it⟩

class Finite (α) [Iterator α m β] : Prop where
  wf : WellFounded (FiniteIteratorWF.lt (α := α))

instance [Iterator α m β] [Finite α] : WellFoundedRelation (FiniteIteratorWF α) where
  rel := FiniteIteratorWF.lt
  wf := Finite.wf

macro_rules | `(tactic| decreasing_trivial) => `(tactic| first | exact Or.inl ⟨_, ‹_›⟩ | exact Or.inr ‹_›)

end Finite

section Productive

structure ProductiveIteratorWF (α : Type u) [Iterator α m β] where
  inner : α

def ProductiveIteratorWF.lt {α m β} [Iterator α m β] (x y : ProductiveIteratorWF α) : Prop :=
  Iterator.skip_rel y.inner x.inner

def productiveIteratorWF {α m β} [Iterator α m β] (it : α) : ProductiveIteratorWF α :=
  ⟨it⟩

class Productive (α) [Iterator α m β] : Prop where
  wf : WellFounded (ProductiveIteratorWF.lt (α := α))

instance [Iterator α m β] [Productive α] : WellFoundedRelation (ProductiveIteratorWF α) where
  rel := ProductiveIteratorWF.lt
  wf := Productive.wf

end Productive

-- def terminatesAfter [Iterator α β] (it : α) : Nat → Bool
--   | 0 => match Iterator.step it with
--     | .done => true
--     | _ => false
--   | n + 1 => (Iterator.step it).successor.elim true (terminatesAfter · n)


-- noncomputable def Nat.inf (p : Nat → Prop) : Option Nat := by
--   if h : ∃ n, p n ∧ ∀ m, p m → n ≤ m then
--     exact some (h.choose)
--   else
--     exact none

-- @[simp]
-- theorem Nat.inf_ge (n : Nat) :
--     Nat.inf (fun m => n ≤ m) = some n := by
--   rw [Nat.inf]
--   split <;> rename_i h
--   · simp only [Option.some.injEq]
--     have hle := h.choose_spec.2 n (Nat.le_refl n)
--     have hge := h.choose_spec.1
--     exact Nat.le_antisymm (h.choose_spec.2 n (Nat.le_refl n)) h.choose_spec.1
--   · simp only [not_exists, not_and, Classical.not_forall, not_imp, Nat.not_le] at h
--     exfalso
--     obtain ⟨m, hle, hgt⟩ := h n (Nat.le_refl n)
--     rw [Nat.lt_iff_le_not_le] at hgt
--     simp_all

-- @[simp]
-- theorem Nat.inf_true :
--     Nat.inf (fun _ => true) = some 0 := by
--   simpa using Nat.inf_ge 0

-- noncomputable def stepsRemaining? [Iterator α β] (it : α) : Option Nat :=
--   Nat.inf fun n => terminatesAfter it n

-- theorem terminatesAfter_step [Iterator α β] {it it' : α} (h : (Iterator.step it).successor = some it') :
--     terminatesAfter it' = fun n => terminatesAfter it (n + 1) := by
--   simp only [terminatesAfter, IterStep.successor]
--   split <;> simp_all [Option.elim, IterStep.successor]

-- theorem stepsRemaining?_step [Iterator α β] {it it' : α} (h : (Iterator.step it).successor = some it') :
--     stepsRemaining? it' = (stepsRemaining? it).map (· - 1) := by
--   simp only [stepsRemaining?, terminatesAfter_step h]
--   sorry

-- class Finite [Iterator α β] (it : α) where
--   finite : (stepsRemaining? it).isSome

-- theorem Finite.yield [Iterator α β] {it it' : α} [Finite it] {x} (h : Iterator.step it = .yield it' x) :
--     Finite it' := by sorry

-- theorem Finite.skip [Iterator α β] {it it' : α} [Finite it] (h : Iterator.step it = .skip it') :
--     Finite it' := by sorry

-- noncomputable def stepsRemaining [Iterator α β] (it : α) [Finite it] : Nat :=
--   stepsRemaining? it |>.get Finite.finite
