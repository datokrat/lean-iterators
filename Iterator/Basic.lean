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

inductive IterStep (α β) where
| yield : (a : α) → β → IterStep α β
| skip : (a : α) → IterStep α β
| done : IterStep α β

variable {p} in
def IterStep.successor : IterStep α β → Option α
  | .yield it _ => some it
  | .skip it => some it
  | .done => none

class Iterator (α : Type u) (m : outParam (Type (max u v) → Type (max u v))) (β : outParam (Type v)) where
  step : α → m (IterStep α β)

class Finite (α : Type u) [Monad m] [Iterator α m β] [WellFoundedRelation α] where
  rel_step : ∀ it : α, satisfies₃ (Iterator.step it) (fun step => match step with
      | .yield it' _ => WellFoundedRelation.rel it' it
      | .skip it' => WellFoundedRelation.rel it' it
      | .done => True)

class Productive (α : Type u) [Monad m] [Iterator α m β] where
  rel : WellFoundedRelation α
  rel_step : ∀ it : α, satisfies₃ (Iterator.step it) (fun step => match step with
      | .yield _ _ => True
      | .skip it' => rel.rel it' it
      | .done => True)

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
