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

inductive IterStep (α β) (yielded : α → β → Prop) (skipped : α → Prop) (finished : Prop) where
| yield : (it : α) → (b : β) → yielded it b → IterStep α β yielded skipped finished
| skip : (a : α) → skipped a → IterStep α β yielded skipped finished
| done : finished → IterStep α β yielded skipped finished

class Iterator (α : Type u) (m : outParam (Type (max u v) → Type (max u v))) (β : outParam (Type v)) where
  yielded : α → α → β → Prop
  skipped : α → α → Prop
  finished : α → Prop
  step : (a : α) → m (IterStep α β (yielded a) (skipped a) (finished a))

section Finite

structure FiniteIteratorWF (α : Type u) [Iterator α m β] where
  inner : α

def FiniteIteratorWF.lt {α m β} [Iterator α m β] (x y : FiniteIteratorWF α) : Prop :=
  (∃ b, Iterator.yielded y.inner x.inner b) ∨ Iterator.skipped y.inner x.inner

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
  Iterator.skipped y.inner x.inner

def productiveIteratorWF {α m β} [Iterator α m β] (it : α) : ProductiveIteratorWF α :=
  ⟨it⟩

class Productive (α) [Iterator α m β] : Prop where
  wf : WellFounded (ProductiveIteratorWF.lt (α := α))

instance [Iterator α m β] [Productive α] : WellFoundedRelation (ProductiveIteratorWF α) where
  rel := ProductiveIteratorWF.lt
  wf := Productive.wf

theorem ProductiveIteratorWF.subrelation_finiteIteratorWF {α m β} [Iterator α m β] :
    Subrelation (α := ProductiveIteratorWF α)
      ProductiveIteratorWF.lt
      (InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ inner)) := by
  intro x y
  exact Or.inr

instance [Iterator α m β] [Finite α] : Productive α where
  wf := ProductiveIteratorWF.subrelation_finiteIteratorWF.wf (InvImage.wf _ Finite.wf)

end Productive
