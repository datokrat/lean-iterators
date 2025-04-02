/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic

structure Iter (m) (β : Type v) [Iterator α m β] where
  inner : α

@[inline]
def toIter {m} [Iterator α m β] (it : α) : Iter (α := α) m β :=
  ⟨it⟩

instance {m} [Functor m] [Iterator α m β] : Iterator (Iter (α := α) m β) m β where
  yield_rel it it' b := Iterator.yield_rel it.inner it'.inner b
  skip_rel it it' := Iterator.skip_rel it.inner it'.inner
  step it := (match · with
    | .yield it' x h => .yield ⟨it'⟩ x h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done => .done) <$> (Iterator.step it.inner)

instance [Functor m] [Iterator α m β] [Finite α] : Finite (Iter (α := α) m β) where
  wf := InvImage.wf (finiteIteratorWF ∘ Iter.inner ∘ FiniteIteratorWF.inner) Finite.wf

def Iter.step [Functor m] [Iterator α m β] (it : Iter (α := α) m β) :=
  Iterator.step it

section FilterMap

-- todo: more universe polymorphism
variable {m : Type max u v → Type max u v} {α : Type u} {β γ : Type v} {f : β → Option γ}

variable (α) in
structure FilterMap [Iterator α m β] (f : β → Option γ) where
  inner : α

instance [Iterator α m β] [Functor m] : Iterator (FilterMap α f) m γ where
  yield_rel it it' b := ∃ b', f b' = some b ∧ Iterator.yield_rel it.inner it'.inner b'
  skip_rel it it' := (∃ b', f b' = none ∧ Iterator.yield_rel it.inner it'.inner b') ∨ Iterator.skip_rel it.inner it'.inner
  step it := (match · with
    | .yield it' x h => match h' : f x with
      | none => .skip ⟨it'⟩ (.inl ⟨x, h', h⟩)
      | some y => .yield ⟨it'⟩ y ⟨x, h', h⟩
    | .skip it' h => .skip ⟨it'⟩ (.inr h)
    | .done => .done) <$> Iterator.step it.inner

theorem FilterMap.subrel [Functor m] [Iterator α m β] :
    Subrelation
      (FiniteIteratorWF.lt (α := (FilterMap α f)))
      (InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ FilterMap.inner ∘ FiniteIteratorWF.inner)) := by
  intro x y hlt
  simp only [FiniteIteratorWF.lt, Iterator.yield_rel, Iterator.skip_rel] at hlt
  obtain ⟨b, b', h⟩ | ⟨b', h⟩ | h := hlt
  · exact Or.inl ⟨b', h.2⟩
  · exact Or.inl ⟨b', h.2⟩
  · exact Or.inr h

instance [Functor m] [Iterator α m β] [Finite α] : Finite (FilterMap α f) where
  wf := FilterMap.subrel.wf <| InvImage.wf (finiteIteratorWF ∘ FilterMap.inner ∘ FiniteIteratorWF.inner) Finite.wf

@[inline]
def Iter.filterMap [Iterator α m β] [Functor m] (f : β → Option γ) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) f) m γ :=
  toIter ⟨it⟩

@[inline]
def Iter.map [Iterator α m β] [Functor m] (f : β → γ) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) (some ∘ f)) m γ :=
  toIter ⟨it⟩

@[inline]
def Iter.filter [Iterator α m β] [Functor m] (f : β → Bool) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) (fun x => if f x then some x else none)) m β :=
  toIter ⟨it⟩

end FilterMap
