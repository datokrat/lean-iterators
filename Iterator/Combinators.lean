prelude
import Iterator.Basic

structure Iter (m) (β : Type v) [Iterator α m β] where
  inner : α

@[inline]
def toIter {m} [Iterator α m β] (it : α) : Iter (α := α) m β :=
  ⟨it⟩

instance {m} [Functor m] [Iterator α m β] : Iterator (Iter (α := α) m β) m β where
  yield_rel it it' := Iterator.yield_rel it.inner it'.inner
  skip_rel it it' := Iterator.skip_rel it.inner it'.inner
  step it := (match · with
    | .yield it' x h => .yield ⟨it'⟩ x h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done => .done) <$> (Iterator.step it.inner)

instance [Functor m] [Iterator α m β] [Finite α] : Finite (Iter (α := α) m β) where
  wf := InvImage.wf (finiteIteratorWF ∘ Iter.inner ∘ FiniteIteratorWF.inner) Finite.wf

section Map

-- TODO: more universe polymorphism
variable {m : Type max u v → Type max u v} {α : Type u} {β : Type v} {γ : Type v} {f : β → γ}

variable (α) in
@[specialize]
structure Map [Iterator α m β] (f : β → γ) where
  inner : α

instance [Iterator α m β] [Functor m] : Iterator (Map α f) m γ where
  yield_rel it it' := Iterator.yield_rel it.inner it'.inner
  skip_rel it it' := Iterator.skip_rel it.inner it'.inner
  step it := (match · with
    | .yield it' x h => .yield ⟨it'⟩ (f x) h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done => .done) <$> Iterator.step it.inner

instance [Functor m] [Iterator α m β] [Finite α] : Finite (Map α f) where
  wf := InvImage.wf (finiteIteratorWF ∘ Map.inner ∘ FiniteIteratorWF.inner) Finite.wf

@[inline]
def Iter.map [Iterator α m β] [Functor m] (f : β → γ) (it : Iter (α := α) m β) :
    Iter (α := Map (Iter (α := α) m β) f) m γ :=
  toIter ⟨it⟩

end Map
