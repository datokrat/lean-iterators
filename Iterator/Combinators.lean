prelude
import Iterator.Basic

structure Iter (m) (β : Type v) [Iterator α m β] where
  inner : α

@[inline]
def toIter {m} [Iterator α m β] (it : α) : Iter (α := α) m β :=
  ⟨it⟩

instance {m} [Functor m] [Iterator α m β] : Iterator (Iter (α := α) m β) m β where
  step it := (match · with
    | .yield it' x => .yield ⟨it'⟩ x
    | .skip it' => .skip ⟨it'⟩
    | .done => .done) <$> (Iterator.step it.inner)

instance {m} [Iterator α m β] [Monad m] [WellFoundedRelation α] :
    WellFoundedRelation (Iter (α := α) m β) := sorry -- invImage Iter.inner (inferInstanceAs (Finite α)).rel

instance {m} [Iterator α m β] [Monad m] [WellFoundedRelation α] [Finite α] : Finite (Iter (α := α) m β) where
  rel_step := sorry

section Map

-- TODO: more universe polymorphism
variable {m : Type max u v → Type max u v} {α : Type u} {β : Type v} {γ : Type v} {f : β → γ}

variable (α) in
@[specialize]
structure Map [Iterator α m β] (f : β → γ) where
  inner : α

instance [Iterator α m β] [Functor m] : Iterator (Map α f) m γ where
  step it := (match · with
    | .yield it' x => .yield ⟨it'⟩ (f x)
    | .skip it' => .skip ⟨it'⟩
    | .done => .done) <$> Iterator.step it.inner

instance [Iterator α m β] [Monad m] [WellFoundedRelation α] : WellFoundedRelation (Map α f) :=
  invImage Map.inner inferInstance

instance [Iterator α m β] [Monad m] [WellFoundedRelation α] [Finite α] :
    Finite (Map α f) where
  rel_step := sorry

@[inline]
def Iter.map [Iterator α m β] [Functor m] (f : β → γ) (it : Iter (α := α) m β) :
    Iter (α := Map (Iter (α := α) m β) f) m γ :=
  toIter ⟨it⟩

end Map
