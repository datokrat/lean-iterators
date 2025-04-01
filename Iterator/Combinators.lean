prelude
import Iterator.Basic

structure Iter (β : Type v) [Iterator α β] where
  inner : α

@[inline]
def toIter [Iterator α β] (it : α) : Iter (α := α) β :=
  ⟨it⟩

instance [Iterator α β] : Iterator (Iter (α := α) β) β where
  step it := match Iterator.step it.inner with
    | .yield it' x => .yield ⟨it'⟩ x
    | .skip it' => .skip ⟨it'⟩
    | .done => .done

instance [Iterator α β] (it : Iter (α := α) β) [Finite it.inner] : Finite it where
  finite := sorry

section Map

variable {α : Type u} {β : Type v} {γ : Type w} {f : β → γ}

variable (α) in
@[specialize]
structure Map [Iterator α β] (f : β → γ) where
  inner : α

instance [Iterator α β] : Iterator (Map α f) γ where
  step it := match Iterator.step it.inner with
    | .yield it' x => .yield ⟨it'⟩ (f x)
    | .skip it' => .skip ⟨it'⟩
    | .done => .done

instance [Iterator α β] (it : Map α f) [Finite it.inner] :
    Finite it where
  finite := sorry

@[inline]
def Iter.map [Iterator α β] (f : β → γ) (it : Iter (α := α) β) :
    Iter (α := Map (Iter (α := α) β) f) γ :=
  toIter ⟨it⟩

end Map
