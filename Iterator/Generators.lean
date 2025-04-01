prelude
import Iterator.Basic
import Iterator.Combinators

variable {m : Type u → Type u}

structure ListIterator (α : Type u) (m : Type u → Type u) where
  list : List α

instance [Pure m] : Iterator (ListIterator α m) m α where
  yield_rel it it' := ∃ a, it.list = a :: it'.list
  skip_rel it it' := False
  step
    | { list := .nil } => pure .done
    | { list := x :: xs } => pure <| .yield { list := xs } x (by simp)

def List.iter {α} (l : List α) (m := Id) [Pure m] : Iter (α := ListIterator α m) m α :=
  toIter { list := l }

theorem test [Pure m] :
    Subrelation (FiniteIteratorWF.lt (α := ListIterator α m))
      (InvImage WellFoundedRelation.rel (ListIterator.list ∘ FiniteIteratorWF.inner)) := by
  intro x y hlt
  simp_wf
  simp only [FiniteIteratorWF.lt, Iterator.yield_rel, Iterator.skip_rel, or_false] at hlt
  cases hlt
  simp_all

instance [Pure m] : Finite (ListIterator α m) where
  wf := test.wf (InvImage.wf _ WellFoundedRelation.wf)
