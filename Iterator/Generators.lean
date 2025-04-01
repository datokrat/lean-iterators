prelude
import Iterator.Basic
import Iterator.Combinators

variable {m : Type u → Type u}

structure ListIterator (α : Type u) (m : Type u → Type u) where
  list : List α

instance [Pure m] : Iterator (ListIterator α m) m α where
  step
    | { list := .nil } => pure .done
    | { list := x :: xs } => pure <| .yield { list := xs } x

def List.iter {α} (l : List α) (m := Id) [Pure m] : Iter (α := ListIterator α m) m α :=
  toIter { list := l }

instance [Monad m] : WellFoundedRelation (ListIterator α m) :=
  invImage ListIterator.list inferInstance

instance [Monad m] : Finite (ListIterator α m) where
  rel_step := by sorry
