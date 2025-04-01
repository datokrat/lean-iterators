prelude
import Iterator.Basic
import Iterator.Combinators

structure ListIterator (α : Type u) where
  list : List α

instance : Iterator (ListIterator α) α where
  step
    | { list := .nil } => .done
    | { list := x :: xs } => .yield { list := xs } x

def List.iter {α} (l : List α) : Iter (α := ListIterator α) α :=
  toIter { list := l }

theorem terminatesAfter_list (it : ListIterator α) :
    terminatesAfter it = fun n => it.list.length ≤ n := by
  cases it; rename_i l
  dsimp only
  induction l with
  | nil =>
    ext
    rw [terminatesAfter.eq_def]
    simp only [Option.elim, IterStep.successor, List.length_nil, Nat.zero_le, decide_true]
    split <;> rfl
  | cons x xs ih =>
    ext
    rw [List.length_cons, terminatesAfter.eq_def]
    simp only [Iterator.step, IterStep.successor, Option.elim]
    split <;> simp [ih]

theorem stepsRemaining?_list (it : ListIterator α) :
    stepsRemaining? it = it.list.length := by
  simp only [stepsRemaining?, terminatesAfter_list, decide_eq_true_iff, Nat.inf_ge]

instance (it : ListIterator α) : Finite it where
  finite := by simp [stepsRemaining?_list]
