import Iterator.Producers
import Iterator.Consumers
import Iterator.Lemmas.Consumer

section ListIterator

variable {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}

theorem List.step_iter_nil :
    (([] : List β).iter m).step =
      pure ⟨.done, by simp [Iterator.plausible_step, List.iter, Iter.plausible_step, IterStep.map]⟩ := by
  simp only [iter, Iter.step, Iter.stepH, IterStep.map, id_eq, Iterator.step, map_pure, USquash.inflate_deflate]
  congr
  simp [toIter]

theorem List.step_iter_cons {x : β} {xs : List β} :
    ((x :: xs).iter m).step = pure ⟨.yield (xs.iter m) x, by simp [List.iter, Iter.plausible_step, Iterator.plausible_step, IterStep.map]⟩ := by
  simp only [iter, Iter.step, Iter.stepH, IterStep.map, id_eq, Iterator.step,
    map_pure, USquash.inflate_deflate]
  congr
  simp [toIter]

theorem ListIterator.toArrayMapped_eq {β : Type w} {γ : Type w} {f : β → m γ}
    {l : List β} :
    IteratorToArray.toArrayMapped f (l.iter m) = List.toArray <$> l.mapM f := by
  rw [LawfulIteratorToArray.lawful]
  induction l with
  | nil =>
    rw [Iter.DefaultConsumers.toArrayMapped_of_step]
    simp [List.step_iter_nil]
  | cons x xs ih =>
    rw [Iter.DefaultConsumers.toArrayMapped_of_step]
    simp [List.step_iter_cons, List.mapM_cons, pure_bind, ih]

theorem List.toArray_iter {l : List β} :
    Iter.toArray (l.iter m) = pure l.toArray := by
  simp only [Iter.toArray, ListIterator.toArrayMapped_eq]
  rw [mapM_pure, map_pure, List.map_id']

theorem List.toList_iter {l : List β} :
    Iter.toList (l.iter m) = pure l := by
  rw [← Iter.toList_toArray, List.toArray_iter, map_pure, toList_toArray]

end ListIterator
