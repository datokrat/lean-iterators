import Iterator.Producers
import Iterator.Consumers
import Iterator.Lemmas.Consumer

section ListIterator

variable {m : Type v → Type v} [Monad m] {β : Type v}

theorem List.step_iter_nil :
    (([] : List β).iter m).step = pure ⟨.done, .done, rfl, rfl⟩ := by
  simp only [iter, Iter.step, CodensityT.run, Iter.stepH, CodensityT.mapH, Iterator.step, pure,
    Function.comp_apply, Iter.Step.ofInternal, IterationT.Plausible.map, IterStep.map, id_eq]
  congr

theorem List.step_iter_cons {x : β} {xs : List β} :
    ((x :: xs).iter m).step = pure ⟨.yield (xs.iter m) x, .yield (xs.iter m).inner x, rfl, rfl⟩ := by
  simp only [iter, Iter.step, CodensityT.run, Iter.stepH, CodensityT.mapH, Iterator.step, pure,
    Function.comp_apply, Iter.Step.ofInternal, IterationT.Plausible.map, IterStep.map, id_eq]
  congr

private theorem List.toArray_iter.aux {l : List β} {acc : Array β} [LawfulMonad m] :
    Iter.toArray.go (l.iter m) acc = pure (acc ++ l.toArray) := by
  induction l generalizing acc with
  | nil =>
    rw [Iter.toArray.go]
    simp [List.step_iter_nil]
  | cons x xs ih =>
    rw [Iter.toArray.go]
    simp [List.step_iter_cons, ih]

theorem List.toArray_iter {l : List β} [LawfulMonad m] :
    Iter.toArray (l.iter m) = pure l.toArray := by
  simp [Iter.toArray, List.toArray_iter.aux]

end ListIterator
