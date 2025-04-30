import Iterator.Producers
import Iterator.Consumers
import Iterator.Lemmas.Consumer

section ListIterator

variable {m : Type v → Type v} [Monad m] [LawfulMonad m] {β : Type v}

theorem List.step_iter_nil :
    (([] : List β).iter m).step = pure ⟨.done, by simp [Iterator.plausible_step, List.iter, Iter.plausible_step, IterStep.map]⟩ := by
  simp only [iter, Iter.step, Iter.stepH, Iter.Step.ofInternal, IterStep.map, id_eq, Iterator.step,
    map_pure, USquash.inflate_deflate]
  congr
  unfold Iter.stepH.proof_1 -- :(
  rw [inner_toIter]
  simp

theorem List.step_iter_cons {x : β} {xs : List β} :
    ((x :: xs).iter m).step = pure ⟨.yield (xs.iter m) x, by simp [List.iter, Iter.plausible_step, Iterator.plausible_step, IterStep.map]⟩ := by
  simp only [iter, Iter.step, Iter.stepH, Iter.Step.ofInternal, IterStep.map, id_eq, Iterator.step,
    map_pure, USquash.inflate_deflate]
  congr
  unfold Iter.stepH.proof_1
  rw [inner_toIter]
  simp

private theorem List.toArray_iter.aux {l : List β} {acc : Array β} :
    Iter.toArray.go (l.iter m) acc = pure (acc ++ l.toArray) := by
  induction l generalizing acc with
  | nil =>
    rw [Iter.toArray.go]
    simp [List.step_iter_nil]
  | cons x xs ih =>
    rw [Iter.toArray.go]
    simp [List.step_iter_cons, ih]

theorem List.toArray_iter {l : List β} :
    Iter.toArray (l.iter m) = pure l.toArray := by
  simp [Iter.toArray, List.toArray_iter.aux]

end ListIterator
