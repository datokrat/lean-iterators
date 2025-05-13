/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Producers
import Iterator.Consumers
import Iterator.Lemmas.Monadic.Consumers

section ListIterator

variable {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}

theorem List.step_iterM_nil :
    (([] : List β).iterM m).step =
      pure ⟨.done, by simp [Iterator.plausible_step, iterM, IterM.plausible_step, IterStep.map]⟩ := by
  simp only [iterM, IterM.step, IterM.stepH, IterStep.map, id_eq, Iterator.step, map_pure, USquash.inflate_deflate]
  congr
  simp [toIter]

theorem List.step_iterM_cons {x : β} {xs : List β} :
    ((x :: xs).iterM m).step = pure ⟨.yield (xs.iterM m) x, by simp [iterM, IterM.plausible_step, Iterator.plausible_step, IterStep.map]⟩ := by
  simp only [iterM, IterM.step, IterM.stepH, IterStep.map, id_eq, Iterator.step,
    map_pure, USquash.inflate_deflate]
  congr
  simp [toIter]

theorem ListIterator.toArrayMapped_eq {β : Type w} {γ : Type w} {f : β → m γ}
    {l : List β} :
    IteratorToArray.toArrayMapped f (l.iterM m) = List.toArray <$> l.mapM f := by
  rw [LawfulIteratorToArray.lawful]
  induction l with
  | nil =>
    rw [IterM.DefaultConsumers.toArrayMapped_of_step]
    simp [List.step_iterM_nil]
  | cons x xs ih =>
    rw [IterM.DefaultConsumers.toArrayMapped_of_step]
    simp [List.step_iterM_cons, List.mapM_cons, pure_bind, ih]

theorem List.toArray_iterM {l : List β} :
    (l.iterM m).toArray = pure l.toArray := by
  simp only [IterM.toArray, ListIterator.toArrayMapped_eq]
  rw [mapM_pure, map_pure, List.map_id']

theorem List.toList_iterM {l : List β} :
    (l.iterM m).toList = pure l := by
  rw [← IterM.toList_toArray, List.toArray_iterM, map_pure, toList_toArray]

theorem List.toListRev_iterM {l : List β} :
    (l.iterM m).toListRev = pure l.reverse := by
  simp [IterM.toListRev_eq, List.toList_iterM]

end ListIterator
