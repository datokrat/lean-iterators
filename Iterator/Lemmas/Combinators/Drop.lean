/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Combinators.Drop
import Iterator.Lemmas.Monadic.Drop
import Iterator.Lemmas.Consumers

theorem Iter.drop_eq {α β} [Iterator α Id β] {n : Nat}
    {it : Iter (α := α) β} :
    it.drop n = (it.toIterM.drop n).toPureIter :=
  rfl

theorem Iter.step_drop {α β} [Iterator α Id β] {n : Nat}
    {it : Iter (α := α) β} :
    (it.drop n).step = (match it.step with
    | .yield it' out h =>
      match n with
      | 0 => .yield (it'.drop 0) out (.yield h rfl)
      | k + 1 => .skip (it'.drop k) (.drop h rfl)
    | .skip it' h => .skip (it'.drop n) (.skip h)
    | .done h => .done (.done h)) := by
  simp only [Iter.step, Iter.step, Iter.drop_eq, IterM.stepH_drop, toIterM_toPureIter]
  simp only [Id.pure_eq, Id.bind_eq, Id.run, drop_eq]
  dsimp only [toIterM_toPureIter]
  generalize it.toIterM.stepH.inflate = step
  obtain ⟨step, h⟩ := step
  cases step <;> cases n <;>
    simp [PlausibleIterStep.map, PlausibleIterStep.yield, PlausibleIterStep.skip,
      PlausibleIterStep.done]

theorem Iter.toList_drop_of_finite {α β} [Iterator α Id β] {n : Nat}
    [Finite α Id] [IteratorToArray α Id] [LawfulIteratorToArray α Id]
    {it : Iter (α := α) β} :
    (it.drop n).toList = it.toList.drop n := by
  revert n
  induction it using Iter.induct with | step it ihy ihs =>
  intro n
  rw [Iter.toList_of_step, Iter.toList_of_step, Iter.step_drop]
  obtain ⟨step, h⟩ := it.step
  cases step
  · cases n <;> simp [ihy h]
  · simp [ihs h]
  · simp
