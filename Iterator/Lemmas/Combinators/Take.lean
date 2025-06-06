/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Combinators.Take
import Iterator.Consumers.Access
import Iterator.Lemmas.Monadic.Take
import Iterator.Lemmas.Consumers

theorem Iter.take_eq {α β} [Iterator α Id β] {n : Nat}
    {it : Iter (α := α) β} :
    it.take n = (it.toIterM.take n).toPureIter :=
  rfl

theorem Iter.step_take {α β} [Iterator α Id β] {n : Nat}
    {it : Iter (α := α) β} :
    (it.take n).step = (match n with
      | 0 => .done (.depleted rfl)
      | k + 1 =>
        match it.step with
        | .yield it' out h => .yield (it'.take k) out (.yield h rfl)
        | .skip it' h => .skip (it'.take (k + 1)) (.skip h rfl)
        | .done h => .done (.done h)) := by
  simp only [Iter.step, Iter.step, Iter.take_eq, IterM.step_take, toIterM_toPureIter]
  cases n
  case zero =>
    simp [Id.run, PlausibleIterStep.map, PlausibleIterStep.done]
  case succ k =>
    simp only [Id.pure_eq, Id.bind_eq, Id.run, take_eq]
    dsimp only [toIterM_toPureIter]
    generalize it.toIterM.step = step
    obtain ⟨step, h⟩ := step
    cases step <;>
      simp [PlausibleIterStep.map, PlausibleIterStep.yield, PlausibleIterStep.skip,
        PlausibleIterStep.done]

theorem Iter.toList_take_of_finite {α β} [Iterator α Id β] {n : Nat}
    [Finite α Id] [IteratorToArray α Id] [LawfulIteratorToArray α Id]
    {it : Iter (α := α) β} :
    (it.take n).toList = it.toList.take n := by
  revert n
  induction it using Iter.induct with | step it ihy ihs =>
  intro n
  rw [Iter.toList_of_step, Iter.toList_of_step, Iter.step_take]
  cases n
  case zero => simp
  case succ k =>
    simp
    obtain ⟨step, h⟩ := it.step
    cases step
    · simp [ihy h]
    · simp [ihs h]
    · simp

theorem Iter.getAtIdx?_take {α β}
    [Iterator α Id β] [Productive α Id] {k l : Nat}
    {it : Iter (α := α) β} :
    (it.take k).getAtIdx? l = if l < k then it.getAtIdx? l else none := by
  revert k
  fun_induction it.getAtIdx? l
  case case1 it it' out h h' =>
    intro k
    simp [getAtIdx?.eq_def (it := it.take k), getAtIdx?.eq_def (it := it), step_take, h']
    cases k <;> simp
  case case2 it it' out h h' l ih =>
    intro k
    simp [getAtIdx?.eq_def (it := it.take k), getAtIdx?.eq_def (it := it), step_take, h']
    cases k <;> cases l <;> simp [ih]
  case case3 l it it' h h' ih =>
    intro k
    simp [getAtIdx?.eq_def (it := it.take k), getAtIdx?.eq_def (it := it), step_take, h']
    cases k <;> cases l <;> simp [ih]
  case case4 l it h h' =>
    intro k
    simp only [getAtIdx?.eq_def (it := it.take k), getAtIdx?.eq_def (it := it), step_take, h']
    cases k <;> cases l <;> simp
