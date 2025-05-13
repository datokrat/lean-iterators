/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Lemmas.Consumers
import Iterator.Lemmas.Monadic.FilterMap
import Iterator.Combinators.FilterMap

theorem Iter.filterMap_eq {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → Option γ} :
    it.filterMap f = (it.toIterM.filterMapH f).toPureIter :=
  rfl

theorem Iter.map_eq {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → γ} :
    it.map f = (it.toIterM.mapH f).toPureIter :=
  rfl

theorem Iter.filter_eq {α β} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → Bool} :
    it.filter f = (it.toIterM.filter f).toPureIter :=
  rfl

theorem Iter.filterMap_step {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → Option γ} :
    (it.filterMap f).step = match it.step with
      | .yield it' out h =>
        match h' : f out with
        | none => .skip (it'.filterMap f) (.yieldNone (out := out) h h')
        | some out' => .yield (it'.filterMap f) out' (.yieldSome (out := out) h h')
      | .skip it' h => .skip (it'.filterMap f) (.skip h)
      | .done h => .done (.done h) := by
  simp only [filterMap_eq, step, toIterM_toPureIter, Id.run, IterM.filterMapH_stepH, Id.pure_eq,
    Id.bind_eq]
  generalize it.toIterM.stepH.inflate = step
  obtain ⟨step, h⟩ := step
  apply Subtype.ext
  match step with
  | .yield it' out =>
    simp only [PlausibleIterStep.map, IterStep.map_yield, id_eq, toIterM_toPureIter,
      PlausibleIterStep.yield, PlausibleIterStep.skip]
    split <;> split
    all_goals
      simp only [USquash.inflate_deflate, IterStep.map_yield, id_eq, reduceCtorEq]
      simp_all
  | .skip it' =>
    simp [PlausibleIterStep.map, IterStep.map_yield, id_eq, toIterM_toPureIter,
      PlausibleIterStep.skip]
  | .done =>
    simp [PlausibleIterStep.map, PlausibleIterStep.done]

theorem Iter.toList_filterMap {α β γ} [Iterator α Id β] [IteratorToArray α Id] [LawfulIteratorToArray α Id]
    {f : β → Option γ} {it : Iter (α := α) β} :
    (it.filterMap f).toList = it.toList.filterMap f := by
  simp [filterMap_eq, toList_eq_toList_toIterM, IterM.toList_filterMapH]

theorem Iter.toList_map {α β γ} [Iterator α Id β] [IteratorToArray α Id] [LawfulIteratorToArray α Id]
    {f : β → γ} {it : Iter (α := α) β} :
    (it.map f).toList = it.toList.map f := by
  simp [map_eq, IterM.toList_mapH, Iter.toList_eq_toList_toIterM]

theorem Iter.toList_filter {α β} [Iterator α Id β] [IteratorToArray α Id] [LawfulIteratorToArray α Id]
    {f : β → Bool} {it : Iter (α := α) β} :
    (it.filter f).toList = it.toList.filter f := by
  simp [filter_eq, IterM.toList_filter, Iter.toList_eq_toList_toIterM]
