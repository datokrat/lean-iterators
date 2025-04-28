import Iterator.Combinators.FilterMap
import Iterator.Consumers

variable {α : Type u} {m : Type w → Type w'} {β : Type v}
  [Iterator α m β] {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β)
  [Monad m]
  (f : β → CodensityT m (Option β'))

theorem FilterMapMH.plausible_of_yield_of_none {it' : Iter (α := α) m β} {out : β}
    (h : it.plausible_step (.yield it' out)) :
    (it.filterMapMH f).plausible_step (.skip (it'.filterMapMH f)) := by
  let step : it.Step := .yield it' out h
  let internalStep := step.toInternal
  simp only [Iter.plausible_step]
  refine ⟨.skip (it'.filterMapMH f).inner, by simp [IterStep.map, Iter.filterMapMH], ?_⟩
  refine ⟨.yield (it'.filterMapMH f).inner.inner out, ?_, ?_⟩
  · exact ⟨none, rfl, True.intro⟩
  · simp only [Iter.filterMapMH, Iterator.filterMapMH, inner_toIter]
    exact internalStep.property

theorem FilterMapMH.plausible_of_yield_of_some {it' : Iter (α := α) m β} {out : β} {out' : β'}
    (h : it.plausible_step (.yield it' out)) :
    (it.filterMapMH f).plausible_step (.yield (it'.filterMapMH f) out') := by
  let step : it.Step := .yield it' out h
  let internalStep := step.toInternal
  refine ⟨.yield (it'.filterMapMH f).inner out', by simp [IterStep.map, Iter.filterMapMH], ?_⟩
  refine ⟨.yield (it'.filterMapMH f).inner.inner out, ?_, ?_⟩
  · exact ⟨some out', rfl, True.intro⟩
  · simp only [Iter.filterMapMH, Iterator.filterMapMH, inner_toIter]
    exact internalStep.property

theorem FilterMapMH.plausible_of_skip {it' : Iter (α := α) m β}
    (h : it.plausible_step (.skip it')) :
    (it.filterMapMH f).plausible_step (.skip (it'.filterMapMH f)) := by
  let step : it.Step := .skip it' h
  let internalStep := step.toInternal
  refine ⟨.skip (it'.filterMapMH f).inner, by simp [IterStep.map, Iter.filterMapMH], ?_⟩
  refine ⟨.skip (it'.filterMapMH f).inner.inner, rfl, ?_⟩
  simp only [Iter.filterMapMH, Iterator.filterMapMH, inner_toIter]
  exact internalStep.property

theorem FilterMapMH.plausible_of_done
    (h : it.plausible_step .done) :
    (it.filterMapMH f).plausible_step .done := by
  let step : it.Step := .done h
  let internalStep := step.toInternal
  refine ⟨.done, by simp [IterStep.map, Iter.filterMapMH], ?_⟩
  refine ⟨.done, rfl, ?_⟩
  simp only [Iter.filterMapMH, Iterator.filterMapMH, inner_toIter]
  exact internalStep.property

theorem filterMapMH_step :
  (it.filterMapMH f).stepH = (it.stepH.bindH (match · with
      | .yield it' out h => (f out).mapH fun
          | none => .skip (it'.filterMapMH f) (FilterMapMH.plausible_of_yield_of_none _ _ h)
          | some out' => .yield (it'.filterMapMH f) out' (FilterMapMH.plausible_of_yield_of_some _ _ h)
      | .skip it' h => pure <| .skip (it'.filterMapMH f) (FilterMapMH.plausible_of_skip _ _ h)
      | .done h => pure <| .done (FilterMapMH.plausible_of_done _ _ h))) := by
  cases it
  simp only [Iter.filterMapMH, Iterator.filterMapMH]
  rw [Iter.stepH, CodensityT.mapH_eq_bindH]
  rw [Iter.stepH, CodensityT.mapH_eq_bindH]
  simp only [plausible_eq_copy
    (congrArg Iterator.step (inner_toIter ..)),
    congrArg Iterator.step, congrArg FilterMapMH.inner, inner_toIter]
  simp only [Iterator.step]
  rw [CodensityT.map_eq_mapH, CodensityT.mapH_eq_bindH]
  simp only [IterationT.bindH]
  simp only [CodensityT.bindH_assoc]
  refine congrArg (CodensityT.bindH _ ·) ?_
  ext x
  simp only [CodensityT.bindH_pure, Iter.Step.ofInternal, IterationT.Plausible.map, IterStep.map]
  match h : x with
  | ⟨.yield .., h⟩ =>
    simp only [matchStep]
    simp only [IterationT.mapH, CodensityT.mapH_eq_bindH, monadLift, MonadLift.monadLift,
      CodensityT.map_eq_mapH, CodensityT.mapH_eq_bindH, CodensityT.bindH_assoc,
      CodensityT.bindH_pure]
    refine congrArg (CodensityT.bindH _ ·) ?_
    ext y
    refine congrArg pure ?_
    simp only [IterationT.Plausible.copy, Iter.Step.yield, Iter.Step.skip, Iter.filterMapMH,
      Iterator.filterMapMH, inner_toIter]
    cases y <;> rfl
  | ⟨.skip .., h⟩ =>
    simp only [matchStep]
    simp only [CodensityT.mapH_eq_bindH, IterationT.computation_pure, CodensityT.bindH_pure,
      IterationT.Plausible.copy, Iter.Step.skip, Iter.filterMapMH, Iterator.filterMapMH,
      inner_toIter]
  | ⟨.done, h⟩ =>
    simp only [matchStep, IterationT.Plausible.copy, CodensityT.mapH_eq_bindH, CodensityT.bindH_assoc,
      IterationT.computation_pure, CodensityT.bindH_pure]
    rfl

-- TODO: Perhaps we should also carry the small instance around in Iter
theorem toList_filterMapMH [Finite α m] [ComputableSmall β] :
    (it.filterMapMH f).toList = it.foldM
