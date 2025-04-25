import Iterator.Combinators.FilterMap

-- section Equivalence

-- variable {α : Type u} {m : Type w → Type w'} {β : Type v}

-- inductive IterTStep (β : Type v) where
--   | yield : β → IterTStep β
--   | skip : IterTStep β
--   | done : IterTStep β

-- inductive IterT (m : Type w → Type w') (β : Type v) : Type w → Type (max v w w' + 1) where
--   | step : ∀ {α}, Nat → (β → α) → IterT m β (IterTStep α)
--   | lift : ∀ {α}, m α → IterT m β α
--   | bind : ∀ {α γ}, IterT m β α → (α → IterT m β γ) → IterT m β γ

-- def IterT.interpret [Iterator α m β] [Monad m] (it : α) (γ : Type w) (x : IterT m β γ) : m γ :=
--   go [it] x |>.mapH (fun p => p.1) |>.run
-- where
--   go {δ : Type w} (its : List α) : IterT m β δ → CodensityT m (δ × List α)
--     | .step n f => match its[n]? with
--       | none => pure (.done, its)
--       | some it =>
--         let v := Iterator.step it
--         v.mapH (match · with
--           | .yield it' out _ => (.yield (f out), it' :: its)
--           | .skip it' _ => (.skip, it' :: its)
--           | .done _ => (.done, its))
--     | .lift x => (CodensityT.eval x).mapH (Prod.mk · its)
--     | .bind x f => (go its x) >>= (fun y => go y.2 (f y.1))

-- end Equivalence

variable {α : Type u} {m : Type w → Type w'} {β : Type v}
  [Iterator α m β] {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β)
  [Monad m]
  (f : β → CodensityT m (Option β'))

-- theorem filterMapMH_step' (it : α) (f : β → IterationT m (Option β')) :
--     Iterator.step (m := m) (Iterator.filterMapMH f it) =
--       (Iterator.step (m := m) it |>.bindH (match · with
--         | .yield it' out h => (f out).computation.mapH (fun x => ⟨match x.val with
--           | none => .skip ⟨it'⟩
--           | some out => .yield ⟨it'⟩ out, .yield it' out, ⟨x.1, rfl, x.2⟩, h⟩)
--         | .skip it' h => pure ⟨.skip ⟨it'⟩, .skip it', rfl, h⟩
--         | .done h => pure ⟨.done, .done, rfl, h⟩)) := by
--   simp [Iterator.filterMapMH, Iterator.step, SimpleIterator.step, computation_matchStepH,
--     IterationT.step, IterationT.mapH, CodensityT.mapH_mapH, IterationT.computation_pure]
--   refine congrArg (CodensityT.bindH _) ?_
--   ext x
--   split
--   · simp
--     refine congrArg (CodensityT.mapH · _) ?_
--     ext y
--     cases y
--     dsimp only
--     split <;> rfl
--   · simp

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

#exit
  simp only [plausible_eq_copy
    (congrArg Iterator.step (inner_toIter ..)),
    congrArg Iterator.step, congrArg FilterMapMH.inner, inner_toIter]

  simp [Iter.filterMapH, Iter.stepH, Iterator.step]
  simp [Iter.filterMapMH, Iter.stepH]
  simp [IterationT.bindH, IterationT.mapH]
  simp only [plausible_eq_copy
    (congrArg (Iterator.step (m := m) (α := α))
      (congrArg FilterMapMH.inner (inner_toIter ..))),
    congrArg Iterator.step, congrArg FilterMapMH.inner, inner_toIter]
  simp [Iterator.filterMapMH]
  simp [toIter, Iter.inner]
  simp [computation_matchStep, IterationT.computation_pure]
  rw [Iterator.step_congr <| ComputableSmall.down_up ..]
  rw [filterMapMH_step']
  simp [CodensityT.map_eq_mapH, CodensityT.mapH_mapH]
  simp [Iter.Step.ofInternal.eq_def, PlausibleIterStep.map_map]
  rw [Iterator.filterMapMH]
  simp [Iter.stepH, Iterator.step, SimpleIterator.step, Iter.Step.ofInternal]

  simp [Iter.stepH, Iterator.step, SimpleIterator.step, CodensityT.map_eq_mapH, CodensityT.mapH_mapH, Iter.Step.ofInternal]

  simp [CodensityT]
  ext
  simp [Iter.stepH, CodensityT.mapH, CodensityT.bindH, Iterator.step, SimpleIterator.step, IterationT.step, Functor.map]
  let proof : (it.filterMapMH f).stepH = sorry := by
    simp [Iter.stepH, Iterator.step, SimpleIterator.step, IterationT.mapH, IterationT.computation_pure,
      CodensityT.map_bindH, IterationT.step]
    split
