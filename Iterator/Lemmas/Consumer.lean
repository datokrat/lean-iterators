import Iterator.Producers
import Iterator.Consumers
import Iterator.Combinators.FilterMap

section Consumers

def Iter.induct {α m β} {_ : Iterator α m β} [Finite α m]
  (motive : Iter (α := α) m β → Sort x)
  (step : (it : Iter (α := α) m β) →
    (ih_yield : ∀ {it' : Iter (α := α) m β} {out : β}, it.plausible_step (.yield it' out) → motive it') →
    (ih_skip : ∀ {it' : Iter (α := α) m β}, it.plausible_step (.skip it') → motive it' ) →
    motive it) (it : Iter (α := α) m β) : motive it :=
  step _ (fun {it' _} _ => Iter.induct motive step it') (fun {it'} _ => Iter.induct motive step it')
termination_by it.terminationByFinite

theorem Iter.DefaultConsumers.toArrayMapped.go.aux₁ [Monad m] [LawfulMonad m] {_ : Iterator α m β} [Finite α m]
    {it : Iter (α := α) m β} {b : γ} {bs : Array γ} {f : β → m γ} :
    Iter.DefaultConsumers.toArrayMapped.go f it (#[b] ++ bs) = (#[b] ++ ·) <$> Iter.DefaultConsumers.toArrayMapped.go f it bs := by
  induction it, bs using Iter.DefaultConsumers.toArrayMapped.go.induct
  next it bs ih₁ ih₂ =>
  rw [go, map_eq_pure_bind, go, bind_assoc]
  refine congrArg (Iter.stepH it >>= ·) ?_
  ext step
  generalize step.inflate = step
  split
  · simp [ih₁ _ _ ‹_›]
  · simp [ih₂ _ ‹_›]
  · simp

theorem Iter.DefaultConsumers.toArrayMapped.go.aux₂ [Monad m] [LawfulMonad m]
    {_ : Iterator α m β} [Finite α m] {it : Iter (α := α) m β} {acc : Array γ} {f : β → m γ} :
    Iter.DefaultConsumers.toArrayMapped.go f it acc =
      (acc ++ ·) <$> Iter.DefaultConsumers.toArrayMapped f it := by
  rw [← Array.toArray_toList (xs := acc)]
  generalize acc.toList = acc
  induction acc with
  | nil => simp [toArrayMapped]
  | cons x xs ih =>
    rw [List.toArray_cons, Iter.DefaultConsumers.toArrayMapped.go.aux₁, ih]
    simp only [Functor.map_map, Array.append_assoc]

theorem Iter.DefaultConsumers.toArrayMapped_of_stepH [Monad m] [LawfulMonad m]
    {_ : Iterator α m β} [Finite α m] {it : Iter (α := α) m β} {f : β → m γ} :
    Iter.DefaultConsumers.toArrayMapped f it = (do
      match (← it.stepH).inflate with
      | .yield it' out _ => return #[← f out] ++ (← Iter.DefaultConsumers.toArrayMapped f it')
      | .skip it' _ => Iter.DefaultConsumers.toArrayMapped f it'
      | .done _ => return #[]) := by
  rw [Iter.DefaultConsumers.toArrayMapped, Iter.DefaultConsumers.toArrayMapped.go]
  apply bind_congr
  intro step
  generalize step.inflate = step
  split <;> simp [Iter.DefaultConsumers.toArrayMapped.go.aux₂]

theorem Iter.DefaultConsumers.toArrayMapped_of_step [Monad m] [LawfulMonad m]
    {_ : Iterator α m β} [Finite α m] {it : Iter (α := α) m β} {f : β → m γ} :
    Iter.DefaultConsumers.toArrayMapped f it = (do
      match ← it.step with
      | .yield it' out _ => return #[← f out] ++ (← Iter.DefaultConsumers.toArrayMapped f it')
      | .skip it' _ => Iter.DefaultConsumers.toArrayMapped f it'
      | .done _ => return #[]) := by
  rw [Iter.DefaultConsumers.toArrayMapped_of_stepH, Iter.step, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  generalize step.inflate = step
  rw [pure_bind]
  rfl

theorem Iter.toArray_of_step [Monad m] [LawfulMonad m]
    {_ : Iterator α m β} [IteratorToArray α m] [LawfulIteratorToArray α m]
    {it : Iter (α := α) m β} :
    it.toArray = (do
      match ← it.step with
      | .yield it' out _ => return #[out] ++ (← it'.toArray)
      | .skip it' _ => it'.toArray
      | .done _ => return #[]) := by
  rw [Iter.toArray, LawfulIteratorToArray.lawful, Iter.DefaultConsumers.toArrayMapped_of_step]
  simp [Iter.toArray, LawfulIteratorToArray.lawful]

theorem Iter.toList_toArray [Monad m] {_ : Iterator α m β} [IteratorToArray α m]
    {it : Iter (α := α) m β} :
    Array.toList <$> it.toArray = it.toList := by
  simp [Iter.toList]

theorem Iter.toArray_toList [Monad m] [LawfulMonad m] {_ : Iterator α m β} [IteratorToArray α m]
    {it : Iter (α := α) m β} :
    List.toArray <$> it.toList = it.toArray := by
  simp [Iter.toList]

theorem Iter.toList_of_step [Monad m] [LawfulMonad m] {_ : Iterator α m β}
    [IteratorToArray α m] [LawfulIteratorToArray α m] {it : Iter (α := α) m β} :
    it.toList = (do
      match ← it.step with
      | .yield it' out _ => return out :: (← it'.toList)
      | .skip it' _ => it'.toList
      | .done _ => return []) := by
  simp [← Iter.toList_toArray]
  rw [Iter.toArray_of_step, map_eq_pure_bind, bind_assoc]
  refine congrArg (_ >>= ·) ?_
  ext step
  split <;> simp

theorem Iter.reverseToList.go.aux₁ [Monad m] [LawfulMonad m] {_ : Iterator α m β} [Finite α m]
    {it : Iter (α := α) m β} {b : β} {bs : List β} :
    Iter.reverseToList.go it (bs ++ [b]) = (· ++ [b]) <$> Iter.reverseToList.go it bs:= by
  induction it, bs using Iter.reverseToList.go.induct
  next it bs ih₁ ih₂ =>
  rw [go, go, map_eq_pure_bind, bind_assoc]
  refine congrArg (Iter.step it >>= ·) ?_
  ext step
  simp only [List.cons_append] at ih₁
  split <;> simp [*]

theorem Iter.reverseToList.go.aux₂ [Monad m] [LawfulMonad m] {_ : Iterator α m β} [Finite α m]
    {it : Iter (α := α) m β} {acc : List β} :
    Iter.reverseToList.go it acc = (· ++ acc) <$> it.reverseToList := by
  rw [← List.reverse_reverse (as := acc)]
  generalize acc.reverse = acc
  induction acc with
  | nil => simp [reverseToList]
  | cons x xs ih => simp [Iter.reverseToList.go.aux₁, ih]

theorem Iter.reverseToList_of_step [Monad m] [LawfulMonad m] {_ : Iterator α m β} [Finite α m]
    {it : Iter (α := α) m β} :
    it.reverseToList = (do
      match ← it.step with
      | .yield it' out _ => return (← it'.reverseToList) ++ [out]
      | .skip it' _ => it'.reverseToList
      | .done _ => return []) := by
  simp [Iter.reverseToList]
  rw [reverseToList.go]
  refine congrArg (it.step >>= ·) ?_
  ext step
  obtain ⟨step, h⟩ := step
  cases step <;> simp [Iter.reverseToList.go.aux₂]

theorem Iter.reverse_reverseToList [Monad m] [LawfulMonad m] {_ : Iterator α m β}
    [IteratorToArray α m] [LawfulIteratorToArray α m]
    {it : Iter (α := α) m β} :
    List.reverse <$> it.reverseToList = it.toList := by
  apply Eq.symm
  induction it using Iter.induct
  rename_i it ihy ihs
  rw [reverseToList_of_step, toList_of_step, map_eq_pure_bind, bind_assoc]
  refine congrArg (_ >>= ·) ?_
  ext step
  split <;> simp (discharger := assumption) [ihy, ihs]

end Consumers

section ListIterator

variable {m : Type v → Type v} [Monad m] {β : Type v}

-- theorem List.step_iter_nil :
--     (([] : List β).iter m).step = pure ⟨.done, .done, sorry, [], sorry⟩

-- private theorem List.toArray_iter.aux {l : List β} {acc : Array β} :
--     Iter.toArray.go (l.iter m) acc = pure (acc ++ l.toArray) := by
--   simp [List.iter]
--   induction l generalizing acc with
--   | nil =>
--     rw [Iter.toArray.go]
--     simp [Iter.step, Iter.stepH, CodensityT.run, CodensityT.mapH, Iterator.step,
--       IterationT.map_eq_mapH, IterationT.mapH, IterationT.computation_pure, Pure.pure]
--     simp [Iter.Step.ofInternal, IterationT.Plausible.map, IterStep.map]
--   | cons x xs ih =>
--     rw [Iter.toArray.go]
--     simp [Iter.step, Iter.stepH, CodensityT.run, CodensityT.mapH, Iterator.step,
--       IterationT.map_eq_mapH, IterationT.mapH, IterationT.computation_pure, Pure.pure,
--       Iter.Step.ofInternal, IterationT.Plausible.map, IterStep.map, ih]

-- private theorem List.toArray_iter {l : List β} :
--     Iter.toArray (l.iter m)

end ListIterator

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

-- variable {α : Type u} {m : Type w → Type w'} {β : Type v}
--   [Iterator α m β] {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β)
--   [Monad m]
--   (f : β → CodensityT m (Option β'))

-- theorem FilterMapMH.plausible_of_yield_of_none {it' : Iter (α := α) m β} {out : β}
--     (h : it.plausible_step (.yield it' out)) :
--     (it.filterMapMH f).plausible_step (.skip (it'.filterMapMH f)) := by
--   let step : it.Step := .yield it' out h
--   let internalStep := step.toInternal
--   simp only [Iter.plausible_step]
--   refine ⟨.skip (it'.filterMapMH f).inner, by simp [IterStep.map, Iter.filterMapMH], ?_⟩
--   refine ⟨.yield (it'.filterMapMH f).inner.inner out, ?_, ?_⟩
--   · exact ⟨none, rfl, True.intro⟩
--   · simp only [Iter.filterMapMH, Iterator.filterMapMH, inner_toIter]
--     exact internalStep.property

-- theorem FilterMapMH.plausible_of_yield_of_some {it' : Iter (α := α) m β} {out : β} {out' : β'}
--     (h : it.plausible_step (.yield it' out)) :
--     (it.filterMapMH f).plausible_step (.yield (it'.filterMapMH f) out') := by
--   let step : it.Step := .yield it' out h
--   let internalStep := step.toInternal
--   refine ⟨.yield (it'.filterMapMH f).inner out', by simp [IterStep.map, Iter.filterMapMH], ?_⟩
--   refine ⟨.yield (it'.filterMapMH f).inner.inner out, ?_, ?_⟩
--   · exact ⟨some out', rfl, True.intro⟩
--   · simp only [Iter.filterMapMH, Iterator.filterMapMH, inner_toIter]
--     exact internalStep.property

-- theorem FilterMapMH.plausible_of_skip {it' : Iter (α := α) m β}
--     (h : it.plausible_step (.skip it')) :
--     (it.filterMapMH f).plausible_step (.skip (it'.filterMapMH f)) := by
--   let step : it.Step := .skip it' h
--   let internalStep := step.toInternal
--   refine ⟨.skip (it'.filterMapMH f).inner, by simp [IterStep.map, Iter.filterMapMH], ?_⟩
--   refine ⟨.skip (it'.filterMapMH f).inner.inner, rfl, ?_⟩
--   simp only [Iter.filterMapMH, Iterator.filterMapMH, inner_toIter]
--   exact internalStep.property

-- theorem FilterMapMH.plausible_of_done
--     (h : it.plausible_step .done) :
--     (it.filterMapMH f).plausible_step .done := by
--   let step : it.Step := .done h
--   let internalStep := step.toInternal
--   refine ⟨.done, by simp [IterStep.map, Iter.filterMapMH], ?_⟩
--   refine ⟨.done, rfl, ?_⟩
--   simp only [Iter.filterMapMH, Iterator.filterMapMH, inner_toIter]
--   exact internalStep.property

-- theorem filterMapMH_step :
--   (it.filterMapMH f).stepH = (it.stepH.bindH (match · with
--       | .yield it' out h => (f out).mapH fun
--           | none => .skip (it'.filterMapMH f) (FilterMapMH.plausible_of_yield_of_none _ _ h)
--           | some out' => .yield (it'.filterMapMH f) out' (FilterMapMH.plausible_of_yield_of_some _ _ h)
--       | .skip it' h => pure <| .skip (it'.filterMapMH f) (FilterMapMH.plausible_of_skip _ _ h)
--       | .done h => pure <| .done (FilterMapMH.plausible_of_done _ _ h))) := by
--   cases it
--   simp only [Iter.filterMapMH, Iterator.filterMapMH]
--   rw [Iter.stepH, CodensityT.mapH_eq_bindH]
--   rw [Iter.stepH, CodensityT.mapH_eq_bindH]
--   simp only [plausible_eq_copy
--     (congrArg Iterator.step (inner_toIter ..)),
--     congrArg Iterator.step, congrArg FilterMapMH.inner, inner_toIter]
--   simp only [Iterator.step]
--   rw [CodensityT.map_eq_mapH, CodensityT.mapH_eq_bindH]
--   simp only [IterationT.bindH]
--   simp only [CodensityT.bindH_assoc]
--   refine congrArg (CodensityT.bindH _ ·) ?_
--   ext x
--   simp only [CodensityT.bindH_pure, Iter.Step.ofInternal, IterationT.Plausible.map, IterStep.map]
--   match h : x with
--   | ⟨.yield .., h⟩ =>
--     simp only [matchStep]
--     simp only [IterationT.mapH, CodensityT.mapH_eq_bindH, monadLift, MonadLift.monadLift,
--       CodensityT.map_eq_mapH, CodensityT.mapH_eq_bindH, CodensityT.bindH_assoc,
--       CodensityT.bindH_pure]
--     refine congrArg (CodensityT.bindH _ ·) ?_
--     ext y
--     refine congrArg pure ?_
--     simp only [IterationT.Plausible.copy, Iter.Step.yield, Iter.Step.skip, Iter.filterMapMH,
--       Iterator.filterMapMH, inner_toIter]
--     cases y <;> rfl
--   | ⟨.skip .., h⟩ =>
--     simp only [matchStep]
--     simp only [CodensityT.mapH_eq_bindH, IterationT.computation_pure, CodensityT.bindH_pure,
--       IterationT.Plausible.copy, Iter.Step.skip, Iter.filterMapMH, Iterator.filterMapMH,
--       inner_toIter]
--   | ⟨.done, h⟩ =>
--     simp only [matchStep, IterationT.Plausible.copy, CodensityT.mapH_eq_bindH, CodensityT.bindH_assoc,
--       IterationT.computation_pure, CodensityT.bindH_pure]
--     rfl
