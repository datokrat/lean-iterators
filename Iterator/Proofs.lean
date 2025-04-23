import Iterator

section Equivalence

variable {α : Type u} {m : Type w → Type w'} {β : Type v}

inductive IterTStep (β : Type v) where
  | yield : β → IterTStep β
  | skip : IterTStep β
  | done : IterTStep β

inductive IterT (m : Type w → Type w') (β : Type v) : Type w → Type (max v w w' + 1) where
  | step : ∀ {α}, Nat → (β → α) → IterT m β (IterTStep α)
  | lift : ∀ {α}, m α → IterT m β α
  | bind : ∀ {α γ}, IterT m β α → (α → IterT m β γ) → IterT m β γ

def IterT.interpret [Iterator α m β] [Monad m] (it : α) (γ : Type w) (x : IterT m β γ) : m γ :=
  go [it] x |>.mapH (fun p => p.1) |>.run
where
  go {δ : Type w} (its : List α) : IterT m β δ → CodensityT m (δ × List α)
    | .step n f => match its[n]? with
      | none => pure (.done, its)
      | some it =>
        let v := Iterator.step it
        v.mapH (match · with
          | .yield it' out _ => (.yield (f out), it' :: its)
          | .skip it' _ => (.skip, it' :: its)
          | .done _ => (.done, its))
    | .lift x => (CodensityT.eval x).mapH (Prod.mk · its)
    | .bind x f => (go its x) >>= (fun y => go y.2 (f y.1))

end Equivalence

variable {α : Type u} {m : Type w → Type w'} {β : Type v}
  [Iterator α m β] {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β)
  [Monad m] [LawfulMonad m]
  (f : β → CodensityT m (Option β'))

theorem filterMapMH_step' (it : α) (f : β → IterationT m (Option β')) :
    Iterator.step (m := m) (Iterator.filterMapMH f it) =
      (Iterator.step (m := m) it |>.bindH (match · with
        | .yield it' out h => (f out).computation.mapH (fun x => ⟨match x.val with
          | none => .skip ⟨it'⟩
          | some out => .yield ⟨it'⟩ out, .yield it' out, ⟨x.1, rfl, x.2⟩, h⟩)
        | .skip it' h => pure ⟨.skip ⟨it'⟩, .skip it', rfl, h⟩
        | .done h => pure ⟨.done, .done, rfl, h⟩)) := by
  simp [Iterator.filterMapMH, Iterator.step, SimpleIterator.step, computation_matchStepH,
    IterationT.step, IterationT.mapH, CodensityT.mapH_mapH, IterationT.computation_pure]
  refine congrArg (CodensityT.bindH _) ?_
  ext x
  split
  · simp
    refine congrArg (CodensityT.mapH · _) ?_
    ext y
    cases y
    dsimp only
    split <;> rfl
  · simp

theorem filterMapMH_step :
  (it.filterMapMH f).stepH = (it.stepH.bindH (match · with
      | .yield it' out h => (f out).mapH fun
          | none => .skip (it'.filterMapMH f) ⟨sorry, sorry⟩
          | _ => sorry
      | .skip it' h => pure <| .skip (it'.filterMapMH f) sorry
      | .done h => pure <| .done sorry)) := by
  simp [Iter.filterMapMH, Iter.stepH]
  simp [toIter, Iter.inner]
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
