import Iterator.Combinators.FilterMap
import Iterator.Lemmas.Consumer

section IterStep

@[simp]
theorem IterStep.map_done {f : α → α'} {g : β → β'} :
  (.done : IterStep α β).map f g = .done := rfl

@[simp]
theorem IterStep.map_skip {f : α → α'} {g : β → β'} :
  (.skip it : IterStep α β).map f g = .skip (f it) := rfl

@[simp]
theorem IterStep.map_yield {f : α → α'} {g : β → β'} :
  (.yield it out : IterStep α β).map f g = .yield (f it) (g out) := rfl

end IterStep

theorem Iter.plausible_step_iff {α : Type u} {m : Type w → Type w'} {β : Type v}
    [Iterator α m β] {it : Iter (α := α) m β} {step} :
    it.plausible_step step ↔ Iterator.plausible_step m it.inner (step.map Iter.inner id) := by
  simp [Iter.plausible_step]

theorem Iterator.step_hcongr {α : Type u} {m : Type w → Type w'} {β : Type v} [Iterator α m β]
    {it₁  it₂ : α} (h : it₁ = it₂) : Iterator.step (m := m) it₁ = h ▸ Iterator.step (m := m) it₂ := by
  cases h; rfl

theorem Iterator.bind_hcongr {α : Type u} {m : Type w → Type w'} [Bind m] {β : Type v} [Iterator α m β] {it it' : α}
    {γ}
    {x : m (USquash (PlausibleIterStep (Iterator.plausible_step m it)))}
    {x' : m (USquash (PlausibleIterStep (Iterator.plausible_step m it')))}
    {f : (USquash (PlausibleIterStep (Iterator.plausible_step m it))) → m γ}
    {f' : (USquash (PlausibleIterStep (Iterator.plausible_step m it'))) → m γ}
    (h : it = it') (h' : x = h ▸ x') (h'' : ∀ s hs, (f (.deflate ⟨s, hs⟩)) = (f' (.deflate ⟨s, h ▸ hs⟩))) :
    x >>= f = x' >>= f' := by
  cases h
  dsimp only at h'
  rw [h']
  apply bind_congr
  intro step
  rw [← USquash.deflate_inflate (x := step)]
  generalize step.inflate = step
  cases step with
  | mk step h => exact h'' step h

theorem Iterator.bind_hcongr' {α : Type u} {m : Type w → Type w'} [Bind m] {β : Type w} [Iterator α m β]
    {it it' : Iter (α := α) m β} {γ}
    {x : m it.Step}
    {f : it.Step → m γ}
    (h : it = it') :
    x >>= f = (h ▸ x : m it'.Step) >>= (fun step => f ⟨step.1, h ▸ step.2⟩) := by
  cases h
  dsimp only
  apply bind_congr
  intro a
  rfl

section StepH

variable {α : Type u} {m : Type w → Type w'} {β : Type v} {β' : Type v'} [Small.{w} β']
  [Iterator α m β] (it : Iter (α := α) m β) [Monad m]
  (f : β → m (USquash <| Option β'))

@[simp]
theorem plausible_step_filterMapMH :
    (it.filterMapMH f).inner.inner = it.inner := by
  simp [Iter.filterMapMH, Iterator.filterMapMH]

theorem filterMapMH_stepH [LawfulMonad m] :
  (it.filterMapMH f).stepH = (do
    match (← it.stepH).inflate with
    | .yield it' out h => do
      match (← f out).inflate with
      | none =>
        pure <| .deflate <| .skip (it'.filterMapMH f)
              (.yieldNone (out := out) (by simp_all [Iter.plausible_step_iff]) True.intro)
      | some out' =>
        pure <| .deflate <| .yield (it'.filterMapMH f) out'
              (.yieldSome (out := out) (by simp_all [Iter.plausible_step_iff]) True.intro)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapMH f)
            (.skip (by simp_all [Iter.plausible_step_iff, plausible_step_filterMapMH]))
    | .done h =>
      pure <| .deflate <| .done
            (.done (by simp_all [Iter.plausible_step_iff, plausible_step_filterMapMH]))) := by
  simp [Iter.stepH, Iterator.step]
  unfold plausible_step_filterMapMH Iter.Step.ofInternal
  refine Iterator.bind_hcongr ?_ ?_ ?_
  · simp
  · exact Iterator.step_hcongr (plausible_step_filterMapMH it f)
  · intro s hs
    simp only [IterStep.map, id_eq, USquash.inflate_deflate]
    match s with
    | .yield it' out =>
      simp only [map_bind]
      refine congrArg (_ >>= ·) ?_
      ext fout
      generalize fout.inflate = fout
      match fout with
      | none => simp [Iter.Step.skip, Iter.filterMapMH, Iterator.filterMapMH]
      | some _ => simp [Iter.Step.yield, Iter.filterMapMH, Iterator.filterMapMH]
    | .skip .. => simp [Iter.Step.skip, Iter.filterMapMH, Iterator.filterMapMH]
    | .done .. => simp [Iter.Step.done]

theorem filterMapH_stepH [LawfulMonad m] {f : β → Option β'} :
  (it.filterMapH f).stepH = (do
    match (← it.stepH).inflate with
    | .yield it' out h => do
      match (f out) with
      | none =>
        pure <| .deflate <| .skip (it'.filterMapH f)
              (.yieldNone (out := out) (by simp_all [Iter.plausible_step_iff, Iter.filterMapH]) True.intro)
      | some out' =>
        pure <| .deflate <| .yield (it'.filterMapH f) out'
              (.yieldSome (out := out) (by simp_all [Iter.plausible_step_iff, Iter.filterMapH]) True.intro)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapH f)
            (.skip (by simp_all [Iter.plausible_step_iff, plausible_step_filterMapMH, Iter.filterMapH]))
    | .done h =>
      pure <| .deflate <| .done
            (.done (by simp_all [Iter.plausible_step_iff, plausible_step_filterMapMH, Iter.filterMapH]))) := by
  simp only [Iter.filterMapH, filterMapMH_stepH]
  refine congrArg (_ >>= ·) ?_
  ext
  split <;> simp

end StepH

section Step

variable {α : Type u} {m : Type w → Type w'} {β : Type v} {β' : Type w}
  [Iterator α m β] (it : Iter (α := α) m β) [Monad m]
  (f : β → m (USquash <| Option β'))

theorem filterMapH_step [LawfulMonad m] {f : β → Option β'} :
  (it.filterMapH f).step = (do
    match (← it.stepH).inflate with
    | .yield it' out h => do
      match (f out) with
      | none =>
        pure <| .skip (it'.filterMapH f)
              (.yieldNone (out := out) (by simp_all [Iter.plausible_step_iff, Iter.filterMapH]) True.intro)
      | some out' =>
        pure <| .yield (it'.filterMapH f) out'
              (.yieldSome (out := out) (by simp_all [Iter.plausible_step_iff, Iter.filterMapH]) True.intro)
    | .skip it' h =>
      pure <| .skip (it'.filterMapH f)
            (.skip (by simp_all [Iter.plausible_step_iff, plausible_step_filterMapMH, Iter.filterMapH]))
    | .done h =>
      pure <| .done
            (.done (by simp_all [Iter.plausible_step_iff, plausible_step_filterMapMH, Iter.filterMapH]))) := by
  simp only [Iter.step, filterMapH_stepH, map_eq_pure_bind, bind_assoc]
  refine congrArg (_ >>= ·) ?_
  ext step
  simp only [Function.comp_apply, bind_pure_comp]
  generalize step.inflate = step
  split
  · split <;> simp
  · simp
  · simp

end Step

section Lawful

variable {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type v'} [Small.{w} γ]
    [Monad m] [Iterator α m β] {p : Option γ → Prop} {f : β → m (USquash <| Subtype p)}

instance {p : γ → Prop} {f : β → m (USquash <| Subtype p)} [LawfulMonad m] [IteratorToArray α m]
    [LawfulIteratorToArray α m] [Finite α m] :
    LawfulIteratorToArray (MapMH α f) m where
  finite := inferInstance
  lawful := by
    intro γ
    ext f it
    let y := toIter m it.inner.inner
    have : it = y.mapH sorry := sorry -- oof
    simp only [IteratorToArray.toArrayMapped]
    rw [LawfulIteratorToArray.lawful]
    induction it using Iter.induct with | step it ih_yield ih_skip =>
    rw [Iter.DefaultConsumers.toArrayMapped_of_stepH]
    rw [Iter.DefaultConsumers.toArrayMapped_of_stepH]



end Lawful

section ToList

variable {α : Type w} {m : Type w → Type w'} {β : Type v} {β' : Type w}
  [Iterator α m β] (it : Iter (α := α) m β) [Monad m]

theorem toList_filterMapMH {α : Type u} {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    {_ : Iterator α m β} [IteratorToArray α m] [LawfulIteratorToArray α m] {f : β → Option β'}
    (it : Iter (α := α) m β) :
    (it.filterMapH f).toList = (fun x => x.filterMap f) <$> it.toList := by
  induction it using Iter.induct
  rename_i it ihy ihs
  rw [Iter.toList_of_step, Iter.toList_of_step]
  simp
  rw [filterMapH_step]
  simp only [bind_assoc, Iter.step, map_eq_pure_bind]
  apply bind_congr
  intro step
  generalize step.inflate = step
  simp only [pure_bind]
  split
  · simp only [List.filterMap_cons, bind_assoc, pure_bind, bind_pure]
    cases f _
    · simp only [Function.comp_apply, bind_pure_comp, pure_bind]
      apply ihy
      assumption
    · simp only [Function.comp_apply, bind_pure_comp, pure_bind]
      rw [ihy]
      · simp
      · assumption
  · simp
    apply ihs
    assumption
  · simp

end ToList
