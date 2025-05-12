import Iterator.Combinators.FilterMap
import Iterator.Lemmas.Consumer

theorem Iterator.step_hcongr {α : Type w} {m : Type w → Type w'} {β : Type v} [Iterator α m β]
    {it₁  it₂ : IterM (α := α) m β} (h : it₁ = it₂) : Iterator.step (m := m) it₁ = h ▸ Iterator.step (m := m) it₂ := by
  cases h; rfl

theorem Iterator.bind_hcongr {α : Type w} {m : Type w → Type w'} [Bind m] {β : Type v}
    [Iterator α m β] {it it' : IterM (α := α) m β}
    {γ}
    {x : m (USquash it.Step)}
    {x' : m (USquash it.Step)}
    {f : (USquash it.Step) → m γ}
    {f' : (USquash it.Step) → m γ}
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

theorem Iterator.bind_hcongr'{α : Type w} {m : Type w → Type w'} [Bind m] {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} {γ}
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

variable {α : Type w} {m : Type w → Type w'} {β : Type v} {β' : Type v'}
  [Iterator α m β] (it : IterM (α := α) m β) [Monad m]
  (f : β → HetT m (Option β'))

-- @[simp]
-- theorem plausible_step_filterMapMH :
--     (it.filterMapMH f).inner.inner = it.inner := by
--   simp [IterM.filterMapMH, Iterator.filterMapMH]

theorem filterMapMH_stepH [LawfulMonad m] :
  (it.filterMapMH f).stepH = (do
    match (← it.stepH).inflate with
    | .yield it' out h => do
      match (← (f out).computation).inflate (small := _) with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterMapMH f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.filterMapMH f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapMH f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  generalize step.inflate = step
  match step with
  | .yield it' out h => rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem filterMapH_stepH [LawfulMonad m] {f : β → Option β'} :
  (it.filterMapH f).stepH = (do
    match (← it.stepH).inflate with
    | .yield it' out h => do
      match h' : f out with
      | none =>
        pure <| .deflate <| .skip (it'.filterMapH f) (.yieldNone h h')
      | some out' =>
        pure <| .deflate <| .yield (it'.filterMapH f) out' (.yieldSome h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapH f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  simp only [IterM.filterMapH, filterMapMH_stepH, pure]
  apply bind_congr
  intro step
  generalize step.inflate = step
  split
  · simp only [pure_bind, USquash.inflate_deflate]
    split <;> split <;> simp_all
  · simp
  · simp

theorem mapMH_stepH [LawfulMonad m] {f : β → HetT m β'} :
  (it.mapMH f).stepH = (do
    match (← it.stepH).inflate with
    | .yield it' out h => do
      let out' := (← (f out).computation).inflate (small := _)
      pure <| .deflate <| .yield (it'.mapMH f) out'.1 (.yieldSome h ⟨out', rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapMH f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  change (it.filterMapMH _).stepH = _
  rw [filterMapMH_stepH]
  apply bind_congr
  intro step
  generalize step.inflate = step
  split
  · simp only [HetT.computation_mapH, bind_map_left, USquash.inflate_deflate, bind_pure_comp]
    rfl
  · rfl
  · rfl

end StepH

section Step

variable {α : Type w} {m : Type w → Type w'} {β : Type v} {β' : Type w}
  [Iterator α m β] (it : IterM (α := α) m β) [Monad m]
  (f : β → m (USquash <| Option β'))

theorem filterMapH_step [LawfulMonad m] {f : β → Option β'} :
  (it.filterMapH f).step = (do
    match (← it.stepH).inflate with
    | .yield it' out h => do
      match h' : f out with
      | none =>
        pure <| .skip (it'.filterMapH f) (.yieldNone (out := out) h h')
      | some out' =>
        pure <| .yield (it'.filterMapH f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .skip (it'.filterMapH f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  simp only [IterM.step, filterMapH_stepH, map_eq_pure_bind, bind_assoc]
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

variable {α : Type w} {m : Type w → Type w'} {β : Type v} {γ : Type v'} [Small.{w} γ]
    [Monad m] [Iterator α m β] {p : Option γ → Prop} {f : β → m (USquash <| Subtype p)}

instance {f : β → HetT m γ} [LawfulMonad m] [IteratorToArray α m]
    [LawfulIteratorToArray α m] [Finite α m] :
    LawfulIteratorToArray (MapMH α f) m where
  finite := inferInstance
  lawful := by
    intro γ
    ext f it
    have : it = it.inner.inner.mapMH _ := rfl
    generalize it.inner.inner = it at *
    cases this
    simp only [IteratorToArray.toArrayMapped]
    rw [LawfulIteratorToArray.lawful]
    induction it using IterM.induct with | step it ih_yield ih_skip =>
    rw [IterM.DefaultConsumers.toArrayMapped_of_stepH]
    rw [IterM.DefaultConsumers.toArrayMapped_of_stepH]
    simp only [mapMH_stepH, bind_assoc]
    apply bind_congr
    intro step
    generalize step.inflate = step
    split
    · simp only [bind_pure_comp, bind_map_left, USquash.inflate_deflate, ← ih_yield ‹_›]
      rfl
    · simp only [bind_pure_comp, pure_bind, USquash.inflate_deflate, ← ih_skip ‹_›]
      rfl
    · simp

end Lawful

section Congruence

def IterM.Morphisms.filterMapMHCongrRight {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type v} [Iterator α m β]
    {γ : Type v'} {f g : β → HetT m (Option γ)} (h : f = g) :
    Morphism (FilterMapMH α f) (FilterMapMH α g) m := by
  exact h ▸ Morphism.id _ m

-- TODO: upstream from Mathlib.Logic.Basic? Note that this lemma is more general
theorem Eq.rec_eq_cast {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _} (x : motive a rfl) {a' : α} (h : a = a') :
    (Eq.rec x h : motive a' h) = cast (by cases h; rfl) x := by
  cases h; rfl

-- TODO: upstream from Mathlib.Logic.Basic?
theorem eq_cast_iff_heq : a = cast e b ↔ HEq a b := by cases e; simp

def IterM.Morphisms.mapHToFilterMapH (α : Type w) (m : Type w → Type w') [Monad m] [LawfulMonad m]
    {β : Type v} [Iterator α m β]
    {γ : Type v'} (f : β → γ) :
    Morphism (β := γ) (MapMH α (fun x => (pure (f x) : HetT m _)))
      (FilterMapMH α (fun x => (pure (some (f x)) : HetT m _)) (γ := γ)) m := by
  apply IterM.Morphism.copy
  case f => exact fun it => it.inner.inner.filterMapMH _
  case φ => exact filterMapMHCongrRight (α := α) (m := m) (by simp)
  case h =>
    ext it
    simp only [filterMapMHCongrRight, Eq.apply_rec _ fun (a : _) (ψ : Morphism _ _ m) => ψ.map it,
      Morphism.id]
    rw [Eq.rec_eq_cast, eq_cast_iff_heq]
    rw (occs := [2]) [(rfl : it = it.inner.inner.filterMapMH _)]
    apply HEq.congrArg (fun f => it.inner.inner.filterMapMH f)
    simp

end Congruence

section ToList

variable {α : Type w} {m : Type w → Type w'} {β : Type v} {β' : Type w}
  [Iterator α m β] (it : IterM (α := α) m β) [Monad m]

theorem toList_filterMapH {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    [Iterator α m β] [IteratorToArray α m] [LawfulIteratorToArray α m] {f : β → Option β'}
    (it : IterM (α := α) m β) :
    (it.filterMapH f).toList = (fun x => x.filterMap f) <$> it.toList := by
  induction it using IterM.induct
  rename_i it ihy ihs
  rw [IterM.toList_of_step, IterM.toList_of_step]
  simp
  rw [filterMapH_step]
  simp only [bind_assoc, IterM.step, map_eq_pure_bind]
  apply bind_congr
  intro step
  generalize step.inflate = step
  simp only [pure_bind]
  split
  · simp only [List.filterMap_cons, bind_assoc, pure_bind, bind_pure]
    split
    · split
      · simp only [bind_pure_comp, pure_bind]
        exact ihy ‹_›
      · simp_all
    · split
      · simp_all
      · simp_all [ihy ‹_›]
  · simp
    apply ihs
    assumption
  · simp

theorem toList_mapH {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    [Iterator α m β] [IteratorToArray α m] [LawfulIteratorToArray α m] {f : β → β'}
    (it : IterM (α := α) m β) :
    (it.mapH f).toList = (fun x => x.map f) <$> it.toList := by
  rw [(IterM.Morphisms.mapHToFilterMapH α m f).toList_eq]
  change (it.filterMapH _).toList = _
  rw [toList_filterMapH]
  change (fun x => x.filterMap (some ∘ f)) <$> it.toList = _
  rw [List.filterMap_eq_map]

end ToList
