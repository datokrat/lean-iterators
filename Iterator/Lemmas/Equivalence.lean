import Iterator.Basic

structure Iter.PlausibilityMorphism (α α' : Type w) (m : Type w → Type w') {β : Type v}
    [Iterator α m β] [Iterator α' m β] where
  map : Iter (α := α) m β → Iter (α := α') m β
  plausible_step_map : ∀ {it : Iter (α := α) m β} {step : IterStep (Iter (α := α) m β) β},
      (map it).plausible_step (step.map map id) ↔ it.plausible_step step

def Iter.PlausibilityMorphism.mapStep {α α' : Type w} {m : Type w → Type w'} {β : Type v}
    [Iterator α m β] [Iterator α' m β] (φ : PlausibilityMorphism α α' m)
    {it : Iter (α := α) m β} (step : it.Step) : (φ.map it).Step :=
  ⟨step.1.map φ.map id, φ.plausible_step_map.mpr step.2⟩

structure Iter.Morphism (α α' : Type w) (m : Type w → Type w') [Functor m] {β : Type v}
    [Iterator α m β] [Iterator α' m β] extends Iter.PlausibilityMorphism α α' m where
  stepH_hom : ∀ {it : Iter (α := α) m β},
      (.deflate <| toPlausibilityMorphism.mapStep ·.inflate) <$> it.stepH = (map it).stepH

def Iter.Morphism.id (α : Type w) (m : Type w → Type w') [Functor m] [LawfulFunctor m] {β : Type v} [Iterator α m β] :
    Morphism α α m where
  map it := it
  plausible_step_map {it step} := by
    change it.plausible_step (step.map _root_.id _root_.id) ↔ it.plausible_step step
    simp [IterStep.map_id]
  stepH_hom {it} := by
    simp only [PlausibilityMorphism.mapStep]
    conv => rhs; rw [← id_map (x := it.stepH)]
    refine congrArg (· <$> _) ?_
    ext step
    conv => rhs; rw [← USquash.deflate_inflate (x := step)]
    refine congrArg USquash.deflate ?_
    generalize step.inflate = step
    obtain ⟨step, _⟩ := step
    cases step <;> simp
