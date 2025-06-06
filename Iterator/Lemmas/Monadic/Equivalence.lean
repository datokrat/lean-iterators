/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic
import Init.Control.Lawful.Basic
import Init.Ext

structure IterM.PlausibilityMorphism (α α' : Type w) (m : Type w → Type w') {β : Type w}
    [Iterator α m β] [Iterator α' m β] where
  map : IterM (α := α) m β → IterM (α := α') m β
  plausible_step_map : ∀ {it : IterM (α := α) m β} {step : IterStep (IterM (α := α) m β) β},
      (map it).plausible_step (step.map map id) ↔ it.plausible_step step

def IterM.PlausibilityMorphism.mapStep {α α' : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α m β] [Iterator α' m β] (φ : PlausibilityMorphism α α' m)
    {it : IterM (α := α) m β} (step : it.Step) : (φ.map it).Step :=
  ⟨step.1.map φ.map id, φ.plausible_step_map.mpr step.2⟩

structure IterM.Morphism (α α' : Type w) (m : Type w → Type w') [Functor m] {β : Type w}
    [Iterator α m β] [Iterator α' m β] extends IterM.PlausibilityMorphism α α' m where
  stepH_hom : ∀ {it : IterM (α := α) m β},
      toPlausibilityMorphism.mapStep <$> it.step = (map it).step

def IterM.Morphism.id (α : Type w) (m : Type w → Type w') [Functor m] [LawfulFunctor m] {β : Type w} [Iterator α m β] :
    Morphism α α m where
  map it := it
  plausible_step_map {it step} := by
    change it.plausible_step (step.map _root_.id _root_.id) ↔ it.plausible_step step
    simp [IterStep.map_id]
  stepH_hom {it} := by
    conv => rhs; rw [← id_map (x := it.step)]
    refine congrArg (· <$> _) ?_
    ext step
    obtain ⟨step, _⟩ := step
    cases step <;> simp [PlausibilityMorphism.mapStep]

def IterM.Morphism.copy {α α' : Type w} {m : Type w → Type w'} [Functor m] {β : Type w}
    [Iterator α m β] [Iterator α' m β] (φ : Morphism α α' m) {f : IterM (α := α) m β → IterM (α := α') m β}
    (h : f = φ.map) : Morphism α α' m where
  map := f
  plausible_step_map := h ▸ φ.plausible_step_map
  stepH_hom := by cases h; exact φ.stepH_hom
