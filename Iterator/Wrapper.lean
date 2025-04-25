/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Option.Lemmas
import Iterator.Basic
import Iterator.Cont

variable {α : Type u} {m : Type w → Type w'} {β : Type v}

structure Iter {α : Type u} (m : Type w → Type w') (β : Type v)
    [Iterator α m β] [small : ComputableSmall.{w} α] : Type w where
  innerLifted : ComputableSmall.Lift α

variable (m) in
@[always_inline, inline]
def toIter [Iterator α m β] [ComputableSmall.{w} α] (it : α) : Iter (α := α) m β :=
  ⟨ComputableSmall.up it⟩

@[always_inline, inline]
def Iter.inner {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) : α :=
  ComputableSmall.down it.innerLifted

@[simp]
theorem inner_toIter {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : α) :
    (toIter m it).inner = it :=
  ComputableSmall.down_up

def Iterator.stepLift [Iterator α m β] [ComputableSmall.{w} α] [ComputableSmall.{w} β] (it : α) :
    IterationT m (IterStep (ComputableSmall.Lift α) (ComputableSmall.Lift β)) :=
  Iterator.step (m := m) it |>.mapH (·.map ComputableSmall.up ComputableSmall.up)

def Iterator.stepLiftState [Iterator α m β] [ComputableSmall.{w} α] (it : α) :
    IterationT m (IterStep (ComputableSmall.Lift α) β) :=
  Iterator.step (m := m) it |>.mapH (·.map ComputableSmall.up id)

def Iter.plausible_step {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β)
    (step : IterStep (Iter (α := α) m β) β) : Prop :=
  Iterator.step (m := m) it.inner |>.mapH (·.map (toIter m) id) |>.property step

def Iter.Step {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) :=
  { step : IterStep (Iter (α := α) m β) β // it.plausible_step step }
  -- Iterator.step (m := m) it.inner |>.mapH (·.map (toIter m) id) |>.Plausible

def Iter.Step.toPlausible {_ : Iterator α m β} {_ : ComputableSmall.{w} α} {it : Iter (α := α) m β}
    (step : Iter.Step it) :
    Iterator.step (m := m) it.inner |>.mapH (·.map (toIter m) id) |>.Plausible :=
  step

@[match_pattern]
def Iter.Step.yield {_ : Iterator α m β} {_ : ComputableSmall.{w} α}
   {it : Iter (α := α) m β} (it' b h) := (⟨.yield it' b, h⟩ : it.Step)

@[match_pattern]
def Iter.Step.skip {_ : Iterator α m β} {_ : ComputableSmall.{w} α}
   {it : Iter (α := α) m β} (it' h) := (⟨.skip it', h⟩ : it.Step)

@[match_pattern]
def Iter.Step.done {_ : Iterator α m β} {_ : ComputableSmall.{w} α}
   {it : Iter (α := α) m β} (h) := (⟨.done, h⟩ : it.Step)

-- inductive Iter.Step {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) where
-- | yield : (it' : Iter (α := α) m β) → (b : β) → Iterator.yielded m it.inner it'.inner b → it.Step
-- | skip : (it' : Iter (α := α) m β) → Iterator.skipped m it.inner it'.inner → it.Step
-- | done : Iterator.done m it.inner → it.Step

def Iter.LiftedStep {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β]
   (it : Iter (α := α) m β) : Type w :=
  Iterator.step (m := m) it.inner |>.mapH (·.map (fun x => toIter m x) ComputableSmall.up) |>.Plausible

@[match_pattern]
def Iter.LiftedStep.yield {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β]
   {it : Iter (α := α) m β} (it' b h) := (⟨.yield it' b, h⟩ : it.LiftedStep)

@[match_pattern]
def Iter.LiftedStep.skip {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β]
   {it : Iter (α := α) m β} (it' h) := (⟨.skip it', h⟩ : it.LiftedStep)

@[match_pattern]
def Iter.LiftedStep.done {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β]
   {it : Iter (α := α) m β} (h) := (⟨.done, h⟩ : it.LiftedStep)

-- inductive Iter.LiftedStep {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β]
--     (it : Iter (α := α) m β) where
-- | yield : (it' : Iter (α := α) m β) → (b : ComputableSmall.Lift.{w} β) → Iterator.yielded m it.inner it'.inner (ComputableSmall.down b) → it.LiftedStep
-- | skip : (it' : Iter (α := α) m β) → Iterator.skipped m it.inner it'.inner → it.LiftedStep
-- | done : Iterator.done m it.inner → it.LiftedStep

@[always_inline, inline]
def Iter.Step.lift {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β]
    (it : Iter (α := α) m β) (step : it.Step) : it.LiftedStep := by
  refine step.toPlausible.map (fun s => s.map id ComputableSmall.up) |>.copy ?_
  simp [Iterator.stepLift, Iterator.stepLiftState, IterationT.mapH_mapH, IterStep.map_map]

@[always_inline, inline]
def Iter.Step.ofInternal {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) (step : Iterator.step (m := m) it.inner |>.Plausible) :
    it.Step := by
  exact step.map _

@[always_inline, inline]
def Iter.Step.toInternal {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) (step : it.Step) :
    Iterator.step (m := m) it.inner |>.Plausible := by
  refine step.toPlausible.map (fun s => s.map Iter.inner id) |>.copy ?_
  simp only [IterationT.mapH_mapH, inner_toIter, IterStep.map_map, id_eq, IterStep.map_id', IterationT.mapH_id']

-- instance {m} [Functor m] [Iterator α m β] : Iterator (Iter (α := α) m β) m β where
--   yielded it it' b := Iterator.yielded m it.inner it'.inner b
--   skipped it it' := Iterator.skipped m it.inner it'.inner
--   finished it := Iterator.finished m it.inner
--   step it := Iterator.step it.inner
--   decode it step := match Iterator.decode it.inner step with
--     | .yield it' x h => .yield ⟨it'⟩ x h
--     | .skip it' h => .skip ⟨it'⟩ h
--     | .done h => .done h

-- instance [Functor m] [Iterator α m β] [Finite α m] : Finite (Iter (α := α) m β) m where
--   wf := InvImage.wf (finiteIteratorWF ∘ Iter.inner ∘ FiniteIteratorWF.inner) Finite.wf

-- instance [Functor m] [Iterator α m β] [Productive α m] : Productive (Iter (α := α) m β) m where
--   wf := InvImage.wf (productiveIteratorWF ∘ Iter.inner ∘ ProductiveIteratorWF.inner) Productive.wf

@[always_inline, inline]
def Iter.stepH [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) :
    CodensityT m it.Step :=
  Iterator.step it.inner |>.computation |>.mapH (Iter.Step.ofInternal it)

@[always_inline, inline]
def Iter.step {β : Type w} [Monad m] {_ : Iterator α m β} {_ : ComputableSmall.{w} α} (it : Iter (α := α) m β) :
    m (Iter.Step it) :=
  it.stepH.run

section Finite

structure Iter.FiniteWFRel (α : Type u) (m : Type w → Type w') [Iterator α m β] where
  inner : α

@[always_inline, inline]
def Iter.terminationByFinite {_ : Iterator α m β} {_ : ComputableSmall.{w} α} [Finite α m] (it : Iter (α := α) m β) :
    Iter.FiniteWFRel α m :=
  ⟨it.inner⟩

def Iter.FiniteWFRel.rel [Iterator α m β] [Finite α m] : FiniteWFRel α m → FiniteWFRel α m → Prop :=
  InvImage (Iterator.successor_of m) Iter.FiniteWFRel.inner

instance [Iterator α m β] [Finite α m] : WellFoundedRelation (Iter.FiniteWFRel α m) where
  rel := Iter.FiniteWFRel.rel
  wf := InvImage.wf _ Finite.wf

private theorem Option.elim_elim {α : Type u} {β : Type v} {γ : Type w} (o : Option α)
    {d₁ : Option β} {f₁ : α → Option β} {d₂ : γ} {f₂ : β → γ} :
    (o.elim d₁ f₁).elim d₂ f₂ = o.elim (d₁.elim d₂ f₂) (f₁ . |>.elim d₂ f₂) := by
  cases o <;> rfl

private theorem Option.elim_id {α : Type u} (o : Option α) :
    o.elim none (some ·) = o := by
  cases o <;> rfl

def Iter.FiniteWFRel.of_step_yield {α m β} {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{w} α}
    {it' it : Iter (α := α) m β} {out : β} (h : (Iterator.step (m := m) it.inner).mapH (·.map (toIter m) id) |>.property (.yield it' out)) : Iter.FiniteWFRel.rel it'.terminationByFinite it.terminationByFinite := by
  simp_wf
  simp [Iter.FiniteWFRel.rel, Iterator.successor_of]
  refine ⟨.yield it'.inner out, rfl, ?_⟩
  have h' : (Iterator.step (m := m) it.inner).mapH (·.map (toIter m) id) |>.mapH (·.map Iter.inner id) |>.property (.yield it'.inner out) :=
    ⟨_, rfl, h⟩
  simpa only [IterationT.mapH_mapH, IterStep.map_map, inner_toIter, id_eq, IterStep.map_id', IterationT.mapH_id'] using h'

def Iter.FiniteWFRel.of_step_skip {α m β} {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{w} α}
    {it' it : Iter (α := α) m β} (h : (Iterator.step (m := m) it.inner).mapH (·.map (toIter m) id) |>.property (.skip it')) : Iter.FiniteWFRel.rel it'.terminationByFinite it.terminationByFinite := by
  simp_wf
  simp [Iter.FiniteWFRel.rel, Iterator.successor_of]
  refine ⟨.skip it'.inner, rfl, ?_⟩
  have h' : (Iterator.step (m := m) it.inner).mapH (·.map (toIter m) id) |>.mapH (·.map Iter.inner id) |>.property (.skip it'.inner) :=
    ⟨_, rfl, h⟩
  simpa only [IterationT.mapH_mapH, IterStep.map_map, inner_toIter, id_eq, IterStep.map_id', IterationT.mapH_id'] using h'

def Iter.FiniteWFRel.of_stepH_yield {α m β} {_ : Iterator α m β} [Finite α m]
    {_ : ComputableSmall.{w} α} {_ : ComputableSmall.{w} β}
    {it' it : Iter (α := α) m β} {out : ComputableSmall.Lift β}
    (h : (Iterator.step (m := m) it.inner).mapH (·.map (toIter m) ComputableSmall.up) |>.property (.yield it' out)) :
    Iter.FiniteWFRel.rel it'.terminationByFinite it.terminationByFinite := by
  apply Iter.FiniteWFRel.of_step_yield
  simpa [IterationT.mapH_mapH, IterStep.map_map, ComputableSmall.down_up] using
    IterationT.property_mapH (·.map id ComputableSmall.down) h

def Iter.FiniteWFRel.of_stepH_skip {α m β} {_ : Iterator α m β} [Finite α m]
    {_ : ComputableSmall.{w} α} {_ : ComputableSmall.{w} β}
    {it' it : Iter (α := α) m β}
    (h : (Iterator.step (m := m) it.inner).mapH (·.map (toIter m) ComputableSmall.up) |>.property (.skip it')) :
    Iter.FiniteWFRel.rel it'.terminationByFinite it.terminationByFinite := by
  apply Iter.FiniteWFRel.of_step_skip
  simpa [IterationT.mapH_mapH, IterStep.map_map, ComputableSmall.down_up] using
    IterationT.property_mapH (·.map id ComputableSmall.down) h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact Iter.FiniteWFRel.of_step_yield ‹_›
  | exact Iter.FiniteWFRel.of_step_skip ‹_›
  | exact Iter.FiniteWFRel.of_stepH_yield ‹_›
  | exact Iter.FiniteWFRel.of_stepH_skip ‹_›)

end Finite

-- section Productive

-- structure ProductiveIteratorWF (α m) [Iterator α m β] where
--   inner : α

-- def productiveIteratorWF {α m β} [Iterator α m β] (it : α) : ProductiveIteratorWF α m :=
--   ⟨it⟩

-- instance {m} [Iterator α m β] [Productive α m] : WellFoundedRelation (ProductiveIteratorWF α m) where
--   rel := ProductiveIteratorWF.lt
--   wf := Productive.wf

-- theorem ProductiveIteratorWF.subrelation_finiteIteratorWF {α m β} [Iterator α m β] :
--     Subrelation (α := ProductiveIteratorWF α m)
--       ProductiveIteratorWF.lt
--       (InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m) ∘ inner)) :=
--   fun h => FiniteIteratorWF.lt_of_skip h

-- instance {m} [Iterator α m β] [Finite α m] : Productive α m where
--   wf := ProductiveIteratorWF.subrelation_finiteIteratorWF.wf (InvImage.wf _ Finite.wf)

-- end Productive
