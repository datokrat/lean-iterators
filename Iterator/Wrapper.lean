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
    [i : Iterator α m β] : Type w where
  innerLifted : USquash.{w} (small := i.state_small) α

variable (m) in
@[always_inline, inline]
def toIter [Iterator α m β] (it : α) : Iter (α := α) m β :=
  ⟨USquash.deflate (small := _) it⟩

@[always_inline, inline]
def Iter.inner {_ : Iterator α m β} (it : Iter (α := α) m β) : α :=
  USquash.inflate (small := _) it.innerLifted

@[simp]
theorem inner_toIter {_ : Iterator α m β} (it : α) :
    (toIter m it).inner = it :=
  USquash.inflate_deflate

def Iter.plausible_step {_ : Iterator α m β} (it : Iter (α := α) m β)
    (step : IterStep (Iter (α := α) m β) β) : Prop :=
  Iterator.plausible_step m it.inner (step.map Iter.inner id)

def Iter.Step {_ : Iterator α m β} (it : Iter (α := α) m β) :=
  { step : IterStep (Iter (α := α) m β) β // it.plausible_step step }

@[match_pattern]
def Iter.Step.yield {_ : Iterator α m β} {it : Iter (α := α) m β} (it' b h) :=
  (⟨.yield it' b, h⟩ : it.Step)

@[match_pattern]
def Iter.Step.skip {_ : Iterator α m β} {it : Iter (α := α) m β} (it' h) :=
  (⟨.skip it', h⟩ : it.Step)

@[match_pattern]
def Iter.Step.done {_ : Iterator α m β} {it : Iter (α := α) m β} (h) :=
  (⟨.done, h⟩ : it.Step)

instance {_ : Iterator α m β} :
    Small.{w} (IterStep (Iter (α := α) m β) β) :=
  haveI : Small.{w} β := Iterator.value_small α m
  inferInstance

instance {_ : Iterator α m β} {it : Iter (α := α) m β} :
    Small.{w} it.Step where
  h := ⟨{
    Target := { step : USquash.{w} (IterStep (Iter (α := α) m β) β) // it.plausible_step step.inflate }
    deflate x := ⟨.deflate (small := _) x.1, by simp [x.2]⟩
    inflate x := ⟨x.1.inflate, x.2⟩
    deflate_inflate := by simp
    inflate_deflate {x} := by cases x; simp
  }⟩

set_option pp.universes true in
def Iter.LiftedStep {_ : Iterator α m β} (it : Iter (α := α) m β) : Type w :=
  { step : IterStep (Iter (α := α) m β) (USquash.{w} (small := Iterator.value_small α m)) //
    it.plausible_step (step.map id (USquash.inflate (small := _))) }

@[match_pattern]
def Iter.LiftedStep.yield {_ : Iterator α m β}
   {it : Iter (α := α) m β} (it' b h) := (⟨.yield it' b, h⟩ : it.LiftedStep)

@[match_pattern]
def Iter.LiftedStep.skip {_ : Iterator α m β}
   {it : Iter (α := α) m β} (it' h) := (⟨.skip it', h⟩ : it.LiftedStep)

@[match_pattern]
def Iter.LiftedStep.done {_ : Iterator α m β}
   {it : Iter (α := α) m β} (h) := (⟨.done, h⟩ : it.LiftedStep)

@[always_inline, inline]
def Iter.Step.lift {_ : Iterator α m β} (it : Iter (α := α) m β) (step : it.Step) : it.LiftedStep :=
  ⟨step.val.map id (USquash.deflate (small := _)),
   by simp [IterStep.map_map, IterStep.map_id', step.property]⟩

@[always_inline, inline]
def Iter.Step.ofInternal {_ : Iterator α m β} (it : Iter (α := α) m β) (step : PlausibleIterStep (Iterator.plausible_step m it.inner)) :
    it.Step :=
  ⟨step.1.map (toIter m) id, by simp [Iter.plausible_step, IterStep.map_map, IterStep.map_id', step.2]⟩

@[always_inline, inline]
def Iter.Step.toInternal {_ : Iterator α m β} (it : Iter (α := α) m β) (step : it.Step) :
    PlausibleIterStep (Iterator.plausible_step m it.inner) :=
  ⟨step.1.map Iter.inner id, step.2⟩

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
def Iter.stepH [Monad m] {_ : Iterator α m β} (it : Iter (α := α) m β) :
    m (USquash it.Step) :=
  (fun x => Iter.Step.ofInternal it (x.inflate (small := _)) |> .deflate) <$> Iterator.step (m := m) it.inner

@[always_inline, inline]
def Iter.step {β : Type w} [Monad m] {_ : Iterator α m β} (it : Iter (α := α) m β) :
    m (Iter.Step it) :=
  USquash.inflate <$> it.stepH

section Finite

structure Iter.FiniteWFRel (α : Type u) (m : Type w → Type w') [Iterator α m β] where
  inner : α

@[always_inline, inline]
def Iter.terminationByFinite {_ : Iterator α m β} [Finite α m] (it : Iter (α := α) m β) :
    Iter.FiniteWFRel α m :=
  ⟨it.inner⟩

def Iter.FiniteWFRel.rel [Iterator α m β] [Finite α m] : FiniteWFRel α m → FiniteWFRel α m → Prop :=
  InvImage (Iterator.plausible_successor m) Iter.FiniteWFRel.inner

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

def Iter.FiniteWFRel.of_step_yield {α m β} {_ : Iterator α m β} [Finite α m]
    {it' it : Iter (α := α) m β} {out : β} (h : it.plausible_step (.yield it' out)) :
    Iter.FiniteWFRel.rel it'.terminationByFinite it.terminationByFinite := by
  simp [terminationByFinite, Iter.FiniteWFRel.rel, Iterator.plausible_successor, InvImage]
  exact ⟨.yield it'.inner out, rfl, h⟩

def Iter.FiniteWFRel.of_step_skip {α m β} {_ : Iterator α m β} [Finite α m]
    {it' it : Iter (α := α) m β} (h : it.plausible_step (.skip it')) : Iter.FiniteWFRel.rel it'.terminationByFinite it.terminationByFinite := by
  simp [terminationByFinite, Iter.FiniteWFRel.rel, Iterator.plausible_successor, InvImage]
  exact ⟨.skip it'.inner, rfl, h⟩

-- def Iter.FiniteWFRel.of_stepH_yield {α m β} {_ : Iterator α m β} [Finite α m]
--     {it' it : Iter (α := α) m β} {out : β}
--     (h : it.plausible_step (.yield it' out)) :
--     Iter.FiniteWFRel.rel it'.terminationByFinite it.terminationByFinite := by
--   apply Iter.FiniteWFRel.of_step_yield
--   simpa [IterationT.mapH_mapH, IterStep.map_map, ComputableSmall.down_up] using
--     IterationT.property_mapH (·.map id ComputableSmall.down) h

-- def Iter.FiniteWFRel.of_stepH_skip {α m β} {_ : Iterator α m β} [Finite α m]
--     {_ : ComputableSmall.{w} α} {_ : ComputableSmall.{w} β}
--     {it' it : Iter (α := α) m β}
--     (h : (Iterator.step (m := m) it.inner).mapH (·.map (toIter m) ComputableSmall.up) |>.property (.skip it')) :
--     Iter.FiniteWFRel.rel it'.terminationByFinite it.terminationByFinite := by
--   apply Iter.FiniteWFRel.of_step_skip
--   simpa [IterationT.mapH_mapH, IterStep.map_map, ComputableSmall.down_up] using
--     IterationT.property_mapH (·.map id ComputableSmall.down) h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact Iter.FiniteWFRel.of_step_yield ‹_›
  | exact Iter.FiniteWFRel.of_step_skip ‹_›
  -- | exact Iter.FiniteWFRel.of_stepH_yield ‹_›
  -- | exact Iter.FiniteWFRel.of_stepH_skip ‹_›
  )

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
