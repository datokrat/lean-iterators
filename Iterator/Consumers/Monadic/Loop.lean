/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.RCases
import Iterator.Basic
import Iterator.Consumers.Monadic.Partial

def IteratorFor.rel (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    {γ : Type x} (plausible_forInStep : β → γ → ForInStep γ → Prop) (p' p : IterM (α := α) m β × γ) : Prop :=
    (∃ b, p.1.plausible_step (.yield p'.1 b) ∧ plausible_forInStep b p.2 (.yield p'.2)) ∨
      (p.1.plausible_step (.skip p'.1) ∧ p'.2 = p.2)

def IteratorFor.WellFounded (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    {γ : Type x} (plausible_forInStep : β → γ → ForInStep γ → Prop) : Prop :=
    _root_.WellFounded (IteratorFor.rel α m plausible_forInStep)

def IteratorFor.WFRel {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {γ : Type x} {plausible_forInStep : β → γ → ForInStep γ → Prop}
    (_wf : WellFounded α m plausible_forInStep) :=
  IterM (α := α) m β × γ

def IteratorFor.WFRel.mk {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {γ : Type x} {plausible_forInStep : β → γ → ForInStep γ → Prop}
    (wf : WellFounded α m plausible_forInStep) (it : IterM (α := α) m β) (c : γ) :
    IteratorFor.WFRel wf :=
  (it, c)

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {γ : Type x} {plausible_forInStep : β → γ → ForInStep γ → Prop}
    (wf : IteratorFor.WellFounded α m plausible_forInStep) :
    WellFoundedRelation (IteratorFor.WFRel wf) where
  rel := IteratorFor.rel α m plausible_forInStep
  wf := wf

@[specialize]
def IterM.DefaultConsumers.forIn {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type w → Type w''} [Monad n]
    (lift : ∀ γ, m γ → n γ) (γ : Type w)
    (plausible_forInStep : β → γ → ForInStep γ → Prop)
    (wf : IteratorFor.WellFounded α m plausible_forInStep)
    (it : IterM (α := α) m β) (init : γ)
    (f : (b : β) → (c : γ) → n (Subtype (plausible_forInStep b c))) : n γ :=
  haveI : WellFounded _ := wf
  letI : MonadLift m n := ⟨fun {γ} => lift γ⟩
  do
    match ← it.step with
    | .yield it' out _ =>
      match ← f out init with
      | ⟨.yield c, _⟩ => IterM.DefaultConsumers.forIn lift _ plausible_forInStep wf it' c f
      | ⟨.done c, _⟩ => return c
    | .skip it' _ => IterM.DefaultConsumers.forIn lift _ plausible_forInStep wf it' init f
    | .done _ => return init
termination_by IteratorFor.WFRel.mk wf it init
decreasing_by
  · exact Or.inl ⟨out, ‹_›, ‹_›⟩
  · exact Or.inr ⟨‹_›, rfl⟩

@[specialize]
partial def IterM.DefaultConsumers.forInPartial {m : Type w → Type w'} {α : Type w} {β : Type w}
    [Iterator α m β]
    {n : Type w → Type w''} [Monad n]
    (lift : ∀ γ, m γ → n γ) (γ : Type w)
    (it : IterM (α := α) m β) (init : γ)
    (f : (b : β) → (c : γ) → n (ForInStep γ)) : n γ :=
  letI : MonadLift m n := ⟨fun {γ} => lift γ⟩
  do
    match ← it.step with
    | .yield it' out _ =>
      match ← f out init with
      | .yield c => IterM.DefaultConsumers.forInPartial lift _ it' c f
      | .done c => return c
    | .skip it' _ => IterM.DefaultConsumers.forInPartial lift _ it' init f
    | .done _ => return init

class IteratorFor (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    (n : Type w → Type w'') where
  forIn : ∀ (_lift : (γ : Type w) → m γ → n γ) (γ : Type w),
      (plausible_forInStep : β → γ → ForInStep γ → Prop) →
      IteratorFor.WellFounded α m plausible_forInStep →
      IterM (α := α) m β → γ →
      ((b : β) → (c : γ) → n (Subtype (plausible_forInStep b c))) → n γ

class IteratorForPartial (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    (n : Type w → Type w'') where
  forInPartial : ∀ (_lift : (γ : Type w) → m γ → n γ) {γ : Type w},
      IterM (α := α) m β → γ → ((b : β) → (c : γ) → n (ForInStep γ)) → n γ

class LawfulIteratorFor (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    [Monad n] [Iterator α m β] [Finite α m] [IteratorFor α m n] where
  lawful : ∀ lift γ, IteratorFor.forIn lift γ (α := α) (m := m) =
    IterM.DefaultConsumers.forIn lift γ (α := α) (m := m) (n := n)

def IteratorFor.defaultImplementation {α : Type w} {m : Type w → Type w'} {n : Type w → Type w'}
    [Monad m] [Monad n] [Iterator α m β] :
    IteratorFor α m n where
  forIn lift := IterM.DefaultConsumers.forIn lift

def IteratorForPartial.defaultImplementation {α : Type w} {m : Type w → Type w'} {n : Type w → Type w'}
    [Monad m] [Monad n] [Iterator α m β] :
    IteratorForPartial α m n where
  forInPartial lift := IterM.DefaultConsumers.forInPartial lift _

instance (α : Type w) (m : Type w → Type w') (n : Type w → Type w')
    [Monad m] [Monad n] [Iterator α m β] [Finite α m] :
    letI : IteratorFor α m n := .defaultImplementation
    LawfulIteratorFor α m n :=
  letI : IteratorFor α m n := .defaultImplementation
  ⟨fun _ _ => rfl⟩

@[always_inline, inline]
def IteratorFor.finiteForIn {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [Finite α m] [IteratorFor α m n]
    (lift : ∀ γ, m γ → n γ) :
    ForIn n (IterM (α := α) m β) β where
  forIn {γ} [Monad n] it init f :=
    IteratorFor.forIn (α := α) (m := m) lift γ (fun _ _ _ => True)
      (by
        apply Subrelation.wf (r := InvImage IterM.TerminationMeasures.Finite.rel (fun p => p.1.finitelyManySteps))
        · intro p' p h
          apply Relation.TransGen.single
          obtain ⟨b, h, _⟩ | ⟨h, _⟩ := h
          · exact ⟨.yield p'.fst b, rfl, h⟩
          · exact ⟨.skip p'.fst, rfl, h⟩
        · apply InvImage.wf
          exact WellFoundedRelation.wf)
      it init ((⟨·, .intro⟩) <$> f · ·)

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [Finite α m] [IteratorFor α m n]
    [MonadLiftT m n] :
    ForIn n (IterM (α := α) m β) β := IteratorFor.finiteForIn (fun _ => monadLift)

instance {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorForPartial α m n] [MonadLiftT m n] :
    ForIn n (IterM.Partial (α := α) m β) β where
  forIn it init f := IteratorForPartial.forInPartial (α := α) (m := m) (fun _ => monadLift) it.it init f

@[specialize]
def IterM.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad n]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α m β] [Finite α m] [IteratorFor α m n]
    [MonadLiftT m n]
    (f : γ → β → n γ) (init : γ) (it : IterM (α := α) m β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

@[specialize]
def IterM.Partial.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad n]
    {α : Type w} {β : Type w} {γ : Type w} [Iterator α m β] [IteratorForPartial α m n]
    [MonadLiftT m n]
    (f : γ → β → n γ) (init : γ) (it : IterM.Partial (α := α) m β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

@[always_inline, inline]
def IterM.count {α : Type w} {β : Type w} [Iterator α Id β] [Finite α Id]
    (it : IterM (α := α) Id β) : Nat :=
  go it 0
where
  @[specialize]
  go [Finite α Id] it acc :=
    match it.step with
    | .yield it' _ _ => go it' (acc + 1)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.finitelyManySteps

@[always_inline, inline]
partial def IterM.Partial.count {α : Type w} {β : Type w} [Iterator α Id β]
    (it : IterM.Partial (α := α) Id β) : Nat :=
  go it.it 0
where
  @[specialize]
  go it acc :=
    match it.step with
    | .yield it' _ _ => go it' (acc + 1)
    | .skip it' _ => go it' acc
    | .done _ => acc

@[always_inline, inline]
def IterM.countM {m : Type → Type w'} [Monad m] {α : Type} {β : Type} [Iterator α m β] [Finite α m]
    (it : IterM (α := α) m β) : m Nat :=
  go it 0
where
  @[specialize]
  go [Finite α m] it acc := do
    match ← it.step with
      | .yield it' _ _ => go it' (acc + 1)
      | .skip it' _ => go it' acc
      | .done _ => return acc
  termination_by it.finitelyManySteps

@[always_inline, inline]
partial def IterM.Partial.countM {m : Type → Type w'} [Monad m] {α : Type} {β : Type} [Iterator α m β]
    (it : IterM.Partial (α := α) m β) : m Nat :=
  go it.it 0
where
  @[specialize]
  go it acc := do
    match ← it.step with
      | .yield it' _ _ => go it' (acc + 1)
      | .skip it' _ => go it' acc
      | .done _ => return acc

@[always_inline, inline]
def IterM.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [Finite α m] (it : IterM (α := α) m β) [IteratorFor α m m] :
    m PUnit :=
  it.foldM (γ := PUnit) (fun _ _ => pure .unit) .unit

@[always_inline, inline]
def IterM.Partial.drain {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorForPartial α m m] :
    m PUnit :=
  it.foldM (γ := PUnit) (fun _ _ => pure .unit) .unit
