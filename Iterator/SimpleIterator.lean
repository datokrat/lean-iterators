/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper

section SimpleIterator

@[ext]
structure IterationT (m : Type w → Type w') (γ : Type u) where
  property : γ → Prop
  computation : CodensityT m { c : γ // property c }

instance : Monad (IterationT m) where
  pure a := { property b := (b = a)
              computation := pure ⟨a, rfl⟩ }
  bind x f := { property a := ∃ b, (f b).property a ∧ x.property b
                computation := do
                  let b ← x.computation
                  let a ← (f b).computation
                  return ⟨a.1, b.1, a.2, b.2⟩ }

theorem IterationT.computation_pure {m : Type w → Type w'} {γ : Type u} {a : γ} :
    (pure a : IterationT m γ).computation = pure ⟨a, rfl⟩ := rfl

instance (m) [Monad m] : MonadLift m (IterationT m) where
  monadLift t := { property := fun _ => True, computation := (⟨·, True.intro⟩) <$> t }

instance (m) [Monad m] : MonadLift (CodensityT m) (IterationT m) where
  monadLift t := { property := fun _ => True, computation := (⟨·, True.intro⟩) <$> t }

@[always_inline, inline]
def IterationT.liftWithProperty {p : γ → Prop} (t : CodensityT m { c : γ // p c }) : IterationT m γ :=
  { property := p, computation := t }

@[inline]
def IterationT.mapH {γ : Type u} {m : Type w → Type w'} [Monad m]
    {δ : Type v}
    (f : γ → δ)
    (t : IterationT m γ) : IterationT m δ :=
  { property d := ∃ c, d = f c ∧ t.property c,
    computation := t.computation.mapH fun c => ⟨f c.1, c.1, rfl, c.2⟩ }

@[inline]
def IterationT.bindH {m : Type w → Type w'} [Monad m] {γ : Type u} {δ : Type v}
    (t : IterationT m γ) (f : γ → IterationT m δ) : IterationT m δ :=
  { property d := ∃ c, (f c).property d ∧ t.property c
    computation := t.computation.bindH fun c => (f c.1).computation.mapH fun d => ⟨d.1, c.1, d.2, c.2⟩}

def IterationT.liftInnerMonad {γ : Type w} {m : Type w → Type w'} [Pure m] (n : Type w → Type w'') [Monad n] [MonadLift m n] (t : IterationT m γ) :
    IterationT n γ :=
  { property := t.property
    computation := monadLift t.computation.run }

variable {α : Type u} {m : Type w → Type w'} {β : Type v}

variable (m) in
@[always_inline, inline]
def IterationT.step [Iterator α m β] [Monad m] (it : α) : IterationT m (IterStep.for m it) :=
  { property
      | .yield it' b _ => Iterator.yielded m it it' b
      | .skip it' _ => Iterator.skipped m it it'
      | .done _ => Iterator.done m it,
    computation := (fun step => ⟨step, match step with
        | .yield _ _ h => h
        | .skip _ h => h
        | .done h => h⟩) <$> Iterator.step it }

class SimpleIterator (α : Type u) (m : Type w → Type w') (β : outParam (Type v)) where
  step : α → IterationT m (RawStep α β)

instance [SimpleIterator α m β] [Monad m] : Iterator α m β where
  yielded it it' output := SimpleIterator.step (m := m) it |>.property <| .yield it' output ⟨⟩
  skipped it it' := SimpleIterator.step it (m := m) |>.property <| .skip it' ⟨⟩
  done it := SimpleIterator.step (m := m) it |>.property <| .done ⟨⟩
  step it := (match · with
    | ⟨.yield it' output _, h⟩ => .yield it' output h
    | ⟨.skip it' _, h⟩ => .skip it' h
    | ⟨.done _, h⟩ => .done h) <$> (SimpleIterator.step (α := α) (m := m) it).computation

variable (α m) in
class SimpleIterator.Finite [SimpleIterator α m β] [Monad m] where
  rel : α → α → Prop
  wf : WellFounded rel
  subrelation : {it it' : α} → ((SimpleIterator.step (m := m) it).mapH IterStep.successor).property (some it') → rel it' it

variable (α m) in
class SimpleIterator.Productive [SimpleIterator α m β] [Monad m] where
  rel : α → α → Prop
  wf : WellFounded rel
  subrelation : {it it' : α} → (SimpleIterator.step (m := m) it).property (.skip it' ⟨⟩) → rel it' it

instance [SimpleIterator α m β] [Monad m] [SimpleIterator.Finite α m] : Finite α m where
  wf := by
    refine Subrelation.wf (r := InvImage (SimpleIterator.Finite.rel m β) FiniteIteratorWF.inner) ?_ ?_
    · intro x y h
      apply SimpleIterator.Finite.subrelation
      obtain ⟨b, h⟩ | h := h
      · exact ⟨.yield x.inner b ⟨⟩, rfl, h⟩
      · exact ⟨.skip x.inner ⟨⟩, rfl, h⟩
    · apply InvImage.wf
      exact SimpleIterator.Finite.wf

instance [SimpleIterator α m β] [Monad m] [SimpleIterator.Productive α m] : Productive α m where
  wf := by
    refine Subrelation.wf (r := InvImage (SimpleIterator.Productive.rel m β) ProductiveIteratorWF.inner) ?_ ?_
    · intro x y h
      apply SimpleIterator.Productive.subrelation
      exact h
    · apply InvImage.wf
      exact SimpleIterator.Productive.wf

@[always_inline, inline]
def matchStepH {α : Type u} {β : Type v} {m : Type w → Type w'} [Monad m]
    [Iterator α m β]
    {γ : Type x}
    (it : α)
    (yield : α → β → IterationT m γ) (skip : α → IterationT m γ) (done : IterationT m γ) : IterationT m γ :=
  IterationT.step m it |>.bindH (match · with
  | .yield it' b _ => yield it' b
  | .skip it' _ => skip it'
  | .done _ => done)

@[always_inline, inline]
def matchStep {γ : Type max u v} [Monad m]
    [Iterator α m β] (it : α) (yield : α → β → IterationT m γ)
    (skip : α → IterationT m γ) (done : IterationT m γ) : IterationT m γ :=
  matchStepH it yield skip done

theorem successor_yield [Monad m] [Pure m] [SimpleIterator α m β] {it₁ it₂ : α} {b : β} :
    ((pure (IterStep.yield it₁ b True.intro) : IterationT m (RawStep α β)).mapH IterStep.successor).property (some it₂) ↔
      it₂ = it₁ := by
  simp [IterationT.mapH, Pure.pure, IterStep.successor]

theorem successor_skip [Monad m] [Pure m] [SimpleIterator α m β] {it₁ it₂ : α} :
    ((pure (IterStep.skip it₁ ⟨⟩) : IterationT m (RawStep α β)).mapH IterStep.successor).property (some it₂) ↔
      it₂ = it₁ := by
  simp [IterationT.mapH, Pure.pure, IterStep.successor]

theorem successor_done [Monad m] [Pure m] [SimpleIterator α m β] {it: α} :
    ((pure (IterStep.done True.intro) : IterationT m (RawStep α β)).mapH IterStep.successor).property (some it) ↔ False := by
  simp [IterationT.mapH, Pure.pure, IterStep.successor]

theorem successor_matchStepH {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x} {δ : Type y}
    [Monad m] [Iterator α m β]
    {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (IterationT.mapH f <| matchStepH (m := m) (γ := γ) it yield skip done).property x) :
    (∃ it' b, Iterator.yielded m it it' b ∧ (IterationT.mapH f <| yield it' b).property x) ∨
    (∃ it', Iterator.skipped m it it' ∧ (IterationT.mapH f <| skip it').property x) ∨
    (Iterator.done m it ∧ (IterationT.mapH f done).property x) := by
  simp only [IterationT.mapH, IterationT.bindH, matchStepH] at h
  obtain ⟨c, rfl, _, h, h'⟩ := h
  split at h
  · exact Or.inl ⟨_, _, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inl ⟨_, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inr ⟨‹_›, ⟨c, rfl, h⟩⟩

theorem successor_matchStep {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type max u v} {δ : Type y}
    [Monad m] [Iterator α m β] {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (IterationT.mapH f <| matchStep (m := m) (γ := γ) it yield skip done).property x) :
    (∃ it' b, Iterator.yielded m it it' b ∧ (IterationT.mapH f <| yield it' b).property x) ∨
    (∃ it', Iterator.skipped m it it' ∧ (IterationT.mapH f <| skip it').property x) ∨
    (Iterator.done m it ∧ (IterationT.mapH f done).property x) :=
  successor_matchStepH h

theorem property_matchStepH {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x}
    [Monad m] [Iterator α m β]
    {it : α} {yield skip done}
    {x : γ}
    (h : (matchStepH (m := m) (γ := γ) it yield skip done).property x) :
    (∃ it' b, Iterator.yielded m it it' b ∧ (yield it' b).property x) ∨
    (∃ it', Iterator.skipped m it it' ∧ (skip it').property x) ∨
    (Iterator.done m it ∧ done.property x) := by
  simp only [IterationT.bindH, matchStepH] at h
  obtain ⟨c, h, h'⟩ := h
  split at h
  · exact Or.inl ⟨_, _, ‹_›, h⟩
  · exact Or.inr <| Or.inl ⟨_, ‹_›, h⟩
  · exact Or.inr <| Or.inr ⟨‹_›, h⟩

theorem computation_matchStepH {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x}
    [Monad m] [Iterator α m β]
    {it : α} {yield skip done} :
    (matchStepH (m := m) (γ := γ) it yield skip done).computation =
      (IterationT.step m it).computation.bindH (match · with
        | ⟨.yield it' out h, h'⟩ => (yield it' out).computation.mapH (fun y => ⟨y.1, .yield it' out h, y.2, h'⟩)
        | ⟨.skip it' h, h'⟩ => (skip it').computation.mapH (fun y => ⟨y.1, .skip it' h, y.2, h'⟩)
        | ⟨.done h, h'⟩ => done.computation.mapH (fun y => ⟨y.1, .done h, y.2, h'⟩)) := by
  simp only [matchStepH, IterationT.bindH]
  refine congrArg (fun x => (IterationT.step m it).computation.bindH x) ?_
  ext x; cases x
  dsimp only
  split <;> dsimp only

end SimpleIterator
