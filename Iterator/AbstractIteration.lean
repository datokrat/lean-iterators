/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper

section AbstractIteration

abbrev RawStep (α β) := IterStep α β (fun _ _ => True) (fun _ => True) True

abbrev IterStep.for {α β m} [Iterator α m β] (it : α) := IterStep α β (Iterator.yielded it) (Iterator.skipped it) (Iterator.finished it)

@[ext]
structure Iteration (m : Type u → Type v) (γ : Type u) where
  prop : γ → Prop
  elem : m { c // prop c }

@[inline]
def Iteration.pure {γ m} [Pure m] (c : γ) : Iteration m γ :=
  { prop c' := (c' = c), elem := Pure.pure ⟨c, rfl⟩ }

@[inline]
def Iteration.bind {γ δ m} [Monad m] (t : Iteration m γ) (f : γ → Iteration m δ) : Iteration m δ :=
  { prop d := ∃ c, (f c).prop d ∧ t.prop c,
    elem := t.elem >>= (fun c => (fun x => ⟨x.1, ⟨c.1, x.2, c.2⟩⟩) <$> (f c.1).elem) }

@[inline]
def Iteration.map {γ δ m} [Functor m] (f : γ → δ) (t : Iteration m γ) : Iteration m δ :=
  { prop d := ∃ c, d = f c ∧ t.prop c,
    elem := (fun c => ⟨f c.1, ⟨c.1, rfl, c.2⟩⟩) <$> t.elem }

@[inline]
def Iteration.mapH {γ : Type u} {m : Type u → Type v}
    {δ : Type u'} {n : Type u' → Type v'}
    (f : γ → δ) (mf : ∀ {γ' : Type u} {δ' : Type u'}, (γ' → δ') → m γ' → n δ')
    (t : Iteration m γ) : Iteration n δ :=
  { prop d := ∃ c, d = f c ∧ t.prop c,
    elem := mf (fun c => ⟨f c.1, ⟨c.1, rfl, c.2⟩⟩) t.elem }

instance (m) [Pure m] : Pure (Iteration m) where
  pure := Iteration.pure

instance (m) [Functor m] : Functor (Iteration m) where
  map := Iteration.map

instance (m) [Monad m] : Monad (Iteration m) where
  pure := Iteration.pure
  bind := Iteration.bind

@[inline]
def Iteration.step {α : Type u} {β : Type v} [Iterator α m β] [Functor m] (it : α) : Iteration m (IterStep.for it) :=
  { prop
      | .yield it' b _ => Iterator.yielded it it' b
      | .skip it' _ => Iterator.skipped it it'
      | .done _ => Iterator.finished it,
    elem := (fun step => ⟨step, match step with
        | .yield _ _ h => h
        | .skip _ h => h
        | .done h => h⟩) <$> Iterator.step it
  }

@[inline]
def Iteration.instIterator [Functor m] (stepFn : α → Iteration m (RawStep α β)) : Iterator α m β where
  yielded it it' b := (stepFn it).prop (.yield it' b ⟨⟩)
  skipped it it' := (stepFn it).prop (.skip it' ⟨⟩)
  finished it := (stepFn it).prop (.done ⟨⟩)
  step it := (match · with
    | ⟨.yield it' b _, h⟩ => .yield it' b h
    | ⟨.skip it' _, h⟩ => .skip it' h
    | ⟨.done _, h⟩ => .done h) <$> (stepFn it).elem

@[inline]
def matchStepH.{w} {α : Type u} {β : Type v} [Iterator α m β] {γ : Type (max u v w)} [Functor m]
    (mf : ∀ {γ' : Type max u v} {δ' : Type max u v w}, (γ' → δ') → m γ' → n δ') [Monad n]
    (it : α)
    (yield : α → β → Iteration n γ) (skip : α → Iteration n γ) (done : Iteration n γ) := do
  match ← Iteration.mapH ULift.up mf (Iteration.step it) with
  | ⟨.yield it' b _⟩ => yield it' b
  | ⟨.skip it' _⟩ => skip it'
  | ⟨.done _⟩ => done

@[inline]
def matchStep {α : Type u} {β : Type v} {γ : Type (max u v)} [Monad m] [Iterator α m β] (it : α)
    (yield : α → β → Iteration m γ) (skip : α → Iteration m γ) (done : Iteration m γ) :=
  matchStepH.{u} (n := m) Functor.map it yield skip done

  --   do
  -- match ← Iteration.step it with
  -- | .yield it' b _ => yield it' b
  -- | .skip it' _ => skip it'
  -- | .done _ => done

theorem finite_instIterator {α : Type u} {β : Type v} {m : Type (max u v) → Type (max u v)} [Functor m]
    (stepFn : α → Iteration m (RawStep α β)) {rel : α → α → Prop} (hwf : WellFounded rel) :
    letI : Iterator α m β := Iteration.instIterator stepFn
    (h : ∀ it it', ((ULift.up ∘ IterStep.successor) <$> stepFn it).prop (ULift.up <| some <| it') → rel it' it) → Finite α := by
  letI : Iterator α m β := Iteration.instIterator stepFn
  intro h
  refine ⟨?_⟩
  refine Subrelation.wf ?_ <| InvImage.wf FiniteIteratorWF.inner hwf
  intro it it' hlt
  specialize h it'.inner it.inner
  apply h
  simp only [Functor.map]
  simp only [FiniteIteratorWF.lt, Iteration.instIterator] at hlt
  obtain ⟨b, hlt⟩ | hlt := hlt
  · exact ⟨_, rfl, hlt⟩
  · exact ⟨_, rfl, hlt⟩

theorem productive_instIterator {α} [Functor m] (stepFn : α → Iteration m (RawStep α β)) {rel : α → α → Prop} (hwf : WellFounded rel) :
    letI : Iterator α m β := Iteration.instIterator stepFn
    (h : ∀ it it', (stepFn it).prop (.skip it' ⟨⟩) → rel it' it) → Productive α := by
  letI : Iterator α m β := Iteration.instIterator stepFn
  intro h
  refine ⟨?_⟩
  refine Subrelation.wf ?_ <| InvImage.wf ProductiveIteratorWF.inner hwf
  intro it it' hlt
  specialize h it'.inner it.inner
  apply h
  simp only [ProductiveIteratorWF.lt, Iteration.instIterator] at hlt
  exact hlt

theorem Iteration.prop_bind {α β m} [Monad m] (f : α → Iteration m β) (t : Iteration m α) (b : β) :
    (t >>= f).prop b ↔ ∃ a, (f a).prop b ∧ t.prop a :=
  Iff.rfl

theorem Iteration.prop_map {α β m} [Functor m] (f : α → β) (t : Iteration m α) (b : β) :
    (f <$> t).prop b ↔ ∃ a, b = f a ∧ t.prop a :=
  Iff.rfl

theorem prop_successor_matchStepH.{w} {α : Type u} {β : Type v} {γ : Type (max u v w)} {m} [Monad m] [Iterator α m β]
    {mf : ∀ {γ' : Type max u v} {δ' : Type max u v w}, (γ' → δ') → m γ' → n δ'} [Monad n] {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (f <$> matchStepH (γ := γ) mf it yield skip done).prop x) :
    (∃ it' b, Iterator.yielded it it' b ∧ (f <$> yield it' b).prop x) ∨
    (∃ it', Iterator.skipped it it' ∧ (f <$> skip it').prop x) ∨
    (Iterator.finished it ∧ (f <$> done).prop x) := by
  simp only [Iteration.prop_map, matchStepH, Iteration.prop_bind] at h
  obtain ⟨c, rfl, _, h, h'⟩ := h
  split at h
  · exact Or.inl ⟨_, _, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inl ⟨_, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inr ⟨‹_›, ⟨c, rfl, h⟩⟩

theorem prop_successor_matchStep {α β γ} {m} [Monad m] [Iterator α m β] {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (f <$> matchStep (γ := γ) it yield skip done).prop x) :
    (∃ it' b, Iterator.yielded it it' b ∧ (f <$> yield it' b).prop x) ∨
    (∃ it', Iterator.skipped it it' ∧ (f <$> skip it').prop x) ∨
    (Iterator.finished it ∧ (f <$> done).prop x) :=
  prop_successor_matchStepH h

theorem successor_skip {α β m} [Functor m] [Pure m] [Iterator α m β] {it₁ it₂ : α} :
    (IterStep.successor <$> pure (f := Iteration m) (IterStep.skip it₁ True.intro : RawStep α β)).prop (some it₂) ↔
      it₂ = it₁ := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

theorem successor_yield {α β m} [Functor m] [Pure m] [Iterator α m β] {it₁ it₂ : α} {b} :
    (IterStep.successor <$> pure (f := Iteration m) (IterStep.yield it₁ b True.intro : RawStep α β)).prop (some it₂) ↔
      it₂ = it₁ := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

theorem successor_done {α β m} [Functor m] [Pure m] [Iterator α m β] {it: α} :
    (IterStep.successor <$> pure (f := Iteration m) (IterStep.done True.intro : RawStep α β)).prop (some it) ↔
      False := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

theorem up_successor_skip {α β m} [Functor m] [Pure m] [Iterator α m β] {it₁ it₂ : α} :
    ((ULift.up ∘ IterStep.successor) <$> pure (f := Iteration m) (IterStep.skip it₁ True.intro : RawStep α β)).prop (ULift.up <| some it₂) ↔
      it₂ = it₁ := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

theorem up_successor_yield {α β m} [Functor m] [Pure m] [Iterator α m β] {it₁ it₂ : α} {b} :
    ((ULift.up ∘ IterStep.successor) <$> pure (f := Iteration m) (IterStep.yield it₁ b True.intro : RawStep α β)).prop (ULift.up <| some it₂) ↔
      it₂ = it₁ := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

theorem up_successor_done {α β m} [Functor m] [Pure m] [Iterator α m β] {it: α} :
    ((ULift.up ∘ IterStep.successor) <$> pure (f := Iteration m) (IterStep.done True.intro : RawStep α β)).prop (ULift.up <| some it) ↔
      False := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

end AbstractIteration
