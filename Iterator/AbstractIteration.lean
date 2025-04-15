/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper

section SimpleIterator

abbrev RawStep (α β) := IterStep α β (fun _ _ => True) (fun _ => True) True

@[ext]
structure IterationT (m : Type u → Type v) (γ : Type u) where
  property : γ → Prop
  computation : m { c : γ // property c }

instance [Monad m] : Monad (IterationT m) where
  pure a := { property b := (b = a)
              computation := pure ⟨a, rfl⟩ }
  bind x f := { property a := ∃ b, (f b).property a ∧ x.property b
                computation := do
                  let b ← x.computation
                  let a ← (f b).computation
                  return ⟨a.1, b.1, a.2, b.2⟩ }

instance (m) [Monad m] : MonadLift m (IterationT m) where
  monadLift t := { property := fun _ => True, computation := (⟨·, True.intro⟩) <$> t }

-- @[inline]
-- def IterationT.mapH {γ : Type w} {m : Type w → Type w'} [Monad m]
--     {δ : Type w}
--     (f : γ → δ)
--     (t : IterationT m γ) : IterationT.{x} m δ :=
--   { property d := ∃ c, d = f c ∧ t.property c,
--     computation := (sorry) <$> t.computation }

-- @[inline]
-- def IterationT.bindH {m : Type w → Type w'} [Monad m] {γ : Type u} {δ : Type u'}
--     (t : IterationT.{max u x} m γ) (f : γ → IterationT.{x} m δ) : IterationT.{x} m δ :=
--   { property d := ∃ c, (f c).property d ∧ t.property c
--     computation n _ bindH :=
--       have := t.computation
--         (Cont (n { d : δ // ∃ c, (f c).property d ∧ t.property c }))
--         (fun {_ _} x f h => bindH x (f · h))
--       this (fun c => (fun d => ⟨d.1, c.1, d.2, c.2⟩) <$> (f c).computation n bindH) }

@[always_inline, inline]
def IterationT.step {α : Type u} (m : Type w → Type w') {β : Type v}
    [Iterator α m β] [Monad m] (it : Iterator.α' α m) : IterationT m (IterStep.for m it) :=
  { property
      | .yield it' b _ => Iterator.yielded it it' b
      | .skip it' _ => Iterator.skipped it it'
      | .done _ => Iterator.done it,
    computation := (fun step => ⟨step, match step with
        | .yield _ _ h => h
        | .skip _ h => h
        | .done h => h⟩) <$> Iterator.step it }

class SimpleIterator (α : Type u) (m : Type w → Type w') (β : outParam (Type v)) where
  α' : Type w
  β' : Type w
  αEquiv : Equiv α α'
  βEquiv : Equiv β β'
  step : α' → IterationT m (RawStep α' β')

instance [SimpleIterator α m β] [Monad m] : Iterator α m β where
  α' := SimpleIterator.α' α m
  β' := SimpleIterator.β' α m
  αEquiv := SimpleIterator.αEquiv
  βEquiv := SimpleIterator.βEquiv
  yielded it it' output := SimpleIterator.step (m := m) it |>.property <| .yield it' output ⟨⟩
  skipped it it' := SimpleIterator.step it (m := m) |>.property <| .skip it' ⟨⟩
  done it := SimpleIterator.step (m := m) it |>.property <| .done ⟨⟩
  step it := (match · with
    | ⟨.yield it' output _, h⟩ => .yield it' output h
    | ⟨.skip it' _, h⟩ => .skip it' h
    | ⟨.done _, h⟩ => .done h) <$> (SimpleIterator.step it).computation

set_option pp.universes true in
class SimpleIterator.Finite {β : Type v} (α : Type u) (m : Type w → Type w') [SimpleIterator α m β] [Monad m] where
  rel : Iterator.α' α m → Iterator.α' α m → Prop
  wf : WellFounded rel
  subrelation : {it it' : Iterator.α' α m} → (IterStep.successor <$> (SimpleIterator.step (m := m) it)).property (some it') → rel it' it

instance (α m) [SimpleIterator.{0} α m β] [Monad m] [SimpleIterator.Finite α m] : Finite α m where
  wf := by
    refine Subrelation.wf (r := InvImage (SimpleIterator.Finite.rel (α := α) (m := m)) FiniteIteratorWF.inner) ?_ ?_
    · intro x y h
      apply SimpleIterator.Finite.subrelation
      obtain ⟨b, h⟩ | h := h
      · exact ⟨.yield x.inner b ⟨⟩, rfl, h⟩
      · exact ⟨.skip x.inner ⟨⟩, rfl, h⟩
    · apply InvImage.wf
      exact SimpleIterator.Finite.wf

-- @[inline]
-- def matchStepH.{w} {α : Type u} {β : Type v} {m : Type w → Type w'} [Monad m]
--     [Iterator α m β] [SteppableIterator.{max x u v} α m β]
--     {γ : Type v'}
--     (it : α)
--     (yield : α → β → IterationT.{x} m γ) (skip : α → IterationT.{x} m γ) (done : IterationT.{x} m γ) : IterationT.{x} m γ :=
--   IterationT.step m it |>.bindH (match · with
--   | .yield it' b _ => yield it' b
--   | .skip it' _ => skip it'
--   | .done _ => done)

variable {α : Type u} {m : Type w → Type w'} {β : Type v}

@[inline]
def matchStep {γ : Type w} [Monad m]
    [Iterator α m β] (it : Iterator.α' α m) (yield : Iterator.α' α m → β → IterationT m γ)
    (skip : Iterator.α' α m → IterationT m γ) (done : IterationT m γ) : IterationT m γ := do
  match ← IterationT.step m it with
  | .yield it' b _ => yield it' (Iterator.βEquiv.inv b)
  | .skip it' _ => skip it'
  | .done _ => done

theorem successor_yield [Monad m] [Pure m] [SimpleIterator α m β] {it₁ it₂ : SimpleIterator.α' α m} {b} :
    (IterStep.successor <$>
        (pure (IterStep.yield it₁ b True.intro) : IterationT m (RawStep (SimpleIterator.α' α m) (SimpleIterator.β' α m)))).property (some it₂) ↔
      it₂ = it₁ := by
  simp [Functor.map, Pure.pure, IterStep.successor]

theorem successor_skip [Monad m] [Pure m] [SimpleIterator α m β] {it₁ it₂ : SimpleIterator.α' α m} :
    (IterStep.successor <$>
        (pure (IterStep.skip it₁ ⟨⟩) : IterationT m (RawStep (SimpleIterator.α' α m) (SimpleIterator.β' α m)))).property (some it₂) ↔
      it₂ = it₁ := by
  simp [Functor.map, Pure.pure, IterStep.successor]

theorem successor_done [Monad m] [Pure m] [SimpleIterator α m β] {it: SimpleIterator.α' α m} :
    (IterStep.successor <$>
      (pure (IterStep.done True.intro : RawStep (SimpleIterator.α' α m) (SimpleIterator.β' α m)) : IterationT m _)).property (some it) ↔ False := by
  simp [Functor.map, Pure.pure, IterStep.successor]

-- theorem successor_matchStepH.{w} {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x} {δ : Type y}
--     [Monad m] [Iterator α m β] [SteppableIterator α m β]
--     {it : α} {yield skip done}
--     {f : γ → δ} {x : δ}
--     (h : (IterationT.mapH f <| matchStepH (m := m) (γ := γ) it yield skip done).property x) :
--     (∃ it' b, Iterator.yielded m it it' b ∧ (IterationT.mapH f <| yield it' b).property x) ∨
--     (∃ it', Iterator.skipped m it it' ∧ (IterationT.mapH f <| skip it').property x) ∨
--     (Iterator.finished m it ∧ (IterationT.mapH f done).property x) := by
--   simp only [IterationT.mapH, IterationT.bindH, matchStepH] at h
--   obtain ⟨c, rfl, _, h, h'⟩ := h
--   split at h
--   · exact Or.inl ⟨_, _, ‹_›, ⟨c, rfl, h⟩⟩
--   · exact Or.inr <| Or.inl ⟨_, ‹_›, ⟨c, rfl, h⟩⟩
--   · exact Or.inr <| Or.inr ⟨‹_›, ⟨c, rfl, h⟩⟩

theorem successor_matchStep {α β γ δ} {m} [Monad m] [Iterator α m β] {it : Iterator.α' α m} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (f <$> matchStep it yield skip done).property x) :
    (∃ it' b, Iterator.yielded it it' b ∧ (f <$> yield it' (Iterator.βEquiv.inv b)).property x) ∨
    (∃ it', Iterator.skipped it it' ∧ (f <$> skip it').property x) ∨
    (Iterator.done it ∧ (f <$> done).property x) := by
  simp only [Functor.map, Bind.bind, matchStep] at h
  obtain ⟨c, rfl, _, h, h'⟩ := h
  split at h
  · exact Or.inl ⟨_, _, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inl ⟨_, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inr ⟨‹_›, ⟨c, rfl, h⟩⟩

#exit

end SimpleIterator

section AbstractIteration

@[ext]
structure Iteration.{w} (m : Type u → Type v) (γ : Type w) where
  prop : γ → Prop
  elem : OverT m { c // prop c }

@[inline]
def Iteration.pure {γ : Type u} {m : Type w → Type w'} [Pure m] (c : γ) : Iteration m γ :=
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
def Iteration.mapH {γ : Type u} {m : Type w → Type w'}
    {δ : Type u'}
    (f : γ → δ)
    (t : Iteration m γ) : Iteration m δ :=
  { prop d := ∃ c, d = f c ∧ t.prop c,
    elem := OverT.mapH (fun c => ⟨f c.1, ⟨c.1, rfl, c.2⟩⟩) t.elem }

@[inline]
def Iteration.bindH {m : Type v → Type v'} [Monad m] {β : Type w} {β' : Type w'}
    (t : Iteration m β) (f : β → Iteration m β') : Iteration m β' :=
  { prop d := ∃ c, (f c).prop d ∧ t.prop c
    elem := t.elem.bindH (fun c => (fun x => ⟨x.1, ⟨c.1, x.2, c.2⟩⟩) <$> (f c.1).elem) }

instance (m : Type w → Type w') [Pure m] : Pure (Iteration m) where
  pure := Iteration.pure

instance (m) [Functor m] : Functor (Iteration m) where
  map := Iteration.map

instance (m) [Monad m] : Monad (Iteration m) where
  pure := Iteration.pure
  bind := Iteration.bind

-- TODO: provide MonadLift m (OverT m) instead
instance (m) [Monad m] : MonadLift m (Iteration m) where
  monadLift t := { prop := fun _ => True, elem := (⟨·, True.intro⟩) <$> OverT.eval t }

instance (m) [Monad m] : MonadLift (OverT m) (Iteration m) where
  monadLift t := { prop := fun _ => True, elem := (⟨·, True.intro⟩) <$> t }

@[inline]
def Iteration.step {α : Type u} (m : Type w → Type w') {β : Type v} [Iterator α m β] [Functor m] (it : α) : Iteration m (IterStep.for m it) :=
  { prop
      | .yield it' b _ => Iterator.yielded m it it' b
      | .skip it' _ => Iterator.skipped m it it'
      | .done _ => Iterator.finished m it,
    elem := (fun step => ⟨step, match step with
        | .yield _ _ h => h
        | .skip _ h => h
        | .done h => h⟩) <$> Iterator.step (m := m) it
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
def matchStepH.{w} {α : Type u} {β : Type v} {m : Type w → Type w'} [Monad m]
    [Iterator α m β]
    {γ : Type v'}
    (it : α)
    (yield : α → β → Iteration m γ) (skip : α → Iteration m γ) (done : Iteration m γ) : Iteration m γ :=
  Iteration.step m it |>.bindH (match · with
  | .yield it' b _ => yield it' b
  | .skip it' _ => skip it'
  | .done _ => done)

-- @[inline]
-- def matchStepH.{w} {α : Type u} {β : Type v} {m : Type w → Type w'} [Functor m]
--     {n : Type x → Type x'} [Monad n]
--     [Iterator α m β]
--     (fmn : ∀ ⦃γ' : Type max u v⦄ ⦃δ' : Type max u v w⦄, (γ' → δ') → OverT m γ' → OverT n δ')
--     {γ : Type x}
--     (it : α)
--     (yield : α → β → Iteration n γ) (skip : α → Iteration n γ) (done : Iteration n γ) : n γ := do
--   match ← Iteration.mapH ULift.up mf (Iteration.step it) with
--   | ⟨.yield it' b _⟩ => yield it' b
--   | ⟨.skip it' _⟩ => skip it'
--   | ⟨.done _⟩ => done

@[inline]
def matchStep {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x} [Monad m] [Iterator α m β] (it : α)
    (yield : α → β → Iteration m γ) (skip : α → Iteration m γ) (done : Iteration m γ) : Iteration m γ :=
  matchStepH it yield skip done

theorem finite_instIterator {α : Type u} {β : Type v} {m : Type w → Type w'} [Functor m]
    (stepFn : α → Iteration m (RawStep α β)) {rel : α → α → Prop} (hwf : WellFounded rel) :
    letI : Iterator α m β := Iteration.instIterator stepFn
    (h : ∀ it it', ((ULift.up ∘ IterStep.successor) <$> stepFn it).prop (ULift.up <| some <| it') → rel it' it) → Finite α m := by
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
    (h : ∀ it it', (stepFn it).prop (.skip it' ⟨⟩) → rel it' it) → Productive α m := by
  letI : Iterator α m β := Iteration.instIterator stepFn
  intro h
  refine ⟨?_⟩
  refine Subrelation.wf ?_ <| InvImage.wf ProductiveIteratorWF.inner hwf
  intro it it' hlt
  specialize h it'.inner it.inner
  apply h
  simp only [ProductiveIteratorWF.lt, Iteration.instIterator] at hlt
  exact hlt

theorem Iteration.prop_bindH {α β m} [Monad m] (f : α → Iteration m β) (t : Iteration m α) (b : β) :
    (t.bindH f).prop b ↔ ∃ a, (f a).prop b ∧ t.prop a :=
  Iff.rfl

theorem Iteration.prop_bind {α β m} [Monad m] (f : α → Iteration m β) (t : Iteration m α) (b : β) :
    (t >>= f).prop b ↔ ∃ a, (f a).prop b ∧ t.prop a :=
  Iff.rfl

theorem Iteration.prop_mapH {α β m} [Functor m] (f : α → β) (t : Iteration m α) (b : β) :
    (t.mapH f).prop b ↔ ∃ a, b = f a ∧ t.prop a :=
  Iff.rfl

theorem Iteration.prop_map {α β m} [Functor m] (f : α → β) (t : Iteration m α) (b : β) :
    (f <$> t).prop b ↔ ∃ a, b = f a ∧ t.prop a :=
  Iff.rfl

theorem prop_successor_matchStepH.{w} {α : Type u} {m : Type w → Type w'} {β : Type v} {γ : Type x} [Monad m] [Iterator α m β]
    {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (f <$> matchStepH (m := m) (γ := γ) it yield skip done).prop x) :
    (∃ it' b, Iterator.yielded m it it' b ∧ (f <$> yield it' b).prop x) ∨
    (∃ it', Iterator.skipped m it it' ∧ (f <$> skip it').prop x) ∨
    (Iterator.finished m it ∧ (f <$> done).prop x) := by
  simp only [Iteration.prop_map, matchStepH, Iteration.prop_bindH] at h
  obtain ⟨c, rfl, _, h, h'⟩ := h
  split at h
  · exact Or.inl ⟨_, _, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inl ⟨_, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inr ⟨‹_›, ⟨c, rfl, h⟩⟩

theorem prop_successor_matchStep {α β γ} {m} [Monad m] [Iterator α m β] {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (f <$> matchStep (m := m) (γ := γ) it yield skip done).prop x) :
    (∃ it' b, Iterator.yielded m it it' b ∧ (f <$> yield it' b).prop x) ∨
    (∃ it', Iterator.skipped m it it' ∧ (f <$> skip it').prop x) ∨
    (Iterator.finished m it ∧ (f <$> done).prop x) :=
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
