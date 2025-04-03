/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper

section FilterMap

-- todo: more universe polymorphism
variable {m : Type max u v → Type max u v} {α : Type u} {β γ : Type v} {f : β → Option γ}

variable (α) in
structure FilterMap (f : β → Option γ) where
  inner : α

instance [Iterator α m β] [Functor m] : Iterator (FilterMap α f) m γ where
  yielded it it' b := ∃ b', f b' = some b ∧ Iterator.yielded it.inner it'.inner b'
  skipped it it' := (∃ b', f b' = none ∧ Iterator.yielded it.inner it'.inner b') ∨ Iterator.skipped it.inner it'.inner
  finished it := Iterator.finished it.inner
  step it := (match · with
    | .yield it' x h => match h' : f x with
      | none => .skip ⟨it'⟩ (.inl ⟨x, h', h⟩)
      | some y => .yield ⟨it'⟩ y ⟨x, h', h⟩
    | .skip it' h => .skip ⟨it'⟩ (.inr h)
    | .done h => .done h) <$> Iterator.step it.inner

theorem FilterMap.finiteIteratorWF_subrelation [Functor m] [Iterator α m β] :
    Subrelation
      (FiniteIteratorWF.lt (α := (FilterMap α f)))
      (InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ FilterMap.inner ∘ FiniteIteratorWF.inner)) := by
  intro x y hlt
  simp only [FiniteIteratorWF.lt, Iterator.yielded, Iterator.skipped] at hlt
  obtain ⟨b, b', h⟩ | ⟨b', h⟩ | h := hlt
  · exact Or.inl ⟨b', h.2⟩
  · exact Or.inl ⟨b', h.2⟩
  · exact Or.inr h

theorem FilterMap.productiveIteratorWF_subrelation [Functor m] [Iterator α m β] :
    Subrelation
      (ProductiveIteratorWF.lt (α := (FilterMap α (some ∘ f))))
      (InvImage ProductiveIteratorWF.lt (productiveIteratorWF ∘ FilterMap.inner ∘ ProductiveIteratorWF.inner)) := by
  intro x y hlt
  simp only [ProductiveIteratorWF.lt, Iterator.yielded, Iterator.skipped] at hlt
  obtain ⟨_, h, _⟩ | h := hlt
  · contradiction
  · exact h

instance [Functor m] [Iterator α m β] [Finite α] : Finite (FilterMap α f) where
  wf := FilterMap.finiteIteratorWF_subrelation.wf <|
    InvImage.wf (finiteIteratorWF ∘ FilterMap.inner ∘ FiniteIteratorWF.inner) Finite.wf

@[inline]
def Iter.filterMap [Iterator α m β] [Functor m] (f : β → Option γ) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) f) m γ :=
  toIter ⟨it⟩

@[inline]
def Iter.map [Iterator α m β] [Functor m] (f : β → γ) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) (some ∘ f)) m γ :=
  toIter ⟨it⟩

@[inline]
def Iter.filter [Iterator α m β] [Functor m] (f : β → Bool) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) (fun x => if f x then some x else none)) m β :=
  toIter ⟨it⟩

end FilterMap

section FlatMap

-- todo: more universe polymorphism
variable {m : Type u → Type u} {α α' β β' : Type u} [Iterator α m β] [Iterator α' m β'] {f : β → α'}

abbrev RawStep (α β) := IterStep α β (fun _ _ => True) (fun _ => True) True

abbrev IterStep.for {α β m} [Iterator α m β] (it : α) := IterStep α β (Iterator.yielded it) (Iterator.skipped it) (Iterator.finished it)

structure Iteration (m) [Monad m] (γ : Type u) where
  prop : γ → Prop
  elem : m { c // prop c }

@[inline]
def Iteration.pure {γ m} [Monad m] (c : γ) : Iteration m γ :=
  { prop c' := (c' = c), elem := Pure.pure ⟨c, rfl⟩ }

@[inline]
def Iteration.bind {γ δ m} [Monad m] (t : Iteration m γ) (f : γ → Iteration m δ) : Iteration m δ :=
  { prop d := ∃ c, (f c).prop d ∧ t.prop c, elem :=
    Bind.bind t.elem (fun c => (fun x => ⟨x.1, ⟨c.1, x.2, c.2⟩⟩) <$> (f c.1).elem) }

#print Iteration.bind

instance (m) [Monad m] : Monad (Iteration m) where
  pure := Iteration.pure
  bind := Iteration.bind

@[inline]
def Iteration.step {α β : Type u} [Iterator α m β] [Monad m] (it : α) : Iteration m (IterStep.for it) :=
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
def Iteration.instIterator [Monad m] (stepFn : α → Iteration m (RawStep α β)) : Iterator α m β where
  yielded it it' b := (stepFn it).prop (.yield it' b ⟨⟩)
  skipped it it' := (stepFn it).prop (.skip it' ⟨⟩)
  finished it := (stepFn it).prop (.done ⟨⟩)
  step it := (match · with
    | ⟨.yield it' b _, h⟩ => .yield it' b h
    | ⟨.skip it' _, h⟩ => .skip it' h
    | ⟨.done _, h⟩ => .done h) <$> (stepFn it).elem

/-
Ideas: use transitivity of the relation, flatMapStepSome

Can I introduce a kind of generator monad?

do
  yield 1
  yield 2
  lift <| println "hi"
  for x in l do
    yield x

it.bind (fun x => it₂ x)

Iterators with a return type!
-/

-- instance [Functor m] [Iterator α m β] [Iterator α' m β'] : Iterator (FlatMapAux α f) m β' where
--   yielded it it' b := FlatMap.rawStep_eq it (.yield it' b ⟨⟩)
--     -- | { it₁, it₂ := some it₂ }, { it₁ := it₁', it₂ := some it₂' }, b => it₁ = it₁' ∧ Iterator.yielded it₂ it₂' b
--     -- | _, _, _ => False
--   skipped it it' := FlatMap.rawStep_eq it (.skip it' ⟨⟩)
--     -- | { it₁, it₂ := none }, { it₁ := it₁', it₂ := none } => Iterator.skipped it₁ it₁'
--     -- | { it₁, it₂ := none }, { it₁ := it₁', it₂ := some it₂' } => ∃ b, f b = it₂' ∧ Iterator.yielded it₁ it₁' b
--     -- | { it₁, it₂ := some it₂ }, { it₁ := it₁', it₂ := none } => it₁ = it₁' ∧ Iterator.finished it₂
--     -- | { it₁, it₂ := some it₂ }, { it₁ := it₁', it₂ := some it₂' } => it₁ = it₁' ∧ Iterator.skipped it₂ it₂'
--   finished it := FlatMap.rawStep_eq it (.done ⟨⟩)
--     -- | { it₁, it₂ := none } => Iterator.finished it₁
--     -- | _ => False
--   step
--     | { it₁, it₂ := none } =>
--       (match · with
--       | .yield it₁' b h => .skip { it₁ := it₁', it₂ := some (f b) } (.inl ⟨it₁', b, h, rfl⟩)
--       | .skip it₁' h => .skip { it₁ := it₁', it₂ := none } (.inr <| .inl ⟨it₁', h, rfl⟩)
--       | .done h => .done (.inr <| .inr ⟨h, rfl⟩)) <$> Iterator.step it₁
--     | { it₁, it₂ := some it₂ } =>
--       (match · with
--         | .yield it₂' b h => .yield { it₁ := it₁, it₂ := some it₂' } b (.inl ⟨it₂', b, h, rfl⟩)
--         | .skip it₂' h => .skip { it₁ := it₁, it₂ := some it₂' } (.inr <| .inl ⟨it₂', h, rfl⟩)
--         | .done h => .skip { it₁ := it₁, it₂ := none } (.inr <| .inr ⟨h, rfl⟩)) <$> Iterator.step it₂

structure FlatMap (α) (f : β → α') where
  it₁ : α
  it₂ : Option α'

@[inline]
def FlatMap.init (it : α) (f : β → α') : FlatMap α f :=
  ⟨it, none⟩

@[inline]
def matchStep [Monad m] [Iterator α m β] (it : α)
    (yield : α → β → Iteration m γ) (skip : α → Iteration m γ) (done : Iteration m γ) := do
  match ← Iteration.step it with
  | .yield it' b _ => yield it' b
  | .skip it' _ => skip it'
  | .done _ => done

theorem finite_instIterator {α} [Monad m] (stepFn : α → Iteration m (RawStep α β)) {rel : α → α → Prop} (hwf : WellFounded rel) :
    letI : Iterator α m β := Iteration.instIterator stepFn
    (h : ∀ it it', (IterStep.successor <$> stepFn it).prop (some it') → rel it' it) → Finite α := by
  letI : Iterator α m β := Iteration.instIterator stepFn
  intro h
  refine ⟨?_⟩
  refine Subrelation.wf ?_ <| InvImage.wf FiniteIteratorWF.inner hwf
  intro it it' hlt
  specialize h it'.inner it.inner
  apply h
  simp [Functor.map, Iteration.bind, Iteration.pure]
  simp [FiniteIteratorWF.lt, Iteration.instIterator] at hlt
  obtain ⟨b, hlt⟩ | hlt := hlt
  · exact ⟨_, rfl, hlt⟩
  · exact ⟨_, rfl, hlt⟩

theorem productive_instIterator {α} [Monad m] (stepFn : α → Iteration m (RawStep α β)) {rel : α → α → Prop} (hwf : WellFounded rel) :
    letI : Iterator α m β := Iteration.instIterator stepFn
    (h : ∀ it it', (stepFn it).prop (.skip it' ⟨⟩) → rel it' it) → Productive α := by
  letI : Iterator α m β := Iteration.instIterator stepFn
  intro h
  refine ⟨?_⟩
  refine Subrelation.wf ?_ <| InvImage.wf ProductiveIteratorWF.inner hwf
  intro it it' hlt
  specialize h it'.inner it.inner
  apply h
  simp [ProductiveIteratorWF.lt, Iteration.instIterator] at hlt
  exact hlt

@[inline]
def flatMapStepNone [Monad m] [Iterator α m β] [Iterator α' m β'] (f : β → α') (it₁ : α) :
    Iteration m (RawStep (FlatMap α f) β') :=
  matchStep it₁
    (fun it₁' b => pure <| .skip { it₁ := it₁', it₂ := some (f b) } ⟨⟩)
    (fun it₁' => pure <| .skip { it₁ := it₁', it₂ := none } ⟨⟩)
    (pure <| .done ⟨⟩)

@[inline]
def flatMapStepSome [Monad m] [Iterator α m β] [Iterator α' m β'] (f : β → α') (it₁ : α) (it₂ : α') :
    Iteration m (RawStep (FlatMap α f) β') :=
  matchStep it₂
    (fun it₂' b => pure <| .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩)
    (fun it₂' => pure <| .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩)
    (flatMapStepNone f it₁)

instance [Monad m] [Iterator α m β] [Iterator α' m β'] : Iterator (FlatMap α f) m β' :=
  Iteration.instIterator fun
    | { it₁, it₂ := none } => flatMapStepNone f it₁
    | { it₁, it₂ := some it₂ } => flatMapStepSome f it₁ it₂

def FlatMap.lex (f : β → α') (r₁ : α → α → Prop) (r₂ : α' → α' → Prop) : FlatMap α f → FlatMap α f → Prop
  | ⟨it₁, it₂⟩, ⟨it₁', it₂'⟩ => (it₁, it₂).Lex r₁ (Option.lt r₂) (it₁', it₂')

theorem FlatMap.lex_of_left {f : β → α'} {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it it'}
    (h : r₁ it'.it₁ it.it₁) : FlatMap.lex f r₁ r₂ it' it :=
  Prod.Lex.left _ _ h

theorem FlatMap.lex_of_right {f : β → α'} {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it₁ it₂ it₂'}
    (h : r₂ it₂' it₂) : FlatMap.lex f r₁ r₂ ⟨it₁, it₂'⟩ ⟨it₁, it₂⟩ :=
  Prod.Lex.right _ h

theorem Iteration.prop_bind {α β m} [Monad m] (f : α → Iteration m β) (t : Iteration m α) (b : β) :
    (t >>= f).prop b ↔ ∃ a, (f a).prop b ∧ t.prop a :=
  Iff.rfl

theorem Iteration.prop_map {α β m} [Monad m] (f : α → β) (t : Iteration m α) (b : β) :
    (f <$> t).prop b ↔ ∃ a, b = f a ∧ t.prop a :=
  Iff.rfl

theorem prop_successor_matchStep {α β γ : Type u} {m} [Monad m] [Iterator α m β] {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (f <$> matchStep (γ := γ) it yield skip done).prop x) {p : Prop}
    (hy : ∀ it' b, Iterator.yielded it it' b → (f <$> yield it' b).prop x → p)
    (hs : ∀ it', Iterator.skipped it it' → (f <$> skip it').prop x → p)
    (hd : (f <$> done).prop x → p) : p := by
  simp only [matchStep, Iteration.prop_map, Iteration.prop_bind] at h
  obtain ⟨c, rfl, _, h, h'⟩ := h
  split at h
  · exact hy _ _ h' ⟨c, rfl, h⟩
  · exact hs _ h' ⟨c, rfl, h⟩
  · exact hd ⟨c, rfl, h⟩

theorem prop_successor_matchStep' {α β γ : Type u} {m} [Monad m] [Iterator α m β] {it : α} {yield skip done}
    {f : γ → δ} {x : δ}
    (h : (f <$> matchStep (γ := γ) it yield skip done).prop x) :
    (∃ it' b, Iterator.yielded it it' b ∧ (f <$> yield it' b).prop x) ∨
    (∃ it', Iterator.skipped it it' ∧ (f <$> skip it').prop x) ∨
    (Iterator.finished it ∧ (f <$> done).prop x) := by
  simp only [Iteration.prop_map, matchStep, Iteration.prop_bind] at h
  obtain ⟨c, rfl, _, h, h'⟩ := h
  split at h
  · exact Or.inl ⟨_, _, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inl ⟨_, ‹_›, ⟨c, rfl, h⟩⟩
  · exact Or.inr <| Or.inr ⟨‹_›, ⟨c, rfl, h⟩⟩

-- theorem FiniteIteratorWF.lt_of_prop_yield {α β : Type u} {m} [Monad m] {it it' : α} {b : β} [Iterator α m β] :
--     (Iteration.step it).prop (.yield it' b ⟨⟩) → (finiteIteratorWF it').lt (finiteIteratorWF it) :=
--   fun h => Or.inl ⟨b, h⟩

-- theorem FiniteIteratorWF.lt_of_prop_skip {α β : Type u} {m} [Monad m] {it it' : α} [Iterator α m β] :
--     (Iteration.step it).prop (.skip it' ⟨⟩) → (finiteIteratorWF it').lt (finiteIteratorWF it) :=
--   fun h => Or.inr h

theorem FiniteIteratorWF.lt_iff_successor {α β : Type u} {m} [Monad m] [Iterator α m β] {it it' : FiniteIteratorWF α} :
    it'.lt it ↔ (IterStep.successor <$> Iteration.step it.inner).prop (some it'.inner) := by
  simp only [FiniteIteratorWF.lt, Functor.map, Iteration.bind, Iteration.pure, Function.comp_apply,
    Iteration.step]
  apply Iff.intro
  · intro h
    obtain ⟨b, h⟩ | h := h
    · refine ⟨.yield it'.inner b h, rfl, h⟩
    · refine ⟨.skip it'.inner h, rfl, h⟩
  · intro h
    obtain ⟨c, h, h'⟩ := h
    split at h'
    · simp only [IterStep.successor, Option.some.injEq] at h
      exact h ▸ Or.inl ⟨_, h'⟩
    · simp only [IterStep.successor, Option.some.injEq] at h
      exact h ▸ Or.inr h'
    · simp only [IterStep.successor, reduceCtorEq] at h

def rel [Iterator α m β] [Iterator α' m β'] : FlatMap α f → FlatMap α f → Prop :=
  FlatMap.lex f (InvImage FiniteIteratorWF.lt finiteIteratorWF) (InvImage FiniteIteratorWF.lt finiteIteratorWF)

theorem descending_step {α β : Type u} [Monad m] [Iterator α m β] {it₁ it₁' : α}
    (h : (IterStep.successor <$> Iteration.step it₁).prop (some it₁')) :
    (finiteIteratorWF it₁').lt (finiteIteratorWF it₁) := by
  simp only [Iteration.prop_map, Iteration.step] at h
  obtain ⟨step, h, h'⟩ := h
  split at h' <;> cases h
  · exact Or.inl ⟨_, h'⟩
  · exact Or.inr h'

theorem successor_skip {α β : Type u} {m : Type u → Type u} [Monad m] [Iterator α m β] {it₁ it₂ : α} :
    (IterStep.successor <$> pure (f := Iteration m) (IterStep.skip it₁ True.intro : RawStep α β)).prop (some it₂) ↔
      it₂ = it₁ := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

theorem successor_yield {α β : Type u} {m : Type u → Type u} [Monad m] [Iterator α m β] {it₁ it₂ : α} {b} :
    (IterStep.successor <$> pure (f := Iteration m) (IterStep.yield it₁ b True.intro : RawStep α β)).prop (some it₂) ↔
      it₂ = it₁ := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

theorem successor_done {α β : Type u} {m : Type u → Type u} [Monad m] [Iterator α m β] {it: α} :
    (IterStep.successor <$> pure (f := Iteration m) (IterStep.done True.intro : RawStep α β)).prop (some it) ↔
      False := by
  simp [Iteration.prop_map, Pure.pure, Iteration.pure, IterStep.successor]

theorem descending_flatMapStepNone {α β α' β' : Type u} {m : Type u → Type u} {f : β → α'}
    [Monad m] [Iterator α m β] [Iterator α' m β']
    {it₁ : α} {it' : FlatMap α f}
    (h : (IterStep.successor <$> flatMapStepNone (f := f) it₁).prop (some it')) :
    (finiteIteratorWF (m := m) it'.it₁).lt (finiteIteratorWF it₁) := by
  simp only [flatMapStepNone] at h
  have := prop_successor_matchStep' h
  obtain ⟨it', b, hy, h⟩ | ⟨it', hs, h⟩ | ⟨hd, h⟩ := this
  · cases successor_skip.mp h
    exact Or.inl ⟨_, hy⟩
  · cases successor_skip.mp h
    exact Or.inr hs
  · simp only [successor_done] at h

theorem descending_flatMapStepSome {α β α' β' : Type u} {m : Type u → Type u} {f : β → α'}
    [Monad m] [Iterator α m β] [Iterator α' m β']
    {it₁ : α} {it₂ : α'} {it' : FlatMap α f}
    (h : (IterStep.successor <$> flatMapStepSome f it₁ it₂).prop (some it')) :
    rel it' { it₁ := it₁, it₂ := some it₂ } := by
  simp only [flatMapStepSome] at h
  obtain ⟨it', b, hy, h⟩ | ⟨it', hs, h⟩ | ⟨hd, h⟩ := prop_successor_matchStep' h
  · cases successor_yield.mp h
    apply FlatMap.lex_of_right
    exact Or.inl ⟨_, hy⟩
  · cases successor_skip.mp h
    apply FlatMap.lex_of_right
    exact Or.inr hs
  · apply FlatMap.lex_of_left
    exact descending_flatMapStepNone h

instance [Monad m] [Iterator α m β] [Iterator α' m β'] [Finite α] [Finite α'] :
    Finite (FlatMap α f) := by
  refine finite_instIterator _ (rel := rel) ?_ ?_
  · sorry
  · intro it it' h
    split at h
    · apply FlatMap.lex_of_left
      exact descending_flatMapStepNone h
    · exact descending_flatMapStepSome h

@[inline]
def Iter.flatMap [Monad m] [Iterator α' m β'] (f : β → α') (it : Iter (α := α) m β) :
    Iter (α := FlatMap (Iter (α := α) m β) f) m β' :=
  toIter <| FlatMap.init it f

end FlatMap
