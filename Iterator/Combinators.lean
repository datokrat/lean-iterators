/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper
import Iterator.AbstractIteration
import Iterator.IteratorMorphism

section FilterMap

-- todo: more universe polymorphism
variable {m : Type max u v → Type max u v} {α : Type u} {β γ : Type v} {f : β → Option γ}

variable (α) in
structure FilterMap (f : β → Option γ) where
  inner : α

--def stepFn [Iterator α m β] [Monad m] (it : FilterMap α f) : Iteration m (FilterMap.{v, u} α f) := sorry

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

structure FlatMap (α) (f : β → α') where
  it₁ : α
  it₂ : Option α'

@[inline]
def FlatMap.init (it : α) (f : β → α') : FlatMap α f :=
  ⟨it, none⟩

@[inline]
def flatMapStepNone [Monad m] [Iterator α m β] [Iterator α' m β'] (f : β → α') (it₁ : α) :
    Iteration m (RawStep (FlatMap α f) β') :=
  matchStep.{u, u} it₁
    (fun it₁' b => pure <| .skip { it₁ := it₁', it₂ := some (f b) } ⟨⟩)
    (fun it₁' => pure <| .skip { it₁ := it₁', it₂ := none } ⟨⟩)
    (pure <| .done ⟨⟩)

@[inline]
def flatMapStepSome [Monad m] [Iterator α m β] [Iterator α' m β'] (f : β → α') (it₁ : α) (it₂ : α') :
    Iteration m (RawStep (FlatMap α f) β') :=
  matchStep.{u, u} it₂
    (fun it₂' b => pure <| .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩)
    (fun it₂' => pure <| .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩)
    (flatMapStepNone f it₁)

instance [Monad m] [Iterator α m β] [Iterator α' m β'] : Iterator (FlatMap α f) m β' :=
  Iteration.instIterator fun
    | { it₁, it₂ := none } => flatMapStepNone f it₁
    | { it₁, it₂ := some it₂ } => flatMapStepSome f it₁ it₂

def FlatMap.lex (f : β → α') (r₁ : α → α → Prop) (r₂ : α' → α' → Prop) : FlatMap α f → FlatMap α f → Prop :=
  InvImage (Prod.Lex r₁ (Option.lt r₂)) (fun it => (it.it₁, it.it₂))

theorem FlatMap.lex_of_left {f : β → α'} {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it it'}
    (h : r₁ it'.it₁ it.it₁) : FlatMap.lex f r₁ r₂ it' it :=
  Prod.Lex.left _ _ h

theorem FlatMap.lex_of_right {f : β → α'} {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it₁ it₂ it₂'}
    (h : r₂ it₂' it₂) : FlatMap.lex f r₁ r₂ ⟨it₁, it₂'⟩ ⟨it₁, it₂⟩ :=
  Prod.Lex.right _ h

def rel [Iterator α m β] [Iterator α' m β'] : FlatMap α f → FlatMap α f → Prop :=
  FlatMap.lex f (InvImage FiniteIteratorWF.lt finiteIteratorWF) (InvImage FiniteIteratorWF.lt finiteIteratorWF)

theorem descending_flatMapStepNone {α β α' β' : Type u} {m : Type u → Type u} {f : β → α'}
    [Monad m] [Iterator α m β] [Iterator α' m β']
    {it₁ : α} {it' : FlatMap α f}
    (h : (IterStep.successor <$> flatMapStepNone (f := f) it₁).prop (some it')) :
    (finiteIteratorWF (m := m) it'.it₁).lt (finiteIteratorWF it₁) := by
  simp only [flatMapStepNone] at h
  have := prop_successor_matchStep h
  obtain ⟨it', b, hy, h⟩ | ⟨it', hs, h⟩ | ⟨hd, h⟩ := this
  · cases successor_skip.mp h
    exact Or.inl ⟨_, hy⟩
  · cases successor_skip.mp h
    exact Or.inr hs
  · simp only [successor_done.{u, u}] at h

theorem descending_flatMapStepSome {α β α' β' : Type u} {m : Type u → Type u} {f : β → α'}
    [Monad m] [Iterator α m β] [Iterator α' m β']
    {it₁ : α} {it₂ : α'} {it' : FlatMap α f}
    (h : (IterStep.successor <$> flatMapStepSome f it₁ it₂).prop (some it')) :
    rel it' { it₁ := it₁, it₂ := some it₂ } := by
  simp only [flatMapStepSome] at h
  obtain ⟨it', b, hy, h⟩ | ⟨it', hs, h⟩ | ⟨hd, h⟩ := prop_successor_matchStep h
  · cases successor_yield.mp h
    apply FlatMap.lex_of_right
    exact Or.inl ⟨_, hy⟩
  · cases successor_skip.mp h
    apply FlatMap.lex_of_right
    exact Or.inr hs
  · apply FlatMap.lex_of_left
    exact descending_flatMapStepNone h

theorem Option.wellFounded_lt {α} {rel : α → α → Prop} (h : WellFounded rel) : WellFounded (Option.lt rel) := by
  refine ⟨?_⟩
  intro x
  have hn : Acc (Option.lt rel) none := by
    refine Acc.intro none ?_
    intro y hyx
    cases y <;> cases hyx
  cases x
  · exact hn
  · rename_i x
    induction h.apply x
    rename_i x' h ih
    refine Acc.intro _ ?_
    intro y hyx'
    cases y
    · exact hn
    · exact ih _ hyx'

instance [Monad m] [Iterator α m β] [Iterator α' m β'] [Finite α] [Finite α'] :
    Finite (FlatMap α f) := by
  refine finite_instIterator _ (rel := rel) ?_ ?_
  · simp only [rel, FlatMap.lex]
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact InvImage.wf _ Finite.wf
    · exact Option.wellFounded_lt <| InvImage.wf _ Finite.wf
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
