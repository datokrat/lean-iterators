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

-- @[inline]
-- def Iteration.instIterator' {α : Type u} {β : Type v} [Functor m] (stepFn : α → Iteration m (RawStep α β)) : Iterator α m β where

instance [Iterator α m β] [Monad m] : Iterator (FilterMap α f) m γ :=
  letI := Iterator.uLiftUp α
  Iteration.instIterator fun it => do
    matchStep it.inner
      (fun it' b => pure <| match f b with
          | none => IterStep.skip ⟨it'⟩ ⟨⟩
          | some c => IterStep.yield ⟨it'⟩ c ⟨⟩)
      (fun it' => pure <| IterStep.skip ⟨it'⟩ ⟨⟩)
      (pure <| IterStep.done ⟨⟩)

instance [Iterator α m β] [Monad m] [Finite α] : Finite (FilterMap α f) := by
  refine finite_instIterator (α := FilterMap α f) (β := γ) (m := m) (rel := ?_) ?_ ?_ ?_
  · exact InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ FilterMap.inner)
  · apply InvImage.wf
    exact Finite.wf
  · intro it it' h
    replace h := prop_successor_matchStep h
    obtain ⟨it'', b, h, h'⟩ | ⟨it'', h, h'⟩ | ⟨h, h'⟩ := h
    · split at h'
      · cases up_successor_skip.mp h'
        apply Or.inl ⟨_, h⟩
      · cases up_successor_yield.mp h'
        apply Or.inl ⟨_, h⟩
    · cases up_successor_skip.mp h'
      exact Or.inr h
    · cases up_successor_done.mp h'

@[inline]
def Iter.filterMap [Iterator α m β] [Monad m] (f : β → Option γ) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) f) m γ :=
  toIter ⟨it⟩

@[inline]
def Iter.map [Iterator α m β] [Monad m] (f : β → γ) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) (some ∘ f)) m γ :=
  toIter ⟨it⟩

@[inline]
def Iter.filter [Iterator α m β] [Monad m] (f : β → Bool) (it : Iter (α := α) m β) :
    Iter (α := FilterMap (Iter (α := α) m β) (fun x => if f x then some x else none)) m β :=
  toIter ⟨it⟩

end FilterMap

section ULiftState

universe u' v u

variable {α : Type u} {β : Type v}
  {m : Type (max u v) → Type (max u v)}
  {n : Type (max u v u') → Type (max u v u')}
  {f : ∀ {δ}, m δ → n (ULift.{u'} δ)}

structure IterULiftState (α : Type u) (f : ∀ {δ}, m δ → n (ULift.{u'} δ)) : Type (max u v u') where
  down : α

@[inline]
def IterULiftState.up (it : α) : IterULiftState α f :=
  ⟨it⟩

instance [Monad n] [Iterator α m β] : Iterator (IterULiftState.{u'} α f) n β where
  yielded it it' b := Iterator.yielded it.down it'.down b
  skipped it it' := Iterator.skipped it.down it'.down
  finished it := Iterator.finished it.down
  step it := do
    let s ← f (Iterator.step it.down)
    return match s.down with
    | .yield it' b h => .yield ⟨it'⟩ b h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done h => .done h

def IterULiftState.downMorphism [Monad n] [Iterator α m β] :
    IteratorMorphism (IterULiftState α f) α where
  mapIterator := IterULiftState.down
  mapValue := id
  preserves_yielded := Iff.rfl
  preserves_skipped := Iff.rfl
  preserves_finished := Iff.rfl

instance [Monad n] [Iterator α m β] [Finite α] : Finite (IterULiftState α f) :=
  IterULiftState.downMorphism.pullbackFinite

end ULiftState

section FlatMap

section Def

universe u v v'

variable {α α': Type (max u v v')} {β : Type v} {β' : Type v'}
  {m : Type (max u v v') → Type (max u v v')}
  [Iterator α m β] [Iterator α' m β'] {f : β → α'}

structure FlatMap (α : Type u) {α' : Type u} {β : Type v} (f : β → α') where
  it₁ : α
  it₂ : Option α'

@[inline]
def FlatMap.init (it : α) (f : β → α') : FlatMap α f :=
  ⟨it, none⟩

variable (f) in
@[inline]
def flatMapStepNone [Monad m] [Iterator α m β] [Iterator α' m β'] (it₁ : α) :
    Iteration m (RawStep (FlatMap α f) β') :=
  matchStep it₁
    (fun it₁' b => pure <| .skip { it₁ := it₁', it₂ := some (f b) } ⟨⟩)
    (fun it₁' => pure <| .skip { it₁ := it₁', it₂ := none } ⟨⟩)
    (pure <| .done ⟨⟩)

variable (f) in
@[inline]
def flatMapStepSome [Monad m] [Iterator α m β] [Iterator α' m β'] (it₁ : α) (it₂ : α') :
    Iteration m (RawStep (FlatMap α f) β') :=
  matchStep.{max u v v', v'} it₂
    (fun it₂' b => pure <| .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩)
    (fun it₂' => pure <| .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩)
    (flatMapStepNone.{u} f it₁)

instance [Monad m] [Iterator α m β] [Iterator α' m β'] : Iterator (FlatMap α f) m β' :=
  Iteration.instIterator fun
    | { it₁, it₂ := none } => flatMapStepNone.{u} f it₁
    | { it₁, it₂ := some it₂ } => flatMapStepSome.{u} f it₁ it₂

end Def

section UniverseMonomorphic

universe u

variable {α β α' β' : Type u} {m : Type u → Type u} {f : β → α'}

def FlatMap.lex (f : β → α') (r₁ : α → α → Prop) (r₂ : α' → α' → Prop) : FlatMap α f → FlatMap α f → Prop :=
  InvImage (Prod.Lex r₁ (Option.lt r₂)) (fun it => (it.it₁, it.it₂))

theorem FlatMap.lex_of_left {f : β → α'} {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it it'}
    (h : r₁ it'.it₁ it.it₁) : FlatMap.lex.{u} f r₁ r₂ it' it :=
  Prod.Lex.left _ _ h

theorem FlatMap.lex_of_right {f : β → α'} {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it₁ it₂ it₂'}
    (h : r₂ it₂' it₂) : FlatMap.lex.{u} f r₁ r₂ ⟨it₁, it₂'⟩ ⟨it₁, it₂⟩ :=
  Prod.Lex.right _ h

def rel [Iterator α m β] [Iterator α' m β'] : FlatMap α f → FlatMap α f → Prop :=
  FlatMap.lex f (InvImage FiniteIteratorWF.lt finiteIteratorWF) (InvImage FiniteIteratorWF.lt finiteIteratorWF)

theorem descending_flatMapStepNone
    [Monad m] [Iterator α m β] [Iterator α' m β'] {it₁ : α} {it' : FlatMap α f}
    (h : ((ULift.up ∘ IterStep.successor) <$> flatMapStepNone (f := f) it₁).prop (ULift.up <| some it')) :
    (finiteIteratorWF (m := m) it'.it₁).lt (finiteIteratorWF it₁) := by
  simp only [flatMapStepNone] at h
  have := prop_successor_matchStep h
  obtain ⟨it'', b, hy, h⟩ | ⟨it'', hs, h⟩ | ⟨hd, h⟩ := this
  · cases up_successor_skip (α := type_of% it') (β := β') |>.mp h
    exact Or.inl ⟨_, hy⟩
  · cases up_successor_skip (α := FlatMap α f) |>.mp h
    exact Or.inr hs
  · cases up_successor_done (α := FlatMap α f) |>.mp h

theorem descending_flatMapStepSome
    [Monad m] [Iterator α m β] [Iterator α' m β'] {it₁ : α} {it₂ : α'} {it' : FlatMap α f}
    (h : ((ULift.up ∘ IterStep.successor) <$> flatMapStepSome f it₁ it₂).prop (ULift.up <| some it')) :
    rel it' { it₁ := it₁, it₂ := some it₂ } := by
  simp only [flatMapStepSome] at h
  obtain ⟨it', b, hy, h⟩ | ⟨it', hs, h⟩ | ⟨hd, h⟩ := prop_successor_matchStep h
  · cases up_successor_yield (α := FlatMap α f) |>.mp h
    apply FlatMap.lex_of_right
    exact Or.inl ⟨_, hy⟩
  · cases up_successor_skip (α := FlatMap α f) |>.mp h
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
  refine finite_instIterator (m := m) _ (rel := rel) ?_ ?_
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

end UniverseMonomorphic

section Morphisms

end Morphisms

section UniversePolymorphic

universe u v v'

variable {α α': Type (max u v v')} {β : Type v} {β' : Type v'}
  {m : Type (max u v v') → Type (max u v v')}
  [Iterator α m β] [Iterator α' m β'] {f : β → α'}

def FlatMap.universeMonomorphisation : IteratorMorphism (FlatMap α f) (FlatMap

end UniversePolymorphic

#exit

@[inline]
def Iter.flatMap [Monad m] [Iterator α' m β'] (f : β → α') (it : Iter (α := α) m β) :
    Iter (α := FlatMap (Iter (α := α) m β) f) m β' :=
  toIter <| FlatMap.init it f

end FlatMap
