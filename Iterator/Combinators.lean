/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper
import Iterator.AbstractIteration
import Iterator.IteratorMorphism

section FilterMapH

universe u' v' u v

structure FilterMapH (α : Type u) {β : Type v} {m : Type max u v → Type max u v} [Iterator α m β]
    {β' : Type v'} (f : β → Option β') {n : Type max u u' v v' → Type max u u' v v'}
    (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') : Type max u u' v where
  inner : α

variable {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m] [Iterator α m β]
    {β' : Type v'} {f : β → Option β'} {n : Type max u u' v v' → Type max u u' v v'} [Monad n]
    {mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ'}

instance : Iterator (FilterMapH.{u'} α f mf) n β' :=
  Iteration.instIterator fun it =>
    matchStepH.{max u' v'} (fun {δ δ'} => mf (δ := δ) (δ' := δ')) it.inner
      (fun it' b => match f b with
        | none => pure <| .skip ⟨it'⟩ ⟨⟩
        | some c => pure <| .yield ⟨it'⟩ c ⟨⟩)
      (fun it' => pure <| .skip ⟨it'⟩ ⟨⟩)
      (pure <| .done ⟨⟩)

instance [Finite α] : Finite (FilterMapH.{u'} α f mf) := by
  refine finite_instIterator (α := FilterMapH.{u'} α f mf) (β := β') (m := n) (rel := ?_) ?_ ?_ ?_
  · exact InvImage FiniteIteratorWF.lt (finiteIteratorWF ∘ FilterMapH.inner)
  · apply InvImage.wf
    exact Finite.wf
  · intro it it' h
    replace h := prop_successor_matchStepH h
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
def Iterator.filterMapH [Monad n] [Monad m] [Iterator α m β] (f : β → Option β') (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') (it : α) :
    FilterMapH.{u'} α f mf :=
  ⟨it⟩

@[inline]
def Iter.filterMapH [Monad n] [Monad m] [Iterator α m β] (f : β → Option β') (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :
    Iter (α := FilterMapH.{u'} α f mf) n β' :=
  toIter <| Iterator.filterMapH f mf it.inner

@[inline]
def Iter.mapH [Monad n] [Monad m] [Iterator α m β] (f : β → β') (mf : ∀ ⦃δ : Type max u v⦄ ⦃δ' : Type max u v u' v'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :
    Iter (α := FilterMapH.{u'} α (fun b => some <| f b) mf) n β' :=
  it.filterMapH (fun b => some <| f b) mf

end FilterMapH

section FilterMap

-- todo: more universe polymorphism
variable {m : Type max u v → Type max u v} {α : Type u} {β γ : Type v} {f : β → Option γ}

variable (α) in
structure FilterMap (f : β → Option γ) where
  inner : α

@[inline]
def Iter.filterMap [Iterator α m β] [Monad m] (f : β → Option γ) (it : Iter (α := α) m β) :=
  it.filterMapH f (m := m) (fun ⦃_ _⦄ => Functor.map)

@[inline]
def Iter.map [Iterator α m β] [Monad m] (f : β → γ) (it : Iter (α := α) m β) :=
  it.filterMap (some ∘ f)

@[inline]
def Iter.filter [Iterator α m β] [Monad m] (f : β → Bool) (it : Iter (α := α) m β) :=
  it.filterMap (fun x => if f x then some x else none)

end FilterMap

section ULiftState

universe u' v u

variable {α : Type u} {β : Type v}
  {m : Type (max u v) → Type (max u v)}
  {n : Type (max u v u') → Type (max u v u')}
  {f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ'}

structure IterULiftState (α : Type u) (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') : Type (max u u') where
  down : α

@[inline]
def IterULiftState.up (it : α) (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') : IterULiftState.{u'} α f :=
  ⟨it⟩

instance [Monad n] [Iterator α m β] : Iterator (IterULiftState.{u'} α f) n β where
  yielded it it' b := Iterator.yielded it.down it'.down b
  skipped it it' := Iterator.skipped it.down it'.down
  finished it := Iterator.finished it.down
  step it := do
    let s ← f ULift.up.{u'} (Iterator.step it.down)
    return match s.down with
    | .yield it' b h => .yield ⟨it'⟩ b h
    | .skip it' h => .skip ⟨it'⟩ h
    | .done h => .done h

def IterULiftState.downMorphism [Monad n] [Iterator α m β] :
    IteratorMorphism (IterULiftState.{u'} α f) α where
  mapIterator := IterULiftState.down
  mapValue := id
  preserves_yielded := Iff.rfl
  preserves_skipped := Iff.rfl
  preserves_finished := Iff.rfl

def Iter.uLiftState [Monad n] [Iterator α m β] (f : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → n δ') (it : Iter (α := α) m β) :
    Iter (α := IterULiftState.{u', v, u} α f) n β :=
  toIter ⟨it.inner⟩

instance [Monad n] [Iterator α m β] [Finite α] : Finite (IterULiftState.{u'} α f) :=
  IterULiftState.downMorphism.pullbackFinite

end ULiftState

section FlatMap

section Def

universe u v

variable {α α': Type (max u v)} {β : Type v}
  {m : Type (max u v) → Type (max u v)}
  [Iterator α m α'] [Iterator α' m β]

structure Flatten (α : Type max u v) {α' : Type max u v} {m : Type max u v → Type max u v} [Iterator α m α'] where
  it₁ : α
  it₂ : Option α'

@[inline]
def Flatten.init {α α' : Type max u v} {m : Type max u v → Type max u v} [Iterator α m α'] (it : α) : Flatten.{u, v} α :=
  ⟨it, none⟩

@[inline]
def flatMapStepNone [Monad m] [Iterator α m α'] [Iterator α' m β] (it₁ : α) :
    Iteration m (RawStep (Flatten.{u, v} α) β) :=
  matchStep it₁
    (fun it₁' b => pure <| .skip { it₁ := it₁', it₂ := some b } ⟨⟩)
    (fun it₁' => pure <| .skip { it₁ := it₁', it₂ := none } ⟨⟩)
    (pure <| .done ⟨⟩)

variable (f) in
@[inline]
def flatMapStepSome [Monad m] [Iterator α m α'] [Iterator α' m β] (it₁ : α) (it₂ : α') :
    Iteration m (RawStep (Flatten.{u, v} α) β) :=
  matchStep.{max u v, v} it₂
    (fun it₂' b => pure <| .yield { it₁ := it₁, it₂ := some it₂' } b ⟨⟩)
    (fun it₂' => pure <| .skip { it₁ := it₁, it₂ := some it₂' } ⟨⟩)
    (flatMapStepNone it₁)

instance [Monad m] [Iterator α m α'] [Iterator α' m β] : Iterator (Flatten.{u, v} α) m β :=
  Iteration.instIterator fun
    | { it₁, it₂ := none } => flatMapStepNone it₁
    | { it₁, it₂ := some it₂ } => flatMapStepSome it₁ it₂

instance [Monad m] [Iterator α m α'] [Iterator α' m β] : Finite (Flatten.{u, v} α) := sorry

@[inline]
def Iter.flatten [Monad m] [i₁ : Iterator α m α'] [i₂ : Iterator α' m β] (it : Iter (α := α) m α') :=
  toIter <| Flatten.init it.inner

end Def

section UniverseMonomorphic

universe u

variable {α α' β' : Type u} {m : Type u → Type u}

def FlatMap.lex [Iterator α m α'] (r₁ : α → α → Prop) (r₂ : α' → α' → Prop) : Flatten.{u, u} α → Flatten.{u, u} α → Prop :=
  InvImage (Prod.Lex r₁ (Option.lt r₂)) (fun it => (it.it₁, it.it₂))

theorem FlatMap.lex_of_left [Iterator α m α'] {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it it'}
    (h : r₁ it'.it₁ it.it₁) : FlatMap.lex r₁ r₂ it' it :=
  Prod.Lex.left _ _ h

theorem FlatMap.lex_of_right [Iterator α m α'] {r₁ : α → α → Prop} {r₂ : α' → α' → Prop} {it₁ it₂ it₂'}
    (h : r₂ it₂' it₂) : FlatMap.lex r₁ r₂ ⟨it₁, it₂'⟩ ⟨it₁, it₂⟩ :=
  Prod.Lex.right _ h

def rel [Iterator α m α'] [Iterator α' m β] : Flatten.{u, u} α → Flatten.{u, u} α → Prop :=
  FlatMap.lex (InvImage FiniteIteratorWF.lt finiteIteratorWF) (InvImage FiniteIteratorWF.lt finiteIteratorWF)

theorem descending_flatMapStepNone
    [Monad m] [Iterator α m α'] [Iterator α' m β] {it₁ : α} {it' : Flatten α}
    (h : ((ULift.up ∘ IterStep.successor) <$> flatMapStepNone it₁).prop (ULift.up <| some it')) :
    (finiteIteratorWF (m := m) it'.it₁).lt (finiteIteratorWF it₁) := by
  simp only [flatMapStepNone] at h
  have := prop_successor_matchStep h
  obtain ⟨it'', b, hy, h⟩ | ⟨it'', hs, h⟩ | ⟨hd, h⟩ := this
  · cases up_successor_skip.mp h
    exact Or.inl ⟨_, hy⟩
  · cases up_successor_skip.mp h
    exact Or.inr hs
  · cases up_successor_done.mp h

theorem descending_flatMapStepSome
    [Monad m] [Iterator α m α'] [Iterator α' m β] {it₁ : α} {it₂ : α'} {it' : Flatten α}
    (h : ((ULift.up ∘ IterStep.successor) <$> flatMapStepSome it₁ it₂).prop (ULift.up <| some it')) :
    rel it' { it₁ := it₁, it₂ := some it₂ } := by
  simp only [flatMapStepSome] at h
  obtain ⟨it', b, hy, h⟩ | ⟨it', hs, h⟩ | ⟨hd, h⟩ := prop_successor_matchStep h
  · cases up_successor_yield.mp h
    apply FlatMap.lex_of_right
    exact Or.inl ⟨_, hy⟩
  · cases up_successor_skip.mp h
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

instance [Monad m] [Iterator α m α'] [Iterator α' m β] [Finite α] [Finite α'] :
    Finite (Flatten α) := by
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

/-

Plan:

1. α ~> β, f : β -dependent-> α', α' ~> β', all polymorphic with heterogeneous monads and potentially dependent
2. convert f into a non-dependent function using some internal helper
2. use `mapH` ("heterogeneous"):
  1. apply the non-dependent function to the inner iterator, again using `mapH`
  1. lift the inner iterator so that it uses the right monad and the right universes (this might not be necessary)
3. ulift `α`
4. use the monomorphic `flatten`

-/

section General

section Helper
set_option pp.universes true
structure SigmaIterator (β : Type u) (α : β → Type max u v) where
  b : β
  inner : α b

instance {β : Type u} {α : β → Type max u v} {γ : Type w}
    {m : Type max u v w → Type max u v w} [Monad m]
    [i : ∀ b, Iterator (α b) m γ] : Iterator (SigmaIterator β α) m γ :=
  Iteration.instIterator fun it => do
    matchStep it.inner
      (fun it' c => pure <| .yield ⟨it.b, it'⟩ c ⟨⟩)
      (fun it' => pure <| .skip ⟨it.b, it'⟩ ⟨⟩)
      (pure <| .done ⟨⟩)

end Helper

section Const

variable {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m]
  {α' : Type u'} {β' : Type v'} {n : Type max u' v' → Type max u' v'} [Monad n]
  {p : Type max u v u' v' → Type max u v u' v'} [Monad p]
  {fm : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → p δ'} {fn : ∀ ⦃δ δ'⦄, (δ → δ') → n δ → p δ'}
  {f : (b : β) → α'}

@[inline]
def Iter.flatMapH (f : β → α') [Iterator α m β] (it : Iter (α := α) m β) [Iterator α' n β'] [Monad m] [Monad n] [Monad p]
    (fm : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → p δ') (fn : ∀ ⦃δ δ'⦄, (δ → δ') → n δ → p δ') :=
  it.mapH (fun b => IterULiftState.up.{max u v u' v'} (f b) fn) fm |>.flatten

end Const

section Dependent

variable {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m]
  {α' : β → Type u'} {β' : Type v'} {n : Type max u' v' → Type max u' v'} [Monad n]
  {p : Type max u v u' v' → Type max u v u' v'} [Monad p]
  {fm : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → p δ'} {fn : ∀ ⦃δ δ'⦄, (δ → δ') → n δ → p δ'}
  {f : (b : β) → α' b}

@[inline]
def Iter.flatMapHD (f : (b : β) → α' b) [Iterator α m β] (it : Iter (α := α) m β) [∀ b, Iterator (α' b) n β'] [Monad m] [Monad n] [Monad p]
    (fm : ∀ ⦃δ δ'⦄, (δ → δ') → m δ → p δ') (fn : ∀ ⦃δ δ'⦄, (δ → δ') → n δ → p δ') :
    Iter (α := Flatten.{max (max u v u' v') v'}
        (FilterMapH.{max u v u' v'} α (fun b => some (SigmaIterator.mk b (IterULiftState.up.{max u v u' v', v', u'} (f b) fn))) fm)) p β' :=
  it.mapH (fun b => SigmaIterator.mk.{v, max u v u' v'} b (IterULiftState.up.{max u v u' v', v', u'} (f b) fn)) fm |>.flatten

end Dependent

section Simple

@[inline]
def Iter.flatMap {α : Type u} {β : Type v} {m : Type max u v → Type max u v} [Monad m] [Iterator α m β]
    {α' : Type u} {β' : Type v} [Iterator α' m β'] (f : β → α') (it : Iter (α := α) m β) :=
  Iter.flatMapH.{u, v, u, v} f it (fun ⦃_ _⦄ => Functor.map) (fun ⦃_ _⦄ => Functor.map)

end Simple

end General

end FlatMap
