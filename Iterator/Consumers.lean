/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper

@[specialize]
def Iter.forIn {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [Monad n] [MonadLiftT m n]
    {α : Type u} {β : Type v} {γ : Type w}
    {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β]
    (it : Iter (α := α) m β) (init : γ) (f : β → γ → n (ForInStep γ)) : n γ := do
  let x : n it.LiftedStep := it.stepH.mapH (·.lift) |>.run
  match ← x with
  | .yield it' b _ =>
    match ← f (ComputableSmall.down b) init with
    | .yield c => it'.forIn c f
    | .done c => return c
  | .skip it' _ => it'.forIn init f
  | .done _ => return init
termination_by it.terminationByFinite

instance {m} [Monad m] [Monad n] [MonadLiftT m n] {α β} [Iterator α m β] [Finite α m] :
    ForIn n (Iter (α := α) m β) β where
  forIn := Iter.forIn

@[specialize]
def Iter.fold {m : Type w → Type w'} {n : Type w → Type w'} [Monad m] [Monad n] [MonadLiftT m n]
    {α : Type u} {β : Type v} {γ : Type w} {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β]
    (f : γ → β → n γ) (init : γ) (it : Iter (α := α) m β) : n γ := do
  let step : n it.LiftedStep := it.stepH.mapH (·.lift) |>.run
  match ← step with
  | .yield it' b _ => it'.fold f (← f init (ComputableSmall.down b))
  | .skip it' _ => it'.fold f init
  | .done _ => return init
termination_by it.terminationByFinite

@[inline]
def Iter.toArrayH {α : Type u} {m : Type w → Type w'} [Monad m] {β : Type v}
    {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{w} α} [ComputableUnivLE.{v, w}] (it : Iter (α := α) m β) : CodensityT m (Array β) :=
  (CodensityT.eval <| go it #[]).mapH ComputableSmall.down
where
  @[specialize]
  go [Monad m] [Finite α m] it a : m (ComputableSmall.Lift.{w} (Array β)) := do
    let step ← it.stepH.mapH (·.lift) |>.run
    match step with
      | .yield it' b _ => go it' (a.push <| ComputableSmall.down b)
      | .skip it' _ => go it' a
      | .done _ => return ComputableSmall.up a
  termination_by it.terminationByFinite

@[inline]
def Iter.toArray {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{v} α} (it : Iter (α := α) m β) : m (Array β) :=
  go it #[]
where
  @[specialize]
  go [Monad m] [Finite α m] it a := do
    match ← it.step with
    | .yield it' b _ => go it' (a.push b)
    | .skip it' _ => go it' a
    | .done _ => return a
  termination_by it.terminationByFinite

@[inline]
def Iter.reverseToList {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{v} α} (it : Iter (α := α) m β) : m (List β) :=
  go it []
where
  @[specialize]
  go [Finite α m] it bs := do
    match ← it.step with
    | .yield it' b _ => go it' (b :: bs)
    | .skip it' _ => go it' bs
    | .done _ => return bs
  termination_by it.terminationByFinite

@[inline]
def Iter.toList {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{v} α} (it : Iter (α := α) m β) : m (List β) :=
  Array.toList <$> it.toArray

@[specialize]
def Iter.drain {α : Type u} {m : Type w → Type w'} {β : Type v} [Monad m]
    {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall α} (it : Iter (α := α) m β) : m PUnit := do
  it.stepH _ (match · with
  | .yield it' _ _ => it'.drain
  | .skip it' _ => it'.drain
  | .done _ => return ⟨⟩)
termination_by it.terminationByFinite
