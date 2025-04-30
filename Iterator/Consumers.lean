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
    {_ : Iterator α m β} [Finite α m]
    (it : Iter (α := α) m β) (init : γ) (f : β → γ → n (ForInStep γ)) : n γ := do
  match (← it.stepH).inflate with
  | .yield it' out _ =>
    match ← f out init with
    | .yield c => it'.forIn c f
    | .done c => return c
  | .skip it' _ => it'.forIn init f
  | .done _ => return init
termination_by it.terminationByFinite

instance {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [Monad n] [MonadLiftT m n]
    {α : Type u} {β : Type v} {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{w} α} [ComputableSmall.{w} β] :
    ForIn n (Iter (α := α) m β) β where
  forIn := Iter.forIn

@[specialize]
def Iter.foldM {m : Type w → Type w'} {n : Type w → Type w'} [Monad m] [Monad n] [MonadLiftT m n]
    {α : Type u} {β : Type v} {γ : Type w} {_ : Iterator α m β} [Finite α m]
    (f : γ → β → n γ) (init : γ) (it : Iter (α := α) m β) : n γ := do
  match (← it.stepH).inflate with
  | .yield it' b _ => it'.foldM f (← f init b)
  | .skip it' _ => it'.foldM f init
  | .done _ => return init
termination_by it.terminationByFinite

@[specialize]
def Iter.count {α : Type u} {β : Type v} {_ : Iterator α Id β} [Finite α Id] {_ : ComputableSmall.{0} α}
    (it : Iter (α := α) Id β) : Nat :=
  go it 0
where
  go [Finite α Id] it acc :=
    match it.stepH.inflate with
    | .yield it' _ _ => go it' (acc + 1)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.terminationByFinite

@[specialize]
def Iter.countM {m : Type → Type w'} [Monad m] {α : Type u} {β : Type v} {_ : Iterator α m β} [Finite α m] {_ : ComputableSmall.{0} α}
    (it : Iter (α := α) m β) : m Nat :=
  go it 0
where
  go [Finite α m] it acc := do
    match (← it.stepH).inflate with
      | .yield it' _ _ => go it' (acc + 1)
      | .skip it' _ => go it' acc
      | .done _ => return acc
  termination_by it.terminationByFinite

-- @[inline]
-- def Iter.toArrayH {α : Type u} {m : Type w → Type w'} [Monad m] {β : Type v}
--     {_ : Iterator α m β} [Finite α m] (it : Iter (α := α) m β) : m (Array β) :=
--   (CodensityT.eval <| go it #[]).mapH ComputableSmall.down
-- where
--   @[specialize]
--   go [Monad m] [Finite α m] it a : m (ComputableSmall.Lift.{w} (Array β)) := do
--     let step ← it.stepH.mapH (·.lift) |>.run
--     match step with
--       | .yield it' b _ => go it' (a.push <| ComputableSmall.down b)
--       | .skip it' _ => go it' a
--       | .done _ => return ComputableSmall.up a
--   termination_by it.terminationByFinite

@[inline]
def Iter.toArray {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    {_ : Iterator α m β} [Finite α m] (it : Iter (α := α) m β) : m (Array β) :=
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
    {_ : Iterator α m β} [Finite α m] (it : Iter (α := α) m β) : m (List β) :=
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
    {_ : Iterator α m β} [Finite α m] (it : Iter (α := α) m β) : m (List β) :=
  Array.toList <$> it.toArray

@[specialize]
def Iter.drain {α : Type u} {m : Type w → Type w'} {β : Type v} [Monad m]
    {_ : Iterator α m β} [Finite α m] (it : Iter (α := α) m β) : m PUnit := do
  match (← it.stepH).inflate with
  | .yield it' _ _ => it'.drain
  | .skip it' _ => it'.drain
  | .done _ => return ⟨⟩
termination_by it.terminationByFinite
