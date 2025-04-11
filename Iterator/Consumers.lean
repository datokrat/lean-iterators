/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper
import Iterator.Combinators.MonadEval

@[inline]
def Iter.forIn {m n} [Monad m] [Monad n] [MonadEvalT m n] {α β γ} [Iterator α m β] [Finite α m]
    (it : Iter (α := α) m β) (init : γ) (f : β → γ → n (ForInStep γ)) : n γ := do
  let x : OverT n (IterStep.for m it) := MonadEvalT.monadEval <| Iterator.step it
  match x.f (← x.el) with
  | .yield it' b _ =>
    match ← f b init with
    | .yield c => it'.forIn c f
    | .done c => return c
  | .skip it' _ => it'.forIn init f
  | .done _ => return init
termination_by finiteIteratorWF (m := m) it

instance {m} [Monad m] [Monad n] [MonadEvalT m n] {α β} [Iterator α m β] [Finite α m] :
    ForIn n (Iter (α := α) m β) β where
  forIn := Iter.forIn

@[specialize]
def Iter.fold {m n} [Monad m] [Monad n] [MonadEvalT m n] {α β γ} [Iterator α m β] [Finite α m]
    (f : γ → β → n γ) (init : γ) (it : Iter (α := α) m β) : n γ := do
  let step : OverT n (IterStep.for m it) := MonadEvalT.monadEval <| Iterator.step it
  match step.f (← step.el) with
  | .yield it' b _ => it'.fold f (← f init b)
  | .skip it' _ => it'.fold f init
  | .done _ => return init
termination_by finiteIteratorWF (m := m) it

-- TODO: This may have performance problems because we use bindH and recursion so that
-- Lean won't be able to inline the `OverT` code.
@[inline]
def Iter.toArrayH {α : Type u} {m : Type w → Type w'} [Monad m] {β : Type v}
    [Iterator α m β] [Finite α m] (it : Iter (α := α) m β) : OverT m (Array β) :=
  go it #[]
where
  @[specialize]
  go [Monad m] [Finite α m] it a := do
    let step := Iterator.step (m := m) it
    step.bindH (match · with
      | .yield it' b _ => go it' (a.push b)
      | .skip it' _ => go it' a
      | .done _ => return a)
  termination_by finiteIteratorWF (m := m) it

@[inline]
def Iter.toArray {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    [Iterator α m β] [Finite α m] (it : Iter (α := α) m β) : m (Array β) :=
  go it #[]
where
  @[specialize]
  go [Monad m] [Finite α m] it a := do
    let step := Iterator.step it
    match step.f (← step.el) with
    | .yield it' b _ => go it' (a.push b)
    | .skip it' _ => go it' a
    | .done _ => return a
  termination_by finiteIteratorWF (m := m) it

@[inline]
def Iter.reverseToList {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    [Iterator α m β] [Finite α m] (it : Iter (α := α) m β) : m (List β) :=
  go it []
where
  @[specialize]
  go [Finite α m] it bs := do
    let step := Iterator.step it
    match step.f (← step.el) with
    | .yield it' b _ => go it' (b :: bs)
    | .skip it' _ => go it' bs
    | .done _ => return bs
  termination_by finiteIteratorWF (m := m) it

@[inline]
def Iter.toList {α : Type u} {m : Type v → Type w} [Monad m] {β : Type v}
    [Iterator α m β] [Finite α m] (it : Iter (α := α) m β) : m (List β) :=
  Array.toList <$> it.toArray

@[specialize]
def Iter.drain [Monad m] [Iterator α m β] [Finite α m] (it : Iter (α := α) m β) : m PUnit := do
  let step := Iterator.step it
  match step.f (← step.el) with
  | .yield it' _ _ => it'.drain
  | .skip it' _ => it'.drain
  | .done _ => return ⟨⟩
  termination_by finiteIteratorWF (m := m) it
