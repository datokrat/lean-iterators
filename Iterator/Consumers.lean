/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Wrapper

@[specialize]
def Iterator.forIn {m n} [Monad m] [Monad n] [MonadEvalT m n] {α β γ} [Iterator α m β] [Finite α]
    (it : α) (init : γ) (f : β → γ → n (ForInStep γ)) : n γ := do
  match ← MonadEvalT.monadEval <| Iterator.step it with
  | .yield it' b _ =>
    match ← f b init with
    | .yield c => Iterator.forIn it' c f
    | .done c => return c
  | .skip it' _ => Iterator.forIn (m := m) it' init f
  | .done _ => return init
termination_by finiteIteratorWF it

instance {m} [Monad m] [Monad n] [MonadEvalT m n] {α β} [Iterator α m β] [Finite α] :
    ForIn n α β where
  forIn := Iterator.forIn

@[specialize]
def Iterator.fold {m n} [Monad m] [Monad n] [MonadEvalT m n] {α β γ} [Iterator α m β] [Finite α]
    (f : γ → β → n γ) (init : γ) (it : α) : n γ := do
  match ← MonadEvalT.monadEval <| Iterator.step it with
  | .yield it' b _ => Iterator.fold f (← f init b) it'
  | .skip it' _ => Iterator.fold f init it'
  | .done _ => return init
termination_by finiteIteratorWF it

@[inline]
def Iter.fold {m n} [Monad m] [Monad n] [MonadEvalT m n] {α β γ} [Iterator α m β] [Finite α]
    (f : γ → β → n γ) (init : γ) (it : Iter (α := α) m β) : n γ :=
  Iterator.fold f init it.inner

-- TODO: more universe polymorphism without making this too inconvenient
@[inline]
def Iterator.toArray [Monad m] {α β : Type u} [Iterator α m β] [Finite α] (it : α) : m (Array β) :=
  go it #[]
where
  @[specialize]
  go [Finite α] (it : α) a := do
    match ← Iterator.step it with
    | .yield it' b _ => go it' (a.push b)
    | .skip it' _ => go it' a
    | .done _ => return a
  termination_by finiteIteratorWF it

@[inline]
def Iter.toArray [Monad m] {α β : Type u} [Iterator α m β] [Finite α] (it : Iter (α := α) m β) : m (Array β) :=
  Iterator.toArray it

@[inline]
def Iterator.reverseToList [Monad m] {α β : Type u} [Iterator α m β] [Finite α] (it : α) : m (List β) :=
  go it []
where
  @[specialize]
  go [Finite α] (it : α) bs := do
    match ← Iterator.step it with
    | .yield it' b _ => go it' (b :: bs)
    | .skip it' _ => go it' bs
    | .done _ => return bs
  termination_by finiteIteratorWF it

@[inline]
def Iter.reverseToList [Monad m] {α β : Type u} [Iterator α m β] [Finite α] (it : Iter (α := α) m β) : m (List β) :=
  Iterator.reverseToList it

@[inline]
def Iterator.toList [Monad m] {α β : Type u} [Iterator α m β] [Finite α] (it : α) : m (List β) :=
  Array.toList <$> Iterator.toArray it

@[inline]
def Iter.toList [Monad m] {α β : Type u} [Iterator α m β] [Finite α] (it : Iter (α := α) m β) : m (List β) :=
  Iterator.toList it

@[inline]
def Iterator.drain [Monad m] [Iterator α m β] [Finite α] (it : α) : m PUnit := do
  match ← Iterator.step it with
  | .yield it' _ _ => Iterator.drain it'
  | .skip it' _ => Iterator.drain it'
  | .done _ => return ⟨⟩
  termination_by finiteIteratorWF it

@[inline]
def Iter.drain [Monad m] [Iterator α m β] [Finite α] (it : Iter (α := α) m β) : m PUnit :=
  Iterator.drain it.inner
