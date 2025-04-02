/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic

@[specialize]
def Iterator.forIn {m n} [Monad m] [Monad n] [MonadEvalT m n] {α β γ} [Iterator α m β] [Finite α]
    (it : α) (init : γ) (f : β → γ → n (ForInStep γ)) : n γ := do
  match ← MonadEvalT.monadEval <| Iterator.step it with
  | .yield it' b _ =>
    match ← f b init with
    | .yield c => Iterator.forIn it' c f
    | .done c => return c
  | .skip it' _ => Iterator.forIn (m := m) it' init f
  | .done => return init
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
  | .done => return init
termination_by finiteIteratorWF it
