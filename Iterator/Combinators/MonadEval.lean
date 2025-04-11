/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.AbstractIteration
import Iterator.IteratorMorphism

structure MonadEvalIterator (α : Type u) (m : Type w → Type w') where
  inner : α

instance {α : Type u} {m : Type w → Type w'} {n : Type w → Type w''} {β : Type v} [Iterator α m β] [MonadEvalT m n] :
    Iterator (MonadEvalIterator α m) n β where
  yielded it it' b := Iterator.yielded m it.inner it'.inner b
  skipped it it' := Iterator.skipped m it.inner it'.inner
  finished it := Iterator.finished m it.inner
  step it := by
    let a := it.inner
    exact MonadEvalT.monadEval ((match · with
      | .yield it b h => .yield ⟨it⟩ b h
      | .skip it h => .skip ⟨it⟩ h
      | .done h => .done h) <$> Iterator.step (m := m) it.inner)

@[inline]
def Iter.monadEval [Iterator α m β] (n) [MonadEvalT m n] (it : Iter (α := α) m β) :=
  (toIter n (MonadEvalIterator.mk it.inner (m := m)) : Iter n β)

def MonadEvalIterator.innerMorphism [Iterator α m β] [MonadEvalT m n] :
    IteratorMorphism (MonadEvalIterator α m) n α m where
  mapIterator := MonadEvalIterator.inner
  mapValue := id

instance [Iterator α m β] [Finite α m] [MonadEvalT m n] : Finite (MonadEvalIterator α m) n :=
  MonadEvalIterator.innerMorphism.pullbackFinite
