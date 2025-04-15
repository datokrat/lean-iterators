/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Basic

class IteratorMorphism (α m α' m') {β β'} [Iterator α m β] [Iterator α' m' β'] where
    mapIterator : Iterator.α' α m → Iterator.α' α' m'
    mapValue : Iterator.β' α m → Iterator.β' α' m'
    preserves_yielded {it it' b} :
      Iterator.yielded (mapIterator it) (mapIterator it') (mapValue b) ↔ Iterator.yielded it it' b := by rfl
    preserves_skipped {it it'} :
      Iterator.skipped (mapIterator it) (mapIterator it') ↔ Iterator.skipped it it' := by rfl
    preserves_finished {it} :
      Iterator.done (mapIterator it) ↔ Iterator.done it := by rfl

variable {α m β α' m' β'} [Iterator α m β] [Iterator α' m' β']

theorem IteratorMorphism.pullbackFinite [Finite α' m'] (φ : IteratorMorphism α m α' m') : Finite α m where
  wf := by
    let pullbackRel : FiniteIteratorWF α m → FiniteIteratorWF α m → Prop :=
      InvImage FiniteIteratorWF.lt (finiteIteratorWF (m := m') ∘ φ.mapIterator ∘ FiniteIteratorWF.inner)
    refine Subrelation.wf (r := pullbackRel) ?_ (InvImage.wf _ Finite.wf)
    · intro x y hlt
      simp only [pullbackRel, InvImage, FiniteIteratorWF.lt, Function.comp_apply,
        finiteIteratorWF] at hlt ⊢
      obtain ⟨b, h⟩ | h := hlt
      · exact Or.inl ⟨φ.mapValue b, φ.preserves_yielded.mpr h⟩
      · exact Or.inr (φ.preserves_skipped.mpr h)

-- @[inline]
-- def Iterator.uLiftUp (α : Type u) {β : Type v} {m} [Functor m] [Iterator α m β] :
--     Iterator (ULift.{v} α) m (ULift.{u} β) where
--   yielded it it' b := Iterator.yielded m it.down it'.down b.down
--   skipped it it' := Iterator.skipped m it.down it'.down
--   finished it := Iterator.finished m it.down
--   step it :=
--     (match · with
--       | .yield it' b h => .yield (.up it') (.up b) h
--       | .skip it' h => .skip (.up it') h
--       | .done h => .done h) <$> Iterator.step it.down

-- @[inline]
-- def Iterator.uLiftDown (α : Type u) {β : Type v} {m : Type (max u v) → Type (max u v)}
--     [Functor m] [Iterator (ULift.{v} α) m (ULift.{u} β)] :
--     Iterator α m β where
--   yielded it it' b := Iterator.yielded m (ULift.up it) (ULift.up it') (ULift.up b)
--   skipped it it' := Iterator.skipped m (ULift.up it) (ULift.up it')
--   finished it := Iterator.finished m (ULift.up it)
--   step it :=
--     (match · with
--       | .yield it' b h => .yield it'.down b.down h
--       | .skip it' h => .skip it'.down h
--       | .done h => .done h) <$> Iterator.step (ULift.up it)

-- class Iterator.ULiftable (α : Type u) {β : Type v} (m)
--     [Iterator α m β] [Iterator (ULift.{v} α) m (ULift.{u} β)] where
--   exists_uLift :
--     ∃ φ : IteratorMorphism α m (ULift.{v} α) m, φ.mapIterator = ULift.up ∧ φ.mapValue = ULift.up

-- attribute [instance] Iterator.uLiftUp in
-- instance {α β m} [Functor m] [Iterator α m β] : Iterator.ULiftable α m where
--   exists_uLift := ⟨⟨ULift.up, ULift.up, Iff.rfl, Iff.rfl, Iff.rfl⟩, rfl, rfl⟩

-- attribute [instance] Iterator.uLiftDown in
-- instance {α : Type u} {β : Type v} {m : Type (max u v) → Type (max u v)}
--     [Functor m] [Iterator (ULift.{v} α) m (ULift.{u} β)] : Iterator.ULiftable α m where
--   exists_uLift := by
--     refine ⟨⟨ULift.up, ULift.up, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [Iterator.yielded, Iterator.skipped, Iterator.finished]

-- def IteratorMorphism.uLiftUp (α : Type u) {β : Type v} {m}
--     [Iterator α m β] [Iterator (ULift.{v} α) m (ULift.{u} β)] [Iterator.ULiftable α m] : IteratorMorphism α m (ULift.{v} α) m where
--   mapIterator := ULift.up
--   mapValue := ULift.up
--   preserves_yielded {it it' b} := by
--     obtain ⟨φ, h, h'⟩ := inferInstanceAs <| Iterator.ULiftable α m
--     simp only [← h, ← h', φ.preserves_yielded]
--   preserves_skipped {it it'} := by
--     obtain ⟨φ, h, h'⟩ := inferInstanceAs <| Iterator.ULiftable α m
--     simp only [← h, ← h', φ.preserves_skipped]
--   preserves_finished {it} := by
--     obtain ⟨φ, h, h'⟩ := inferInstanceAs <| Iterator.ULiftable α m
--     simp only [← h, φ.preserves_finished]

-- def IteratorMorphism.uLiftDown (α : Type u) {β : Type v} {m}
--     [Iterator α m β] [Iterator (ULift.{v} α) m (ULift.{u} β)] [Iterator.ULiftable α m] : IteratorMorphism (ULift.{v} α) m α m where
--   mapIterator := ULift.down
--   mapValue := ULift.down
--   preserves_yielded {it it' b} := by
--     rw (occs := [2]) [← ULift.up_down (b := it), ← ULift.up_down (b := it'), ← ULift.up_down (b := b)]
--     exact (uLiftUp α).preserves_yielded.symm
--   preserves_skipped {it it'}:= by
--     rw (occs := [2]) [← ULift.up_down (b := it), ← ULift.up_down (b := it')]
--     exact (uLiftUp α).preserves_skipped.symm
--   preserves_finished {it} := by
--     rw (occs := [2]) [← ULift.up_down (b := it)]
--     exact (uLiftUp α).preserves_finished.symm
