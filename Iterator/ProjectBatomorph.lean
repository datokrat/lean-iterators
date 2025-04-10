/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/

-- Project Batomorph: super flat iterators, fast as rays

class Iterator (α : Type) (β : outParam Type) where
  fold : α → (δ : Type) → δ → (f : δ → β → δ) → δ

instance : Iterator (List α) α where
  fold it δ d f := it.foldl f d

structure MapI (α : Type) (f : β → β') where
  inner : α

instance [Iterator α β] {f : β → β'} : Iterator (MapI α f) β' where
  fold it _ d g := Iterator.fold it.inner _ d (fun d b => g d (f b))

class PartitionedIterator (γ : Type) (β : outParam Type) where
  foldparts : (δ : Type) → δ → (f : δ → (α : Type) → Iterator α β → (γ → α) → δ) → δ

structure SinglePartition (α : Type) where
  inner : α

instance [Iterator α β] : PartitionedIterator (SinglePartition α) β where
  foldparts _ init f := f init α inferInstance SinglePartition.inner

structure Concatenation (γ γ' : Type) where
  fst : γ
  snd : γ'

structure Map (γ : Type) {β β' : Type} (f : β → β') where
  inner : γ

instance [i : PartitionedIterator γ β] {f : β → β'} : PartitionedIterator (Map γ f) β' where
  foldparts _ init h := i.foldparts _ init (fun d α _ g => h d (MapI α f) inferInstance (fun x => ⟨g x.inner⟩))

instance [i₁ : PartitionedIterator γ β] [i₂ : PartitionedIterator γ' β] : PartitionedIterator (Concatenation γ γ') β where
  foldparts δ init f := i₁.foldparts δ (i₂.foldparts δ init (fun d α i g => f d α i (fun x => g x.snd)))
    (fun d α i g => f d α i (fun x => g x.fst))

@[inline]
def list (x : List α) : SinglePartition (List α) := ⟨x⟩

@[inline]
def concat [PartitionedIterator γ β] [PartitionedIterator γ' β] (it : γ) (it' : γ') : Concatenation γ γ' :=
  ⟨it, it'⟩

@[inline]
def map [PartitionedIterator γ β] (it : γ) (f : β → β') : Map γ f := ⟨it⟩

@[inline]
def fold [i : PartitionedIterator γ β] {δ : Type} (it : γ) (init : δ) (f : δ → β → δ) : δ :=
  i.foldparts δ init (fun d α i g => Iterator.fold (g it) δ d f)

set_option trace.compiler.ir.result true in
def test (l l' : List Nat) : Nat :=
  letI it := concat (map (concat (list l') (list l)) (· * 2)) (list l)
  fold it 0 fun acc x => acc + x
