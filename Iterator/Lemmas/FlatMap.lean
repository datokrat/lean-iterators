/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Lemmas.Monadic.FlatMap
import Iterator.Combinators.FlatMap
import Iterator.Consumers.Collect

theorem Iter.toList_flatMap {α α₂ : Type w} {β : Type w}
    {γ : Type w} [Iterator α Id β] [Iterator α₂ Id γ] [Finite α Id] [Finite α₂ Id]
    [IteratorToArray α Id] [IteratorToArray α₂ Id]
    [LawfulIteratorToArray α Id] [LawfulIteratorToArray α₂ Id]
    {f : β → Iter (α := α₂) γ} {it : Iter (α := α) β} :
    (it.flatMap f).toList = it.toList.flatMap (f · |>.toList) :=
  IterM.toList_flatMap_of_pure
