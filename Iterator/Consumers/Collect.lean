/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Iterator.Pure
import Iterator.Consumers.Monadic.Collect
import Iterator.Consumers.Partial

@[always_inline, inline]
def Iter.toArray {α : Type w} {β : Type w}
    [Iterator α Id β] [IteratorToArray α Id] (it : Iter (α := α) β) : Array β :=
  it.toIterM.toArray

@[always_inline, inline]
def Iter.Partial.toArray {α : Type w} {β : Type w}
    [Iterator α Id β] [IteratorToArrayPartial α Id] (it : Iter.Partial (α := α) β) : Array β :=
  it.it.toIterM.allowNontermination.toArray

@[always_inline, inline]
def Iter.toListRev {α : Type w} {β : Type w}
    [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β) : List β :=
  it.toIterM.toListRev

@[always_inline, inline]
def Iter.Partial.toListRev {α : Type w} {β : Type w}
    [Iterator α Id β] (it : Iter.Partial (α := α) β) : List β :=
  it.it.toIterM.allowNontermination.toListRev

@[always_inline, inline]
def Iter.toList {α : Type w} {β : Type w}
    [Iterator α Id β] [IteratorToArray α Id] (it : Iter (α := α) β) : List β :=
  it.toIterM.toList

@[always_inline, inline]
def Iter.Partial.toList {α : Type w} {β : Type w}
    [Iterator α Id β] [IteratorToArrayPartial α Id] (it : Iter.Partial (α := α) β) : List β :=
  it.it.toIterM.allowNontermination.toList
