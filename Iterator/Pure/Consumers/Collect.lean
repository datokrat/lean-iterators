import Iterator.Pure.Basic
import Iterator.Consumers.Collect

@[always_inline, inline]
def Iter.toArray {α : Type w} {β : Type w}
    [Iterator α Id β] [IteratorToArray α Id] (it : Iter (α := α) β) : Array β :=
  it.toIterM.toArray

@[always_inline, inline]
def Iter.reverseToList {α : Type w} {β : Type w}
    [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β) : List β :=
  it.toIterM.reverseToList

@[always_inline, inline]
def Iter.toList {α : Type w} {β : Type w}
    [Iterator α Id β] [IteratorToArray α Id] (it : Iter (α := α) β) : List β :=
  it.toIterM.toList
