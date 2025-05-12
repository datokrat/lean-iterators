import Iterator.Basic

structure Iter {α : Type w} (β : Type v) : Type w where
  inner : α

def Iter.toIterM {α : Type w} {β : Type v} (it : Iter (α := α) β) : IterM (α := α) Id β :=
  ⟨it.inner⟩

def IterM.toPureIter {α : Type w} {β : Type v} (it : IterM (α := α) Id β) : Iter (α := α) β :=
  ⟨it.inner⟩
