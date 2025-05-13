prelude
import Iterator.Combinators.Drop
import Iterator.Pure.Basic

@[always_inline, inline]
def Iter.drop {α : Type w} {β : Type v} (n : Nat) (it : Iter (α := α) β) :
    Iter (α := Drop α Id β) β :=
  it.toIterM.drop n |>.toPureIter
