prelude
import Iterator.Combinators.Monadic.Take
import Iterator.Pure

@[always_inline, inline]
def Iter.take {α : Type w} {β : Type v} (n : Nat) (it : Iter (α := α) β) :
    Iter (α := Take α Id β) β :=
  it.toIterM.take n |>.toPureIter
