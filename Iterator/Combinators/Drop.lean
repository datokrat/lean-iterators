prelude
import Iterator.Combinators.Monadic.Drop
import Iterator.Pure

@[always_inline, inline]
def Iter.drop {α : Type w} {β : Type w} (n : Nat) (it : Iter (α := α) β) :
    Iter (α := Drop α Id β) β :=
  it.toIterM.drop n |>.toPureIter
