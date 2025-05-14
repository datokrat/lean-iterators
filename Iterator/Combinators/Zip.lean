prelude
import Iterator.Combinators.Monadic.Zip
import Iterator.Pure

@[always_inline, inline]
def Iter.zip {α₁ : Type w} {β₁: Type w} {α₂ : Type w} {β₂ : Type w}
    [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    (left : Iter (α := α₁) β₁) (right : Iter (α := α₂) β₂) :=
  ((left.toIterM.zip right.toIterM).toPureIter : Iter (β₁ × β₂))
