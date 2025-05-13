prelude
import Iterator.Combinators.Zip
import Iterator.Pure.Basic

@[always_inline, inline]
def Iter.zip {α₁ : Type w} {β₁: Type v₁} {α₂ : Type w} {β₂ : Type v₂}
    [Iterator α₁ Id β₁] [Iterator α₂ Id β₂]
    (left : Iter (α := α₁) β₁) (right : Iter (α := α₂) β₂) :=
  ((left.toIterM.zipH right.toIterM).toPureIter : Iter (β₁ × β₂))
