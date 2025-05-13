prelude
import Iterator.Combinators.Monadic.FilterMap
import Iterator.Pure

-- TODO: consistently require or do not require `Iterator` instances
-- in combinators
@[always_inline, inline]
def Iter.filterMap {α : Type w} {β : Type v} {γ : Type v'} [Iterator α Id β]
    (f : β → Option γ) (it : Iter (α := α) β) :=
  ((it.toIterM.filterMapH f).toPureIter : Iter γ)

@[always_inline, inline]
def Iter.filter {α : Type w} {β : Type v} [Iterator α Id β]
    (f : β → Bool) (it : Iter (α := α) β) :=
  ((it.toIterM.filter f).toPureIter : Iter β)

@[always_inline, inline]
def Iter.map {α : Type w} {β : Type v} [Iterator α Id β]
    (f : β → γ) (it : Iter (α := α) β) :=
  ((it.toIterM.map f).toPureIter : Iter γ)
