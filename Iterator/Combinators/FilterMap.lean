prelude
import Iterator.Combinators.Monadic.FilterMap
import Iterator.Pure

-- TODO: consistently require or do not require `Iterator` instances
-- in combinators
@[always_inline, inline]
def Iter.filterMap {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    (f : β → Option γ) (it : Iter (α := α) β) :=
  ((it.toIterM.filterMap f).toPureIter : Iter γ)

@[always_inline, inline]
def Iter.filter {α : Type w} {β : Type w} [Iterator α Id β]
    (f : β → Bool) (it : Iter (α := α) β) :=
  ((it.toIterM.filter f).toPureIter : Iter β)

@[always_inline, inline]
def Iter.map {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    (f : β → γ) (it : Iter (α := α) β) :=
  ((it.toIterM.map f).toPureIter : Iter γ)
