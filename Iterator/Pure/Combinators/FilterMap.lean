prelude
import Iterator.Combinators.FilterMap
import Iterator.Pure.Basic

-- TODO: consistently require or do not require `Iterator` instances
-- in combinators
@[always_inline, inline]
def Iter.filterMap {α : Type w} {β : Type v} [Iterator α Id β]
    (f : β → Option γ) (it : Iter (α := α) β) :=
  ((it.toIterM.filterMap f).toPureIter : Iter γ)
