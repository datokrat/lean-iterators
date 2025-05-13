import Iterator.Pure.Basic
import Iterator.Consumers.Loop

instance (α : Type w) (β : Type v) (n : Type w → Type w')
    [Iterator α Id β] :
    [IteratorFor α Id n] →
    ForIn n (Iter (α := α) β) β where
  forIn it := IteratorFor.forIn (_lift := fun _ c => pure c.run) it.toIterM

@[always_inline, inline]
def Iter.foldM {n : Type w → Type w} [Monad n]
    {α : Type w} {β : Type v} {γ : Type w} [Iterator α Id β]
    [IteratorFor α Id n] (f : γ → β → n γ)
    (init : γ) (it : Iter (α := α) β) : n γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

@[always_inline, inline]
def Iter.count {α : Type u} {β : Type v} [Iterator α Id β] [Finite α Id]
    (it : Iter (α := α) β) : Nat :=
  it.toIterM.count
