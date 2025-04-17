
class ComputableUnivLE.{u, v} where
  Lift : Type u → Type v

instance ComputableUnivLE.self : ComputableUnivLE.{0, 0} where
  Lift α := sorry

instance ComputableUnivLE.ofMax [i : ComputableUnivLE.{v, v}] : ComputableUnivLE.{0, v} where
  Lift α := sorry

-- adding the zero instance _after `ofMax`_ resolves the errors
-- instance ComputableUnivLE.zero : ComputableUnivLE.{0, u} := sorry

class ComputableSmall.{v} (α : Type 0) where
  Lift : Type v

instance [ComputableUnivLE.{0, v}] {α} : ComputableSmall.{v} α where
  Lift := ComputableUnivLE.Lift α -- replacing this with sorry resolves the errors

structure Iter {α : Type 0} (m : Type w → Type 0) (β : Type 0) [ComputableSmall.{w} α] where

inductive T where
inductive W
inductive X
inductive Y
| y : Y

def Y.iter (l : Y) : Iter (α := X) Id W := sorry

-- replacing w with 0 resolves the errors
-- replacing m altogether with Id, too
@[inline]
def Iter.take {α : Type 0} {m : Type w → Type 0}
    -- exchanging ComputableUnivLE and n resolves the errors
    [ComputableUnivLE.{0, w}]
    (n : Nat) {_ : ComputableSmall.{w} α} (it : Iter (α := α) m W) : Iter (α := T) m W :=
  sorry

def flatMap {β : Type 0} {_ : ComputableSmall.{0} T} (f : β → Iter (α := T) Id W) (it : β) :
    W := sorry

set_option pp.universes true in
set_option pp.explicit true in
def fails :=
  flatMap (fun x => x.iter |>.take 1) Y.y
where
  x := 0

def succeeds :=
  flatMap (fun x => Y.iter x |>.take 1) Y.y
where
  x := 0
