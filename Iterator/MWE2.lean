class X (α : Type u) (β : outParam (Type v)) where

structure Wrapper (α : Type u) : Type u where

instance {α α₂ : Type w} {α' : Type u} {α₂' : Type v} [X α α'] [X α₂ α₂'] :
  X (α × α₂) (PUnit.{max u v + 1} : Type max u v) := sorry

instance {α} : X (Wrapper α) (Wrapper α) := sorry

def f {β γ : Type w} (x : (Wrapper γ) × (Wrapper γ)) (y : (Wrapper β) × (Wrapper β)) :
    ((Wrapper β) × (Wrapper γ)) × PUnit.{w + 1} := sorry

def g {α α' : Type w} [X α α'] (it : α × α') : Nat := sorry

set_option pp.universes true in
set_option pp.explicit true in
def firstOfEach {α} (l : List (List α)) : Nat :=
  g (f (sorry : (Wrapper (List α)) × (Wrapper (List α))) ((sorry : (Wrapper α) × (Wrapper α))))

set_option pp.universes true in
set_option pp.explicit true in
def firstOfEach' {α : Type u} (l : List (List α)) : Nat :=
  g (f (sorry : (Wrapper (List α)) × (Wrapper (List α))) ((sorry : (Wrapper α) × (Wrapper α))))
