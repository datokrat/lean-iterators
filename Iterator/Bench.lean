import Iterator.Basic
import Iterator.Bundled
import Iterator.FiniteOfType
import Iterator.Generators

open Std

set_option trace.compiler.ir true in
@[noinline]
def sum (l : List Nat) : Nat := Id.run do
  let mut it := l.iter
  let mut sum := 0
  while true do
    match Iterator.step it with
    | .yield it' n =>
      sum := sum + n
      it := it'
    | .skip it' =>
      it := it'
    | .done =>
      break
  return sum

set_option trace.compiler.ir.result true in
@[noinline]
def sumrec (l : List Nat) : Nat :=
  go (l.iter.map (2 * ·)) 0
where
  go it acc := match Iterator.step it with
    | .yield it' n => go it' (acc + n)
    | .skip it' => go it' acc
    | .done => acc
  termination_by stepsRemaining it
  decreasing_by
    · sorry
    · sorry

#eval! match [1, 2, 3].iter.map (3 * ·) |> Iterator.step with
  | .yield _ x => x
  | _ => 0

set_option trace.compiler.ir true in
@[noinline]
def sumrecFiniteOfType (l : List Nat) : Nat :=
  go (attachFinite <| l.iter.map (2 * ·)) 0
where
  go it acc := match Iterator.step it with
    | .yield it' n => go it' (acc + n)
    | .skip it' => go it' acc
    | .done => acc
  termination_by stepsRemaining it
  decreasing_by
    · sorry
    · sorry

set_option trace.compiler.ir true in
@[noinline]
def sumbundled (l : List Nat) : Nat :=
  go (toFiniteIterator l.iter) 0
where
  go it acc := match Iterator.step it with
    | .yield it' n => go it' (acc + n)
    | .skip it' => go it' acc
    | .done => acc
  termination_by stepsRemaining it
  decreasing_by
    · sorry
    · sorry

set_option trace.compiler.ir true in
@[noinline]
def sum' (l : List Nat) : Nat := Id.run do
  let mut it := l
  let mut sum := 0
  while true do
    match it with
    | [] => break
    | n :: it' =>
      sum := sum + n
      it := it'
  return sum

set_option trace.compiler.ir.result true in
def sum'' (l : List Nat) : Nat := l.foldl (· + 2 * ·) 0

def l := List.range 1000000

set_option trace.compiler.ir.result true in
@[noinline]
def runInternal (f : List Nat → Nat) : IO Nat := do
  return f l

set_option trace.compiler.ir.result true in
def run (name : String) (f : List Nat → Nat) : IO Unit := do
  let sum ← timeit name <| runInternal f
  IO.println sum

set_option trace.compiler.ir.result true in
def Bench.main : IO Unit := do
  for _ in [0:10] do
    run "List.sum" sum''
    run "List.sumrec" sumrec
    run "List.sumrecFiniteOfType" sumrecFiniteOfType
    -- run "sum" sum
    -- run "sum'" sum'

#eval! Bench.main
