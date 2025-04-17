/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Iterator.Basic
import Iterator.Bundled
import Iterator.Producers
import Iterator.Combinators
import Iterator.Consumers

open Std

section ListIterator

-- set_option trace.compiler.ir true in
-- @[noinline]
-- def sum (l : List Nat) : Nat := Id.run do
--   let mut it := l.iter Id
--   let mut sum := 0
--   while true do
--     match it.step with
--     | .yield it' n _ =>
--       sum := sum + n
--       it := it'
--     | .skip it' _ =>
--       it := it'
--     | .done _ =>
--       break
--   return sum

end ListIterator

section FilterMap

set_option trace.compiler.ir.result true in
def steppi (l : List Nat) : Nat :=
  let x : Iter (α := ListIterator Nat) Id.{0} Nat := sorry
  match (l.iter Id |>.step).run with
  | .yield it' x _ => x
  | .skip it' _ => 1
  | .done _ => 0

@[noinline]
def sumrec (l : List Nat) : Nat :=
  go (l.iter Id) 0
where
  go it acc :=
    match it.step with
    | .yield it' n _ => go it' (acc + n)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by finiteIteratorWF it (m := Id)

set_option trace.compiler.ir.result true in
@[noinline]
def forInItSum (l : List Nat) : Nat := Id.run do
  let mut sum := 0
  for x in l.iter do
    sum := sum + x
  return sum

end FilterMap

section FlatMap

set_option trace.compiler.ir.result true in
def testFlatMap (l : List (List Nat)) : Nat :=
  go (l.iter.flatMap fun l' => l'.iter) 0
where
  @[specialize]
  go it acc :=
    match it.step with
    | .yield it' n _ => go it' (acc + n)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by finiteIteratorWF it

set_option trace.compiler.ir.result true in
def testFlatMap' (l : List (List Nat)) : Nat := Id.run do
  let mut sum := 0
  for x in l.iter.flatMap (fun l' => l'.iter) do
    sum := sum + x
  return sum

#eval! testFlatMap [[1, 2], [3]]

end FlatMap

section IO

set_option trace.compiler.ir.result true in
def testIO (l : List Nat) : IO Unit :=
  go (l.iter IO |>.map (2 * ·))
where
  go it := do
    let step ← it.step
    match step with
    | .yield it' x _ =>
      if x < 1 then IO.println x
      go it'
    | .skip it' _ =>
      go it'
    | .done _ =>
      return
  termination_by finiteIteratorWF it

#eval testIO [1, 2, 3]

def testIOList : List Nat → IO Unit
  | [] => pure ()
  | x :: xs => do
    if x < 1 then IO.println x
    testIOList xs

end IO

section PlainListIteration

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

end PlainListIteration

def l := List.range 1000000

set_option trace.compiler.ir.result true in
@[noinline]
def runInternal (f : List Nat → Nat) : IO Nat := do
  return f l

set_option trace.compiler.ir.result true in
def run (name : String) (f : List Nat → Nat) : IO Unit := do
  let sum ← timeit name <| runInternal f
  IO.println sum

@[noinline]
def runIOInternal (f : List Nat → IO Unit) : IO Unit := do
  f l

def runIO (name : String) (f : List Nat → IO Unit) : IO Unit := do
  timeit name <| runIOInternal f

set_option trace.compiler.ir.result true in
set_option trace.compiler.ir.result true in
def Bench.main : IO Unit := do
  for _x : Nat in [0:10] do
    -- run "List.sum" sum''
    -- run "iterator recursion" sumrec
    runIO "it" testIO
    runIO "l" testIOList
  return ()

#eval Bench.main
