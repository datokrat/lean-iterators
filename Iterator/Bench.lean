/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
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
    | .yield it' n _ =>
      sum := sum + n
      it := it'
    | .skip it' _ =>
      it := it'
    | .done =>
      break
  return sum

set_option trace.compiler.ir.result true in
@[noinline]
def sumrec (l : List Nat) : Nat :=
  go (l.iter.map (2 * ·)) 0
where
  go it acc :=
    match Iterator.step it with
    | .yield it' n _ => go it' (acc + n)
    | .skip it' _ => go it' acc
    | .done => acc
  termination_by finiteIteratorWF it

set_option trace.compiler.ir.result true in
def testIO (l : List Nat) : IO Unit :=
  go (l.iter IO |>.map (2 * ·))
where
  go it := do
    let step ← Iterator.step it
    match step with
    | .yield it' x _ =>
      if x < 1 then IO.println x
      go it'
    | .skip it' _ =>
      go it'
    | .done =>
      return
  termination_by finiteIteratorWF it

def testIOList : List Nat → IO Unit
  | [] => pure ()
  | x :: xs => do
    if x < 1 then IO.println x
    testIOList xs

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

@[noinline]
def runIOInternal (f : List Nat → IO Unit) : IO Unit := do
  f l

def runIO (name : String) (f : List Nat → IO Unit) : IO Unit := do
  timeit name <| runIOInternal f

set_option trace.compiler.ir.result true in
def Bench.main : IO Unit := do
  for _ in [0:10] do
    -- run "List.sum" sum''
    -- run "iterator recursion" sumrec
    runIO "it" testIO
    runIO "l" testIOList

#eval Bench.main
