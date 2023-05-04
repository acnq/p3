-- Additional Conveniences

-- automatic implicit arguments
def length {α : Type} (xs : List α) : Nat :=
  match  xs with 
  | [] => 0
  | y :: ys => Nat.succ (length ys)

def length' (xs : List α) : Nat := 
  match xs with 
  | [] => 0
  | y :: ys => Nat.succ (length' ys)

-- Pattern-Matching Definitions
def length'' : List α → Nat
  | [] => 0
  | y :: ys => Nat.succ (length'' ys)

def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, x :: xs => drop n xs

def fromOption (default : α) : Option α → α 
  | none => default 
  | some x => x 

#eval (some "salmonberry").getD ""
#eval none.getD ""

-- Local Definitions
def unzip : List (α × β) → List α × List β 
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzip xys).fst, y :: (unzip xys).snd)
-- slow: 2 recursive here.

def unzip' : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)

def reverse (xs : List α) : List α := 
  let rec helper : List α → List α → List α 
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

#eval reverse [1,2, 3]  

-- Type Inference
def unzip'' : List (α × β) → List α × List β 
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)

-- omitting return type possible when explicit matched
def unzip''' (pairs : List (α × β)) := 
  match pairs with 
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
-- make type as explicit as possible

#check 14
#check (14 : Int)

-- def unzip4 pairs :=
--   match pairs with
--   | [] => ([], [])
--   | (x, y) :: xys =>
--     let unzipped := unzip xys
--     (x :: unzipped.fst, y :: unzipped.snd)

-- invalid match-expression, pattern contains metavariables
--  []

def id' (x : α) : α := x 
def id'' (x : α) := x 

-- def id x = x 
-- failed to infer binder type

-- In general, messages that say something like "failed to infer" 
-- or that mention metavariables 
-- are often a sign that more type annotations are necessary. 

-- simultaneous matching
def drop' (n : Nat) (xs : List α) : List α := 
  match n, xs with 
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n, y :: ys => drop n ys 

-- Natural Number Pattern
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
-- use 0 (as .zero) and + (as .succ)
def even' : Nat → Bool 
  | 0 => true 
  | n + 1 => not (even n)

def halve : Nat → Nat 
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1

#eval halve 6

def halve' : Nat → Nat 
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

-- not here the + means succ, so the second para must be Nat
-- def halve'' : Nat → Nat
--   | 0 => 0
--   | 1 => 0
--   | 2 + n => halve n + 1

-- invalid patterns, `n` is an explicit pattern variable, 
-- but it only occurs in positions that are inaccessible to pattern matching
--  .(Nat.add 2 n)

-- Anonymous Functions
#check fun x => x + 1
#check fun (x : Int) => x + 1

#check fun {α : Type} (x : α) => x 
-- lambda expression

#check fun 
  | 0 => none
  | n + 1 => some n 

def double : Nat → Nat := fun 
  | 0 => 0
  | k + 1 => double k + 2

#eval (· , ·) 1 2
#eval (fun x => x + x) 5 
#eval (· * 2) 5 

-- Namespaces
def Nat.double (x : Nat) : Nat := x + x
#eval (4 : Nat).double

namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

#check NewNamespace.triple
#check NewNamespace.quadruple

def timesTwelve (x : Nat) :=
  open NewNamespace in 
  quadruple (triple x)

open NewNamespace in 
#check quadruple

-- #check quadruple
-- in only effects 1 line

-- if let
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

def Inline.string? (inline : Inline) : Option String := 
  match inline with 
  | Inline.string s => some s 
  | _ => none 

def Inline.string?' (inline : Inline) : Option String := 
  if let Inline.string s := inline then 
    some s
  else none

-- Positional Structure Arguments

-- #eval ⟨1, 2⟩ 
-- invalid constructor ⟨...⟩, expected type must be an inductive type 
-- ?m.35347
-- need a type 

structure Point where 
  x : Float
  y : Float
deriving Repr

#eval (⟨1, 2⟩ : Point)

-- String Interpolation
#eval s!"three five is {NewNamespace.triple 5}"

-- #eval s!"three fives is {NewNamespace.triple}"
-- failed to synthesize instance
--  ToString (Nat → Nat)





