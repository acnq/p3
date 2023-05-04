-- polymorphism

-- In functional programming, 
-- the term polymorphism typically refers to datatypes and definitions
-- that take types as arguments. 
-- This is different from the object-oriented programming community, 
-- where the term typically refers to subclasses 
-- that may override some behavior of their superclass. 

structure PPoint (α : Type) where 
  x : α 
  y : α 
deriving Repr

def natOrigin : PPoint Nat := 
  { x := Nat.zero, y := Nat.zero}

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α := 
  {point with x := newX}

#check (replaceX)
#check replaceX Nat

#check replaceX Nat natOrigin
#check replaceX Nat natOrigin 5 
#eval replaceX Nat natOrigin 5 

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int := 
  match s with 
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos 

-- (posOrNegThree Sign.pos : match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
-- ===>
-- ((match Sign.pos with
--   | Sign.pos => (3 : Nat)
--   | Sign.neg => (-3 : Int)) :
--  match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
-- ===>
-- ((3 : Nat) : Nat)
-- ===>
-- 3


-- Linked Lists 
def primeUnder10 : List Nat := [2, 3, 5, 7]

inductive List' (α : Type) where
  | nil : List' α 
  | cons : α → List' α → List' α 

def explicitPrimeUnder10 : List Nat := 
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

-- length String ["Sourdough", "bread"]
-- ===>
-- length String (List.cons "Sourdough" (List.cons "bread" List.nil))
-- ===>
-- Nat.succ (length String (List.cons "bread" List.nil))
-- ===>
-- Nat.succ (Nat.succ (length String List.nil))
-- ===>
-- Nat.succ (Nat.succ Nat.zero)
-- ===>
-- 2

def length (α : Type) (xs : List α) : Nat := 
  match xs with 
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)

def length' (α : Type) (xs : List α) : Nat := 
  match xs with 
  | [] => 0
  | y :: ys => Nat.succ (length α ys)

-- Implicit Arguments
def replaceX' {α : Type} (point : PPoint α) (newX : α) : PPoint α := 
  { point with x := newX}

#eval replaceX' natOrigin 5 

def length'' {α : Type} (xs : List α) : Nat := 
  match xs with 
  | [] => 0
  | y :: ys => Nat.succ (length'' ys)

#eval length'' primeUnder10

#eval primeUnder10.length

#check List.length (α := Int)

-- More Built-In Datatypes
-- option
-- used to check nullability
namespace Hidden
inductive Option (α : Type) : Type where
  | none : Option α 
  | some (val : α) : Option α
end Hidden  

namespace Hidden
def List.head? {α : Type} (xs : List α) : Option α := 
  match xs with 
  | [] => Option.none 
  | y :: _ => Option.some y 
end Hidden 

-- ? returns option, !: crashes when call empty, D: returns default when call empty

#eval primeUnder10.head?

-- #eval [].head?
-- don't know how to synthesize implicit argument
--   @List.nil ?m.20368
-- context:
-- ⊢ Type ?u.20365

-- don't know how to synthesize implicit argument
--   @_root_.List.head? ?m.20368 []
-- context:
-- ⊢ Type ?u.20365
-- unable to determine type

#eval [].head? (α := Int)
#eval ([] : List Int).head?

-- prod
namespace Hidden 
structure Prod (α : Type) (β : Type) : Type where
  fst : α 
  snd : β
end Hidden 

def fives : String × Int := {fst := "five", snd := 5}

def fives' : String × Int := ("fives", 5)

#eval fives 

def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
def sevens' : String × (Int × Nat) := ("VII", (7, 4 + 3))
-- both equivalent 

-- sum 
namespace Hidden
inductive Sum (α : Type) (β : Type) : Type where 
  | inl : α → Sum α β -- injection left
  | inr : β → Sum α β -- injection right
end Hidden 

def PetName : Type := String ⊕ String
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

-- inl : dog names, inr : cat names
def howManyDogs (pets : List PetName) : Nat := 
  match pets with 
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1 -- function call first, then + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

-- Unit
-- argumentless constructor 
namespace Hidden
inductive Unit : Type where
  | unit : Unit
end Hidden 

inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann 
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann 
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann 
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann 

-- Empty 

-- names : prod, sum and units

-- Messages
-- inductive MyType : Type where
--   | ctor : (α : Type) → α → MyType

-- invalid universe level in constructor 'MyType.ctor', parameter 'α' has type
--   Type
-- at universe level
--   2
-- it must be smaller than or equal to the inductive datatype universe level
--   1

-- inductive MyType : Type where
--   | ctor : (MyType → Int) → MyType

-- (kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared

-- inductive MyType (α : Type) : Type where 
--   | ctor : α → MyType

-- type expected, got
--   (MyType : Type → Type)

inductive MyType (α : Type) : Type where 
  | ctor : α → MyType α 

-- def ofFive : MyType := ctor 5 

-- Exercise

-- 1.
def List.last? {α : Type} (xs : List α) : Option α := 
  match xs with 
  | [] => none 
  | y :: [] => some y 
  | y :: ys => last? ys 


#eval primeUnder10.last?

-- 2. 
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := 
  match xs with 
  | [] => none
  | y :: ys => 
    if predicate y then some y 
    else List.findFirst? ys predicate

def even (n : Nat) : Bool := 
  match n with 
  | Nat.zero => true            -- base case
  | Nat.succ k => not (even k)

def odd (n : Nat) : Bool := 
  not (even n)

#eval primeUnder10.findFirst? even 
#eval primeUnder10.findFirst? odd 

-- 3. 
def Prod.swap {α β : Type} (pair : α × β) : β × α := 
  (pair.snd, pair.fst)

#eval (1, 2).swap 

-- 4 
inductive PetName' where 
  | catname
  | dogname 

-- 5 
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := 
  match xs, ys with 
    | [], _ => []
    | _, [] => []
    | x :: xs', y :: ys' => (x, y) :: zip xs' ys'  

#eval zip [1,2, 3] [3,4, 5]
#eval zip [1,2] [3,4,4]

-- 6 
def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n, xs with 
    | 0, _ => []
    | _, [] => []
    | n, x :: xs' => x :: take (n - 1) xs'

#eval take 3 ["bolete", "oyster"] 
#eval take 1 ["bolete", "oyster"]

-- 7
def distributeProductOverSum {α β γ : Type} : α × (β ⊕ γ) → (α × β) ⊕ (α × γ) 
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)

def multiplication2ToSum {α : Type} : Bool × α → α ⊕ α
  | (true, a) => Sum.inl a 
  | (false, a) => Sum.inr a 
