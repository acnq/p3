-- Tail Recursion

-- Functional programming, in the opposite, run tail call quicker
-- due to an aspect called *tail-call elimination*

def NonTail.sum : List Nat → Nat 
  | [] => 0
  | x :: xs => x + sum xs 

def Tail.sumHelper (soFar : Nat) : List Nat → Nat -- tail-recursive function
  | [] => soFar -- accumulators
  | x :: xs => sumHelper (x + soFar) xs 

def Tail.sum (xs : List Nat) : Nat := 
  Tail.sumHelper 0 xs 

-- Tail and Non-Tail Positions

-- a function call is in tail position
-- when the caller does not need to modify the returned value in any way,
--  but will just return it directly

-- Reversing Lists
def NonTail.reverse : List α → List α 
  | [] => []
  | x :: xs => reverse xs ++ [x]


def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs 

def Tail.reverse (xs : List α) : List α := 
  Tail.reverseHelper [] xs 


-- Multiple Recursive Calls
inductive BinTree (α : Type) where
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 
deriving Repr
 
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

