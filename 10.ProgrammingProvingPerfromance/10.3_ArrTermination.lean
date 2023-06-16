-- Arrays and Termination

-- Inequility
namespace Hidden
class LE (α : Type u) where
  le : α → α → Prop
class LT (α : Type u) where
  lt : α → α → Prop 
instance : LE Nat where
  le := Nat.le 
end Hidden 

-- Inductively-Defined Propositions, Predicates, and Relations

-- When a proposition takes an argument, 
-- it is referred to as a *predicate* that may be true for some, 
-- but not all, potential arguments

-- Propositions that take multiple arguments are called *relations*.

inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve

theorem fairlyEasy : EasyToProve := by 
  constructor 

namespace Hidden
inductive True : Prop where
  | intro : True 
end Hidden 

inductive IsThree : Nat → Prop where
  | isThree : IsThree 3 

theorem three_is_three : IsThree 3 := by 
  constructor

inductive IsFive : Nat → Prop where
  | isFive : IsFive 5

theorem three_plus_two_five : IsThree n → IsFive ( n + 2) := by 
  intro three 
  cases three with 
  | isThree => constructor 

theorem four_is_not_three : ¬ IsThree 4 := by 
  intro h 
  cases h 

-- Inequality of Natural Numbers 
namespace Hidden
inductive Nat.le (n : Nat) : Nat → Prop 
  | refl : Nat.le n n 
  | step : Nat.le n m → Nat.le n (m + 1)
end Hidden 

theorem four_le_seven : 4 ≤ 7 := 
  open Nat.le in 
  step (step (step refl))

namespace Hidden 
def Nat.lt (n m : Nat) : Prop :=
  Nat.le (n + 1) m 

instance : LT Nat where
  lt := Nat.lt 
end Hidden 

theorem four_lt_seven : 4 < 7 := 
  open Nat.le in 
  step (step refl)

-- Proving Termination
namespace Hidden 
def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arrayMapHelper _ arr _ i _ => arr.size - i

def Array.map (f : α → β) (arr : Array α) : Array β := 
  arrayMapHelper f arr Array.empty 0

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) := 
  if h : i < arr.size then 
    let x := arr[i]
    if p x then 
      some (i, x)
    else findHelper arr p (i + 1)
  else none 
termination_by findHelper arr p i => arr.size - i 

def Array.find (arr : Array α) (p : α → Bool) : Option (Nat × α) := 
  findHelper arr p 0
end Hidden

