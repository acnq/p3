-- Indexed Families

-- type arguments, which are the same in every 
-- constructor of the dataype, are referred to as parameters

--  Inductive types 
-- in which the arguments to the type 
-- vary based on the choice of constructor are called indexed families, 
-- and the arguments that vary are referred to as indices

inductive Vect (α : Type u) : Nat → Type u where 
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

-- example : Vect String 3 := Vect.nil 
-- type mismatch
--   Vect.nil
-- has type
--   Vect String 0 : Type
-- but is expected to have type
--   Vect String 3 : Type

-- example : Vect String n := Vect.nil 
-- type mismatch
--   Vect.nil
-- has type
--   Vect String 0 : Type
-- but is expected to have type
--   Vect String n : Type

-- example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)
-- type mismatch
--   Vect.cons "Hello" (Vect.cons "world" Vect.nil)
-- has type
--   Vect String (0 + 1 + 1) : Type
-- but is expected to have type
--   Vect String n : Type

def Vect.replicate (n : Nat) (x : α) : Vect α n := 
  match n with  -- dependent pattern matching
    | 0 => .nil 
    | k + 1 => .cons x (replicate k x)


-- help rule out a number of unexpected functions
namespace Hidden 
def List.replicate (n : Nat) (x : α) : List α := 
  match n with 
    | 0 => []
    | k + 1 => x :: x :: replicate k x 

-- a wrong function, but grammarly right

-- def Vect.replicate (n : Nat) (x : α) : Vect α n := 
--   match n with 
--     | 0 => .nil
--     | k + 1 => .cons x (.cons x (replicate k x))

-- wrong function, and grammarly checked wrong
-- application type mismatch
--   cons x (cons x (replicate k x))
-- argument
--   cons x (replicate k x)
-- has type
--   Vect α (k + 1) : Type ?u.2019
-- but is expected to have type
--   Vect α k : Type ?u.2019

#eval ["Mount Hood", "Mount Jefferson", "South Sister"].zip ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]
#eval [3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35]

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n 
  | .nil, .nil => .nil 
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

-- there are no missing cases of .nil and .cons,
--  since the first nil or cons refines the type checker's knowledge about lentgh m

-- but if it is List, it would be missing cases
-- def List.zip : List α → List β → List (α × β)
--   | [], [] => []
--   | x :: xs, y :: ys => (x, y) :: zip xs ys   
-- missing cases:
-- (List.cons _ _), []
-- [], (List.cons _ _)

-- use nil and cons together is a type error 
-- def Vect.zip : Vect α n → Vect β n → Vect (α × β) n 
--   | .nil, .nil => .nil 
--   | .nil, .cons y ys => .nil
--   | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

-- type mismatch
--   Vect.cons y ys
-- has type
--   Vect β (?m.4765 + 1) : Type ?u.4577
-- but is expected to have type
--   Vect β 0 : Type ?u.4577

def Vect.zip2 : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n 
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip2 k xs ys)