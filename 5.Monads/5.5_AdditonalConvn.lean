-- Additional Conveniences

-- Shared Argument Types
def equal? [BEq α] (x : α) (y : α) : Option α := 
  if x == y then 
    some x 
  else 
    none 
-- can be written
def equal_? [BEq α] (x y : α) : Option α := 
  if x == y then 
    some x 
  else 
    none  

-- Leading Dot Notation
inductive BinTree (α : Type) where
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 
deriving Repr

def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
-- can be written
def BinTree.mirror_ : BinTree α → BinTree α 
  | .leaf => .leaf
  | .branch l x r => .branch (mirror_ r) x (mirror_ l)

def BinTree.empty : BinTree α := .leaf
#check (.empty : BinTree Nat)

-- Or-Patterns
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr

def Weekday.isWeekend (day : Weekday) : Bool := 
  match day with
    | Weekday.saturday => true
    | Weekday.sunday => true
    | _ => false

def Weekday.isWeekend' (day : Weekday) : Bool := 
  match day with
    | .saturday => true
    | .sunday => true
    | _ => false 

def Weekday.isWeekend'' (day : Weekday) : Bool := 
  match day with 
    | .saturday | .sunday => true
    | _ => false

def condense : α ⊕ α → α 
  | .inl x | .inr x => x 

def stringy : Nat ⊕ Weekday → String 
  | .inl x | .inr x => s!"It is {repr x}"

def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat 
  | .inl (n, x) | .inr (n, y) => n

-- Attempting to access x in a similar definition causes an error 
-- because there is no x available in the second pattern:

-- def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
--   | .inl (n, x) | .inr (n, y) => x
-- unknown identifier 'x'

def str := "Some string"
def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str

#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))
#eval getTheString (.inr (20, "twenty"))
