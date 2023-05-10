-- type class and polymorphism
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
class Plus (α : Type) where
  plus : α → α → α  
instance : Plus Nat where
  plus := Nat.add
instance : OfNat Pos (n + 1) where
  ofNat := 
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n 

#check (IO.println)
#check @IO.println
-- ⊢ {α : Type u_1} → [inst : ToString α] → α → IO Unit
-- inst : instance name, u_1, not discussed now

-- Defining Polymorphic Functions with Instance Implicits
def List.sum [Add α] [OfNat α 0] : List α → α 
  | [] => 0
  | x :: xs => x + xs.sum

def fourNats : List Nat := [1, 2, 3, 4]
#eval fourNats.sum  

def fourPos : List Pos := [1, 2, 3, 4]
-- #eval fourPos.sum
-- failed to synthesize instance
--  OfNat Pos 0

structure PPoint (α : Type) where
  x : α 
  y : α 
deriving Repr

instance [Add α] : Add (PPoint α) where
  add p1 p2 := {x := p1.x + p2.x, y := p1.y + p2.y}

-- Methods and Implicit Arguments
#check @OfNat.ofNat
--  {α : Type} → (n : Nat) → [OfNat α n] → α,

-- Exercise:
structure Even where
  double :: 
  core : Nat 
deriving Repr

def zero2 : Even := Even.double 0
def four : Even := Even.double 2
def six : Even := Even.double 3

def Even.plus : Even → Even → Even
  | Even.double n, Even.double k => Even.double (n + k)
instance : Add Even where
  add := Even.plus

def Even.mul : Even → Even → Even
  | Even.double 0, k => Even.double 0
  | Even.double n, Even.double k => Even.double ( 2 * n * k)
instance: Mul Even where
  mul := Even.mul

#eval four + four
#eval four * four
#eval four * six


def Even.toNat : Even → Nat 
  | Even.double n => n * 2

instance : ToString Even where
  toString x := toString (x.toNat)

#eval s!"there are {four}"

instance : OfNat Even Nat.zero where
    ofNat := {core := 0} 


instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat :=  Even.double (n + 2) 

def eight : Even := 8
def zero3 : Even := 0
#eval zero3
#eval eight
def six' : Even := 6
#eval six'
