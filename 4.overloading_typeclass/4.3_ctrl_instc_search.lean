-- Controlling Instance Search

-- heterogeneous operator overloading

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def Pos.toNat : Pos → Nat 
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : ToString Pos where
  toString x := toString (x.toNat)
instance : OfNat Pos (n + 1) where
  ofNat := 
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n 
#eval (3 : Pos)


def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)

-- Heterogeneous Overloadings
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)

class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos
instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

-- #eval HPlus.hPlus (3 : Pos) (5 : Nat)  
-- typeclass instance problem is stuck, it is often due to metavariables
--  HPlus Pos Nat ?m.7602
-- γ is unknown

#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)

-- output parameters
class HPlus1 (α : Type) (β : Type) (γ : outParam Type) where
  hPlus1 : α → β → γ

instance : HPlus1 Pos Nat Pos where
  hPlus1 := addPosNat 
#eval HPlus1.hPlus1 (3 : Pos) (5 : Nat)

-- Default Instances

-- -- default types
-- Default instances are instances 
-- that are available for instance search 
-- even when not all their inputs are known


instance [Add α] : HPlus1 α α α where
  hPlus1 := Add.add

#eval HPlus1.hPlus1 (3 : Nat) (5 : Nat)

#check HPlus1.hPlus1 (5 : Nat) (3 : Nat)
-- HPlus1.hPlus1 5 3 : Nat

#check HPlus1.hPlus1 (5 :Nat)
-- HPlus1.hPlus1 5 : ?m.18334 → ?m.18336

@[default_instance]
instance [Add α] : HPlus1 α α α where
  hPlus1 := Add.add

#check HPlus1.hPlus1 (5 : Nat)
-- HPlus.hPlus 5 : Nat → Nat

-- Exercise
structure PPoint (α : Type) where
  x : α 
  y : α
deriving Repr

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul s p := {x := s.x * p, y := s.y * p}

#eval {x := 2.5, y := 3.7 : PPoint Float}
#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0 