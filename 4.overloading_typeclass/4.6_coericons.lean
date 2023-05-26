-- Coericions //强转

-- Postive Numbers

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
-- #eval [1, 2, 3, 4].drop (2 : Pos)
-- application type mismatch
--   List.drop 2
-- argument
--   2
-- has type
--   Pos : Type
-- but is expected to have type
--   Nat : Type

namespace Hidden
class Coe (α : Type) (β : Type) where 
  coe : α → β  
end Hidden

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos)

-- Chaining Coericons
def oneInt : Int := Pos.one

inductive A where
  | a 

inductive B where
  | b 
deriving Repr

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := () -- () used for Unit.unit 
#eval coercedToB

def List.last? : List α → Option α 
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)

def perhapsPerhapsPerhaps : Option (Option (Option String)) := 
  "Please don't tell me"

-- def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) := 
--   392
-- -- failed to synthesize instance
--   OfNat (Option (Option (Option Nat))) 392
-- since it is a instance missing, not a type mismatch, the coericon is not of help

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) := 
  (392 : Nat)

def perhapsPerhapsPerhapsNat' : Option (Option (Option Nat)) := 
  ↑(392 : Nat)
-- ↑ as coericon 

