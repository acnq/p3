-- Standard Classes

-- Arithmetic

-- x + y : HAdd.hAdd x y
-- x - y : HSub.hSub x y
-- x * y : HMul.hMul x y 
-- x / y : HDiv.hDiv x y 
-- x % y : HMod.hMod x y
-- x ^ y : HPow.hPow x y
-- (- x) : Neg.neg x

-- Bitwise Operators

-- x &&& y : HAnd.hAnd x y 
-- x ||| y : HOr.hOr x y 
-- x ^^^ y : HXor.hXor x y 
-- ~~~ x   : Complement.complement x 
-- x >>> y : HShiftRight.hShiftRight x y 
-- x <<< y : HShiftLeft.hShiftLetf x y 

-- Equality and Ordering
-- BEq classes : == (Boolean Equality)
-- PEq classes : = (Proposition equality)

#eval "Octopus" == "Cuttlefish"
#eval "Octopodes" == "Octo".append "podes"
-- #eval (fun (x : Nat) => 1 + x) == (Nat.succ ·)
-- failed to synthesize instance
--   BEq (Nat → Nat)

#check 2 < 4 
#check if 2 < 4 then 1 else 2 
#eval if 2 < 4 then 1 else 2 
-- #eval if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"
-- failed to synthesize instance
--  Decidable ((fun x => 1 + x) = fun x => Nat.succ x)

-- x < y : LT.lt x y
-- x ≤ y : LE.le x y
-- x > y : LT.lt y x
-- x ≥ y : LE.le y x 

namespace Hidden
inductive Ordering where
  | lt
  | eq
  | gt 
end Hidden 

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

def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt 
  | Pos.succ n, Pos.succ k => comp n k 

instance : Ord Pos where
  compare := Pos.comp

-- Hashing
namespace Hidden
class Hashable (α : Type) where
  hash : α → UInt64
end Hidden 

def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos

#eval hashPos (2 : Pos)
#eval hashPos (1 : Pos)

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

inductive BinTree (α : Type) where
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 
deriving Repr

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool 
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable  α] : Hashable (BinTree α) where
  hash := hashBinTree


-- Deriving Standard  Classes
deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable, Repr for NonEmptyList

-- Appending
namespace Hidden
class HAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ
end Hidden

instance : Append (NonEmptyList α) where
  append xs ys := 
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced 蜘蛛"
  ]
}  
#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys := 
    {head := xs.head, tail := xs.tail ++ ys}

#eval idahoSpiders ++ ["Trapdorr Spider"]

-- Functors
#eval Functor.map (· + 5) [1,2,3]
#eval Functor.map toString (some (List.cons 5 List.nil))
#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]

#eval (· + 5) <$> [1,2,3]
#eval toString <$> (some (List.cons 5 List.nil)) 
#eval List.reverse <$> [[1, 2, 3], [4, 5, 6]]

instance : Functor NonEmptyList where
  map f xs := {head := f xs.head, tail := f <$> xs.tail}

structure PPoint (α : Type) where
  x : α 
  y : α
deriving Repr
instance : Functor PPoint where
  map f p := {x := f p.x, y := f p.y}

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start 
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

#eval concat idahoSpiders

namespace Hidden
class Functor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  mapConst {α β : Type} (x : α) (coll : f β) : f α := 
    map (fun _ => x) coll

-- deriving instance ToString for NonEmptyList 
-- default handlers have not been implemented yet, class: 'ToString' types: [NonEmptyList]

-- Exercise

-- 1. 
instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys :=
    let rec happ : List α → NonEmptyList α → NonEmptyList α 
      | [], ys => ys
      | x :: xs', ys' => {head := x, tail := xs' ++ [ys'.head] ++ ys'.tail}
    happ xs ys

def xs : List Nat := [1, 2, 3]
def ys : NonEmptyList Nat := {
  head := 4, 
  tail := [5,6]
  }

def result : NonEmptyList Nat := HAppend.hAppend xs ys 
#eval result

-- 2.

def BTmap {α β : Type} (f : α → β) : BinTree α → BinTree β 
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch left val right => BinTree.branch (BTmap f left) (f val) (BTmap f right)
instance : Functor BinTree where
  map f t := BTmap f t

def double : Nat → Nat := λ n => n * 2
def tree : BinTree Nat := BinTree.branch (BinTree.leaf) 1 (BinTree.branch (BinTree.leaf) 2 (BinTree.leaf))
def transformed : BinTree Nat := Functor.map double tree  
#eval transformed

