-- Arrays and Indexing

-- Arrays
-- like C++ std::vector, Java ArrayList, Rust vec

def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size
#eval northernTrees[2]

-- #eval northernTrees[8]
-- failed to prove index is valid, possible solutions:
--   - Use `have`-expressions to prove the index is valid
--   - Use `a[i]!` notation instead, runtime check is perfomed, and 'Panic' error message is produced if index is not valid
--   - Use `a[i]?` notation instead, result is an `Option` type
--   - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
-- ⊢ 8 < Array.size northernTrees

-- Non-Empty Lists

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced 蜘蛛"
  ]
}  

#eval idahoSpiders.tail

def NonEmptyList.get? : NonEmptyList α → Nat → Option α 
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n 


def NonEmptyList.get1? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head 
  | xs, n + 1 => xs.tail.get? n     

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop := 
  i ≤ xs.tail.length

theorem atLeastThreeSipders : idahoSpiders.inBounds 2 := by simp
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by simp

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=  
  match i with 
  | 0 => xs.head
  | n + 1 => xs.tail[n]

-- Overloading Indexing

-- GetElem type class : 
-- type of the collection,
-- type of the index
-- type of elements that are extracted from the collection
-- function determines what count as evidence that the idx is inBounds

class GetElem1 (coll : Type) (idx : Type) (item : outParam Type) (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item
 

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get


#eval idahoSpiders[0]
-- #eval idahoSpiders[8]
-- failed to prove index is valid, possible solutions:
--   - Use `have`-expressions to prove the index is valid
--   - Use `a[i]!` notation instead, runtime check is perfomed, and 'Panic' error message is produced if index is not valid
--   - Use `a[i]?` notation instead, result is an `Option` type
--   - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
-- ⊢ NonEmptyList.inBounds idahoSpiders 9

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
def Pos.toNat : Pos → Nat 
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat)  where 
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

structure PPoint (α : Type) where
  x : α 
  y : α
deriving Repr
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ := 
    if not i then p.x else p.y