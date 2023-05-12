-- Coericions

-- Postive Numbers

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def Pos.toNat : Pos → Nat 
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

-- #eval [1, 2, 3, 4].drop (2 : Pos)
-- application type mismatch
--   List.drop 2
-- argument
--   2
-- has type
--   Pos : Type
-- but is expected to have type
--   Nat : Type
