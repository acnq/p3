-- Interlude :  Tactics, Induction, and Proofs

-- A Note on Proofs and User Interfaces

-- Return and Induction

-- The Induction Tactic
def Nat.plusR : Nat → Nat → Nat 
  | n, 0 => n
  | n, k + 1 => plusR n k + 1 

theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [←ih] -- which takes a list of equality proofs and replaces the left side 
    -- with the right side in the goa


theorem plusR_zero_left' (k : Nat) : k = Nat.plusR 0 k := by 
  induction k with 
  | zero => rfl
  | succ n ih => 
    simp [Nat.plusR]
    assumption 

theorem plusR_zero_left2 (k : Nat) : k = Nat.plusR 0 k := by 
  induction k 
  case zero => rfl 
  case succ n ih => 
    simp [Nat.plusR]
    assumption

-- T1 <;> T2 applies T1 to the current goal, 
-- and then applies T2 in all goals created by T1

theorem plusR_zero_left3 (k : Nat) : k = Nat.plusR 0 k := by 
  induction k <;> simp [Nat.plusR] <;> assumption 


-- Induction on Other Datatypes 

inductive BinTree (α : Type) where
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 
deriving Repr

def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r => 
    1 + l.count + r.count 

def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)

theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by 
  induction t with 
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr => 
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
    simp_arith


theorem BinTree.mirror_count2 (t : BinTree α) : t.mirror.count = t.count := by 
  induction t with 
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp_arith [BinTree.mirror, BinTree.count, ihl, ihr]

theorem BinTree.mirror_count3 (t : BinTree α) : t.mirror.count = t.count := by 
  induction t with 
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp_arith [BinTree.mirror, BinTree.count, *]

theorem BinTree.mirror_count4 (t : BinTree α) : t.mirror.count = t.count := by 
  induction t <;> simp_arith [BinTree.mirror, BinTree.count, *]
