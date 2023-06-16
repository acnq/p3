-- Proving Equivalence

-- Proving sum Equal 
def NonTail.sum : List Nat → Nat 
  | [] => 0
  | x :: xs => x + sum xs 

def Tail.sumHelper (soFar : Nat) : List Nat → Nat -- tail-recursive function
  | [] => soFar -- accumulators
  | x :: xs => sumHelper (x + soFar) xs 

def Tail.sum (xs : List Nat) : Nat := 
  Tail.sumHelper 0 xs 


-- theorem helper_add_sum_accum (xs : List Nat) (n : Nat) : 
--     n + Tail.sum xs = Tail.sumHelper n xs := by 
--   induction xs with 
--   | nil => rfl 
--   | cons y ys ih => 
--     simp [Tail.sum, Tail.sumHelper]
-- unsolved goals
-- case cons
-- n y : Nat
-- ys : List Nat
-- ih : n + Tail.sum ys = Tail.sumHelper n ys
-- ⊢ n + Tail.sumHelper y ys = Tail.sumHelper (y + n) ys
-- stuck 
-- The induction hypothesis can be used for Tail.sumHelper n ys, 
-- not Tail.sumHelper (y + n) ys

-- A Second Attempt
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by 
  induction xs with 
  | nil => 
    intro n 
    rfl 
  | cons y ys ih => 
    intro n 
    simp [NonTail.sum, Tail.sumHelper]
    rw [← Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n + y)



theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs -- funext == funcion extensibility 
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0 

  