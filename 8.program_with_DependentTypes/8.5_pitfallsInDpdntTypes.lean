-- Pitafalls of Programming with Dependent Types

-- distinction btwn interface and implementation begins to break down

def Nat.plusL : Nat → Nat → Nat 
  | 0, k => k
  | n + 1, k => plusL n k + 1

def Nat.plusR : Nat → Nat → Nat 
  | n, 0 => n
  | n, k + 1 => plusR n k + 1 

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

-- def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
--   | 0, k, .nil, ys => ys 
--   | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1)) -- Lean checks definition equality but stuck with vars

-- Vect α (Nat.plusL (n✝ + 1) k)
-- ✝ : dagger, indicate names Lean internally invented

-- Definitional Equality 
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys 
  | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)

def appendL_ : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys 
  | .cons x xs, ys => .cons x (appendL_ xs ys)

-- use of plusL in type of appendL, menas the def of plusL can't be refined

-- Getting Stuck on Addition
-- def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
--   | 0, k, .nil, ys => (_ : Vect α k)
--   | n + 1, k, .cons x xs, ys => _

-- type mismatch
--   ?m.3079
-- has type
--   Vect α k : Type ?u.3016
-- but is expected to have type
--   Vect α (Nat.plusR 0 k) : Type ?u.3016

-- since plusR 0 k and k are not definitionally equal 

-- Propositional Equality

-- diff from definitionally equality, propositional equality 
-- need evidence such as propositions
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)

def plusR_succ_left (n : Nat) : (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1 
  | 0 => by rfl 
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)

def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => plusR_succ_left n k ▸ .cons x (appendR n k xs ys)

-- operator ▸. 
-- Given an equality proof as its first argument and some other expression as its second, 
-- this operator replaces instances of the left side of the equality 
-- with the right side of the equality in the second argument's type

def appendR_ : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR_ xs ys)


-- Pros and Cons 
-- Recursive funct s.a plusR_zero_left are in fact proofs by mathematical induction

