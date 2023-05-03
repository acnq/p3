-- Datatypes and Patterns

-- sum types: datatypes allow choices
-- recursive types: include itself
-- inductive types: rec type + sum type

inductive Bool' where
  | false : Bool' 
  | true : Bool'
deriving Repr

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat') : Nat'
deriving Repr
-- Pattern Matching

def isZero (n : Nat) : Bool := 
  match n with 
  | Nat.zero => true
  | Nat.succ k => false


#eval isZero Nat.zero
#eval isZero 5

def pred (n : Nat) : Nat := 
  match n with 
  | Nat.zero => Nat.zero
  | Nat.succ k => k 

#eval pred 5 
#eval pred 0 

structure Point3D where 
  x : Float
  y : Float 
  z : Float 
deriving Repr 

def depth (p : Point3D) : Float := 
  match p with 
  | { x := h, y := w, z := d } => d 


-- recursive functions
def even (n : Nat) : Bool := 
  match n with 
  | Nat.zero => true            -- base case
  | Nat.succ k => not (even k)

-- structural recursion above


-- forbid non-terminable function
-- def evenLoops (n : Nat) : Bool := 
--   match n with 
--   | Nat.zero => true
--   | Nat.succ k => not (evenLoops n)

-- fail to show termination for
--   evenLoops
-- with errors
-- structural recursion cannot be used

-- well-founded recursion cannot be used, 'evenLoops' does not take any (non-fixed) arguments

def plus (n : Nat) (k : Nat) : Nat := 
  match k with 
  | Nat.zero => n 
  | Nat.succ k' => Nat.succ (plus n k')

def times (n : Nat) (k : Nat) : Nat := 
  match k with 
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat := 
  match k with 
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

-- def div (n : Nat) (k : Nat) : Nat := 
--   if n < k then 
--     0
--   else Nat.succ (div (n - k) k)
-- errored with 

-- fail to show termination for
--   div
-- with errors
-- argument #1 was not used for structural recursion
--   failed to eliminate recursive application
--     div (n - k) k

-- argument #2 was not used for structural recursion
--   failed to eliminate recursive application
--     div (n - k) k

-- structural recursion cannot be used

-- failed to prove termination, use `termination_by` to specify a well-founded relation

-- we need to manually prove div terminated
  