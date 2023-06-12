-- do-Notation for Monads

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := 
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def firsthThirdFIfthSeventh' [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

inductive BinTree (α : Type) where
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 
deriving Repr
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

-- def number (t : BinTree α) : BinTree (Nat × α) :=
--   let rec helper : BinTree α → State Nat (BinTree (Nat × α))
--     | BinTree.leaf => pure BinTree.leaf
--     | BinTree.branch left x right => do
--       let numberedLeft ← helper left
--       let n ← get
--       set (n + 1)
--       let numberedRight ← helper right
--       ok (BinTree.branch numberedLeft (n, x) numberedRight)
--   (helper t 0).snd

def mapM_ [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd => 
    mapM_ f xs >>= fun tl =>
    pure (hd :: tl)

def mapM [Monad m] (f : α → m β) : List α → m (List β) 
  | [] => pure []
  | x :: xs => do 
    let hd ← f x
    let tl ← mapM f xs 
    pure (hd :: tl)

def mapM__ [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do 
    pure ((← f x) :: (← mapM f xs))

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next := 
    fun s => 
      let (s', x) := first s 
      next x s'

def get : State σ σ := 
  fun s => (s, s)

def set (s : σ) : State σ Unit := 
  fun _ => (s, ())

def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      pure (BinTree.branch (← helper left) ((← increment), x) (← helper right))
  (helper t 0).snd




