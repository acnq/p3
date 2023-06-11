-- The Monad Type Class 
namespace Hidden 
class Monad (m : Type → Type) where -- Is m here a Type → Type or just a Type 
  pure : α → m α  -- ok 
  bind : m α → (α → m β) → m β  -- andThen 
end Hidden 

instance : Monad Option where -- Option is m here 
  pure x := some x 
  bind opt next := 
    match opt with 
      | none => none 
      | some x => next x 

instance : Monad (Except ε) where
  pure x := Except.ok x 
  bind attempt next := 
    match attempt with
      | Except.error e => Except.error e 
      | Except.ok x => next x 

#check Option 
#check Except.ok 

-- infix version of bind is >>= 

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := 
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth => 
  lookup xs 6 >>= fun seventh => 
  pure (first, third, fifth, seventh)

def slowMammals : List String := 
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds

def getOrExcept (xs : List α) (i : Nat) : Except String α := 
  match xs[i]? with 
    | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
    | some x => Except.ok x 
#eval firstThirdFifthSeventh getOrExcept slowMammals 
#eval firstThirdFifthSeventh getOrExcept fastBirds

-- General Monad Operations 


def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => 
    f x >>= fun hd =>
    mapM f xs >>= fun tl => 
    pure (hd :: tl)

-- f determines which Monad instance will be used

-- Monad requires its paramter a single type, how to 
-- handle with State σ α 

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

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


def increment (howMuch : Int) : State Int Int := 
  get >>= fun i => 
  set (i + howMuch) >>= fun () =>
  pure i 

#eval mapM increment [1, 2, 3, 4, 5] 0

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α 
deriving Repr 
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next := 
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes 
    {log := thisOut ++ nextOut, val := nextRes}

def isEven (i : Int) : Bool := 
  i % 2 == 0
def save (data : α) : WithLog α Unit := 
  {log := [data], val := ()}

def saveIfEven (i : Int) : WithLog Int Int := 
  ( if isEven i then 
      save i 
    else pure ()) >>= fun () =>
  pure i 

#eval mapM saveIfEven [1, 2, 3, 4, 5]

-- Indentity Monad 
namespace Hidden 
def Id (t : Type) : Type := t 
end Hidden 

instance : Monad Id where
  pure x := x 
  bind x f := f x 

#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]

-- #eval mapM (· + 1) [1, 2, 3, 4, 5]
-- failed to synthesize instance
--   HAdd Nat Nat (?m.9319 ?m.9321)

-- #eval mapM (fun x => x) [1, 2, 3, 4, 5]
-- typeclass instance problem is stuck, it is often due to metavariables
--   Monad ?m.9319
-- with a function whose type doesn't provide any specific hints about 
-- which monad is to be used results in 
-- an "instance problem stuck" message:

-- Monad Contract 

-- First, pure should be a left identity of bind. 
-- That is, bind (pure v) f should be the same as f v. 
-- Secondly, pure should be a right identity of bind, 
-- so bind v pure is the same as v. 
-- Finally, bind should be associative, 
-- so bind (bind v f) g is the same as bind v (fun x => bind (f x) g)

-- Exercise 

inductive BinTree (α : Type) where
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 
deriving Repr

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf 
  | BinTree.branch l x r => 
    BinTree.mapM f l >>= fun lt => 
    f x >>= fun x' =>
    BinTree.mapM f r >>= fun rt => 
    pure (BinTree.branch lt x' rt)

open BinTree in 
def aTree := 
  branch 
    (branch
      (branch leaf 0 (branch leaf 1 leaf))
      2
      leaf)
    3
    (branch leaf 4 leaf)

#eval BinTree.mapM (m := Id) (· + 1) aTree