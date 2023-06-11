-- Checking for none : Don't Repeat Yourself
def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) := 
  match xs[0]? with
    | none => none
    | some first =>
      match xs[2]? with
        | none => none
        | some third =>
          some (first, third)

def firstThirdFifth (xs : List α) : Option (α × α × α) := 
  match xs[0]? with 
    | none => none
    | some first =>
      match xs[2]? with
        | none => none  
        | some third =>
          match xs[4]? with
            | none => none
            | some fifth =>
              some (first, third, fifth)


def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) := 
  match xs[0]? with 
    | none => none
    | some first =>
      match xs[2]? with
        | none => none  
        | some third =>
          match xs[4]? with
            | none => none
            | some fifth =>
              match xs[6]? with
                | none => none
                | some seventh =>
                  some (first, third, fifth, seventh)
              
def andThen (opt : Option α) (next : α → Option β) : Option β := 
  match opt with
    | none => none  
    | some x => next x 

def firstThird' (xs : List α) : Option (α × α) := 
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)

def firstThird'' (xs : List α) : Option (α × α) := 
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))


-- Inflix Operators
infixl:55 " ~~> " => andThen

def firstThirdInfix4 (xs : List α) : Option (α × α) := 
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)

def firstThirdFifthSeventh' (xs : List α) : Option (α × α × α × α) := 
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)


-- Propogating Error Messages
namespace Hidden
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α 
  | ok : α → Except ε α  
deriving BEq, Hashable, Repr
end Hidden 

def get (xs : List α) (i : Nat) : Except String α := 
  match xs[i]? with
    | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
    | some x => Except.ok x

def ediblePlants : List String := 
  [ "ramsons", "sea plantation", "sea buckthorn", "garden nasturtium"]

#eval get ediblePlants 2 

#eval get ediblePlants 4 

def first' (xs : List α) : Except String α := 
  get xs 0 

def firstThird''' (xs : List α) : Except String (α × α) := 
  match get xs 0 with
    | Except.error msg => Except.error msg
    | Except.ok first =>
      match get xs 2 with
        | Except.error msg =>Except.error msg
        | Except.ok third =>
          Except.ok (first, third)

def firstThirdFifth4 (xs : List α) : Except String (α × α × α) := 
  match get xs 0 with 
    | Except.error msg => Except.error msg
    | Except.ok first =>
      match get xs 2 with
        | Except.error msg => Except.error msg
        | Except.ok third =>
          match get xs 4 with 
            | Except.error msg => Except.error msg
            | Except.ok fifth =>
              Except.ok (first, third, fifth)

def firstThirdFifthSeventh'' (xs : List α) : Except String (α × α × α × α) := 
  match get xs 0 with 
    | Except.error msg => Except.error msg
    | Except.ok first =>
      match get xs 2 with
        | Except.error msg => Except.error msg
        | Except.ok third =>
          match get xs 4 with 
            | Except.error msg => Except.error msg
            | Except.ok fifth =>
              match get xs 6 with 
                | Except.error msg => Except.error msg
                | Except.ok seventh =>
                  Except.ok (first, third, fifth, seventh)

def andThen' (attempt : Except e α) (next : α → Except e β) : Except e β := 
  match attempt with
    | Except.error msg => Except.error msg
    | Except.ok x => next x 


def firstThird5 (xs : List α) : Except String (α × α) := 
  andThen' (get xs 0) fun first =>
  andThen' (get xs 2) fun third =>
  Except.ok (first, third)

def ok (x : α) : Except ε α := Except.ok x 
def fail (err : ε) : Except ε α := Except.error err

def get' (xs : List α) (i : Nat) : Except String α := 
  match xs[i]? with
    | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
    | some x => ok x 

infixl:55 " ~~> " => andThen' 

def firstThird6 (xs : List α) : Except String (α × α) :=
  get' xs 0 ~~> fun first =>
  get' xs 2 ~~> fun third =>
  ok (first, third)

def firstThirdFifthSeventh6 (xs : List α) : Except String (α × α × α × α) :=
  get' xs 0 ~~> fun first =>
  get' xs 2 ~~> fun third =>
  get' xs 4 ~~> fun fifth =>
  get' xs 6 ~~> fun seventh => 
  ok (first, third, fifth, seventh)


-- Logging 
def isEven (i : Int) : Bool := 
  i % 2 == 0

def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)

inductive BinTree (α : Type) where
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 
deriving Repr

def inorderSum : BinTree Int → List Int × Int 
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum l 
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum r 
    (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)

def sumAndFindEvens' : List Int → List Int × Int 
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens' is 
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α 

def andThen2 (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ := 
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok2 (x : β) : WithLog α β := {log := [], val := x} 
def save (data : α) : WithLog α Unit := 
  {log := [data], val := ()}

def sumAndFindEvens2 : List Int → WithLog Int Int 
  | [] => ok2 0
  | i :: is =>
    andThen2 (if isEven i then save i else ok2 ()) fun () =>
    andThen2 (sumAndFindEvens2 is) fun sum =>
      ok2 (i + sum)

def inorderSum2 : BinTree Int →  WithLog Int Int
  | BinTree.leaf => ok2 0
  | BinTree.branch l x r =>
    andThen2 (inorderSum2 l) fun leftSum =>
    andThen2 (save x) fun () =>
    andThen2 (inorderSum2 r) fun rightSum =>
    ok2 (leftSum + x + rightSum)

infixl:55 " ~~> " => andThen2 


def sumAndFindEvens3 : List Int → WithLog Int Int 
  | [] => ok2 0
  | i :: is =>
    (if isEven i then save i else ok2 ()) ~~> fun () =>
    sumAndFindEvens3 is ~~> fun sum =>
    ok2 (i + sum)

def inorderSum3 : BinTree Int → WithLog Int Int 
  | BinTree.leaf => ok2 0
  | BinTree.branch l x r =>
    inorderSum3 l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum3 r ~~> fun rightSum =>
    ok2 (leftSum + x + rightSum)

-- Numbering Tree Nodes

open BinTree in 
def aTree := 
  branch 
    (branch
      (branch leaf "a" (branch leaf "b" leaf))
      "c"
      leaf)
    "d"
    (branch leaf "e" leaf)

-- ```python 
-- class Branch:
--     def __init__(self, value, left=None, right=None):
--         self.left = left
--         self.value = value
--         self.right = right
--     def __repr__(self):
--         return f'Branch({self.value!r}, left={self.left!r}, right={self.right!r})'

-- def number(tree):
--     num = 0
--     def helper(t):
--         nonlocal num
--         if t is None:
--             return None
--         else:
--             new_left = helper(t.left)
--             new_value = (num, t.value)
--             num += 1
--             new_right = helper(t.right)
--             return Branch(left=new_left, value=new_value, right=new_right)

--     return helper(tree)

-- a_tree = Branch("d",
--                 left=Branch("c",
--                             left=Branch("a", left=None, right=Branch("b")),
--                             right=None),
--                 right=Branch("e"))

-- >>> number(a_tree)
-- Branch((3, 'd'), left=Branch((2, 'c'), left=Branch((0, 'a'), left=None, right=Branch((1, 'b'), left=None, right=None)), right=None), right=Branch((4, 'e'), left=None, right=None))

def number (t : BinTree α) : BinTree (Nat × α) := 
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch left x right =>
      let (k, numberedLeft) := helper n left 
      let (i, numberedRight) := helper (k + 1) right
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
    (helper 0 t).snd 

-- taking an input state as an argument 
-- and returning an output state together with a value:
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

-- ok is a function that returns the input state unchanged, 
-- along with the provided value:
def ok3 (x : α) : State σ α := 
  fun s => (s, x)

--  Reading the current value is accomplished with a function 
--  that places the input state unmodified into the output state, 
--  and also places it into the value field:
def get3 : State σ σ := 
  fun s => (s, s)

-- Writing a new value consists of ignoring the input state, 
-- and placing the provided new value into the output state:
def set (s : σ) : State σ Unit := 
  fun _ => (s, ())

-- two computations that use state can be sequenced 
-- by finding both the output state 
-- and return value of the first function, 
-- then passing them both into the next function:
def andThen3 (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s => 
    let (s', x) := first s 
    next x s' 
infixl:55 " ~~> " => andThen3 

def number2 (t : BinTree α) : BinTree (Nat × α) := 
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok3 BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get3 ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok3 (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd  

-- Monads : A Funtional Design Pattern

-- While the idea of monads is derived from a branch of mathematics called category theory, 
-- no understanding of category theory is needed in order to use them for programming.
--  The key idea of monads is that each monad encodes a particular kind of side effect 
--  using the tools provided by the pure functional language Lean