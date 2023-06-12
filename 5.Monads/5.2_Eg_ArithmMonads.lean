-- Example: Arithmetic in Monads

-- Arithmetic Expressions

inductive Expr (op : Type) where
  | const : Int → Expr op 
  | prim : op → Expr op → Expr op → Expr op 

inductive Arith where
  | plus 
  | minus 
  | times 
  | div 

open Expr in 
open Arith in 
def twoPlusThree : Expr Arith := 
  prim plus (const 2) (const 2)
-- 2 + 3

open Expr in 
open Arith in 
def fourteenDivided : Expr Arith := 
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))

-- 14 / (45 - 5 * 9)

-- Evaluating Expressions
def evaluateOption : Expr Arith → Option Int 
  | Expr.const i => pure i 
  | Expr.prim p e1 e2 => 
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 => 
    match p with 
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1  - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 ==  0 then none else pure (v1 / v2)

-- splitting 
def applyPrim : Arith → Int → Int → Option Int 
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then none else pure (x / y)

def evaluateOption' : Expr Arith → Option Int 
  | Expr.const i => pure i 
  | Expr.prim p e1 e2 =>
    evaluateOption' e1 >>= fun v1 =>
    evaluateOption' e2 >>= fun v2 =>
    applyPrim p v1 v2 

#eval evaluateOption' fourteenDivided


def applyPrim2 : Arith → Int → Int → Except String Int 
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => 
    if y == 0 then 
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateOption2 : Expr Arith → Except String Int 
  | Expr.const i => pure i 
  | Expr.prim p e1 e2 =>
    evaluateOption2 e1 >>= fun v1 =>
    evaluateOption2 e2 >>= fun v2 =>
    applyPrim2 p v1 v2 

def applyPrimOption : Arith → Int → Int → Option Int 
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => 
    if y == 0 then
      none 
    else pure (x / y)

def applyPrimExcept : Arith → Int → Int → Except String Int 
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => 
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int): Expr Arith → m Int 
  | Expr.const i => pure i 
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 => 
    applyPrim p v1 v2 

#eval evaluateM applyPrimOption fourteenDivided
#eval evaluateM applyPrimExcept fourteenDivided 

-- further improvement
def applyDivOption (x : Int) (y : Int) : Option Int := 
  if y == 0 then
    none
  else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int := 
  if y == 0 then 
    Except.error s!"Tried to divide {x} by zero"
  else pure (x / y)

def applyPrim3 [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int 
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y 

def evaluateM3 [Monad m] (applyDiv : Int → Int → m Int) : Expr Arith → m Int 
  | Expr.const i => pure i 
  | Expr.prim p e1 e2 =>
    evaluateM3 applyDiv e1 >>= fun v1 =>
    evaluateM3 applyDiv e2 >>= fun v2 => 
    applyPrim3 applyDiv p v1 v2 

-- Further Effects
inductive Prim (special : Type) where
  | plus 
  | minus 
  | times
  | other : special → Prim special 

inductive CanFail where
  | div 

def divOption : CanFail → Int → Int → Option Int 
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int 
  | CanFail.div, x, y => 
    if y == 0 then 
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim4 [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int  
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y 

def evaluateM4 [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim special) → m Int 
  | Expr.const i => pure i 
  | Expr.prim p e1 e2 =>
    evaluateM4 applySpecial e1 >>= fun v1 => 
    evaluateM4 applySpecial e2 >>= fun v2 => 
    applyPrim4 applySpecial p v1 v2 


-- No Effects
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int := 
  nomatch op 

open Expr Prim in 
#eval evaluateM4 (m := Id) applyEmpty (prim plus (const 5) (const (-14)))

-- Nondeterministic Search
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α


def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.fromList : List α → Many α 
  | [] => Many.none 
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.take : Nat → Many α → List α 
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more  x xs => x :: (xs ()).take n 

def Many.takeAll : Many α → List α 
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll


def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)

-- notice bind and one of Many obey monad contract:
-- left, right identity and associativity
instance : Monad Many where
  pure := Many.one
  bind := Many.bind 


def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then 
      pure []
    else 
      Many.none
  | x :: xs => 
    if x > goal then 
      addsTo goal xs 
    else 
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
          pure (x :: answer))

inductive NeedsSearch
  | div
  | choose 

def applySearch : NeedsSearch → Int → Int → Many Int 
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y => 
    if y == 0 then 
      Many.none
    else Many.one (x / y)

open Expr Prim NeedsSearch
#eval (evaluateM4 applySearch (prim plus (const 1) (prim (other choose) (const 2) (const 5)))).takeAll
#eval (evaluateM4 applySearch (prim plus (const 1) (prim (other div) (const 2) (const 0)))).takeAll
#eval (evaluateM4 applySearch (prim (other div) (const 90) (prim plus (prim (other choose) (const (-5)) (const 5)) (const 5)))).takeAll

-- Custom Environments
--  The mapping from function names to function implementations
--  is called an *environment*.

-- Using functions as a monad 
-- is typically called a *reader* monad.
def Reader (ρ : Type) (α : Type) : Type := ρ → α
def read : Reader ρ ρ := fun env => env 

-- ρ for environments
def Reader.pure (x : α) : Reader ρ α := fun _ => x 

def Reader.bind_ {ρ : Type} {α : Type} {β : Type} (result : ρ → α) (next : α → ρ → β) : ρ → β := 
  fun env => next (result env) env 

def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env

-- bind is bind and pure is pure, they obey monad contracts
instance : Monad (Reader ρ) where 
  pure x := fun _ => x
  bind x f := fun env => f (x env) env 

abbrev Env : Type := List (String × (Int → Int → Int))
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int := 
  read >>= fun env =>
  match env.lookup op with
    | none => pure 0
    | some f => pure (f x y)

open Expr Prim in 
#eval evaluateM4 applyPrimReader (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv

-- Exercise 
-- checking contracts of State σ and Except ε

-- readers with failure
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α
def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α


def ReaderOption.pure (x : α) : ReaderOption ρ α := fun _ => some x   
def ReaderOption.bind (action : ReaderOption ρ α) (next : α → ReaderOption ρ β) : ReaderOption ρ β := 
  fun env => 
    match action env with 
      | none => none 
      | some x => next x env 
      
instance : Monad (ReaderOption ρ) where
  pure := ReaderOption.pure
  bind := ReaderOption.bind

def ReaderExcept.pure (x : α) : ReaderExcept ε ρ α := fun _ => Except.ok x 
def ReaderExcept.bind (action : ReaderExcept ε ρ α) (next : α → ReaderExcept ε ρ β) : ReaderExcept ε ρ β := 
  fun env =>
    match action env with 
      | Except.ok x => next x env
      | Except.error e => Except.error e 

instance : Monad (ReaderExcept ε ρ) where
  pure := ReaderExcept.pure
  bind := ReaderExcept.bind

-- Tracing Evaluator
-- give up
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α


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

def applyTraced (op : ToTrace (Prim empty)) (x y : Int) : WithLog (Prim empty × Int × Int) Int :=
  match op with
  | ToTrace.trace times =>
    let result := x * y
    { log := [(Prim.times, x, y)],
      val := result }
  | ToTrace.trace plus =>
    let result := x + y
    { log := [(Prim.plus, x, y)],
      val := result }
  | ToTrace.trace minus =>
    let result := x - y
    { log := [(Prim.minus, x, y)],
      val := result }
  | _ =>
    let result := 0
    { log := [(Prim.minus, 0, 0)],
      val := result }

deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim


open Expr Prim ToTrace in
#eval evaluateM applyTraced (prim (other (trace times)) (prim (other (trace plus)) (const 1) (const 2)) (prim (other (trace minus)) (const 3) (const 4)))
