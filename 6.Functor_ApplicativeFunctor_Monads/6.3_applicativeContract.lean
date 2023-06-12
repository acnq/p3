-- The Applicative Contract
-- 4 rules
-- 1. identiy :               pure id <*> v = v
-- 2. function composition :  pure (· ∘ ·) <*> u <*> v <*> w =  u <*> (v <*> w)
-- 3. sequencng pure no-op :  pure f <*> pure x = pure (f x)
-- 4. associative :           u <*> pure x = pure (fun f => f x) <*> u 

-- All Applicative are Functors
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure  g <*> x 

namespace Hidden
class Applicative (f : Type → Type) extends Functor f where
  pure : α → f α 
  seq : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)   
end Hidden 

-- All Monads are Applicative Functors
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)

--replacing do notation
def seq' [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  f >>= fun g =>
  x () >>= fun y =>
  pure (g y)
namespace Hidden
class Monad (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β 
  seq f x := 
    bind f fun g =>
    bind (x ()) fun y => 
    pure (g y)

end Hidden 

-- Additional Stipulations

-- a type that provides both Applicative and Monad instances 
-- should not have an implementation of seq 
-- that works differently from the version 
-- that the Monad instance generates 
-- as a default implementation.

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr 

instance : HAppend (NonEmptyList α) (NonEmptyList α)  (NonEmptyList α) where
  hAppend := fun ⟨x, xs⟩ ⟨y, ys⟩ => ⟨x, xs ++ y :: ys⟩


inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α 
  | errors : NonEmptyList ε → Validate  ε α 
deriving Repr

def notFun : Validate String (Nat → String) := 
  .errors {head := "First error", tail := []}
def notArg : Validate String Nat := 
  .errors {head := "Second error", tail := []}

-- #check notFun <*> notArg