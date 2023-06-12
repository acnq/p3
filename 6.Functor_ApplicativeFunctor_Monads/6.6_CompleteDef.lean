-- The Complete Definitions

-- Functor
namespace Hidden
class Functor (f : Type u → Type v) : Type (max (u + 1) v) where
  map : {α β : Type u} → (α → β) → f α → f β 
  mapConst : {α β : Type u} → α → f β → f α := 
    Function.comp map (Function.const _)
   
-- Function.comp is function composition, 
-- which is typically written with the ∘ operator
-- Function.const is the constant function, 
-- which is a two-argument function 
-- that ignores its second argument
-- here used since API demands a function but a program 
-- doesn't need to compute the result for different args.

def simpleConst (x : α) (_ : β) : α := x 
#eval [1, 2, 3].map (simpleConst "same")

-- why must u + 1
class Functor' (f : Type u → Type v) : Type (max (u + 1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
inductive Functor'' (f : Type u → Type v) : Type (max (u + 1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor'' f  

-- reason: map method (passed as an arg to Functor.mk) contains 2 Type u as arg
-- so the function itself should be in Type (u + 1)

-- Applicative
class Pure (f : Type u → Type v) : Type (max (u + 1) v) where
  pure {α : Type u} : α → f α

class Seq (f : Type u → Type v) : Type (max (u + 1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

class SeqRight (f : Type u → Type v) : Type (max (u + 1) v) where 
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β 
class SeqLeft (f : Type u → Type v) : Type (max (u + 1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α 

class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map       := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft   := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight  := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b


-- Seq.seq (Functor.map (Function.const _) a) b
-- is
-- fun a b => Seq.seq ((fun x _ => x) <$> a) b
-- Here, a has type f α, and f is a functor (e.g. List Option)
-- If f is List
-- then (fun x _ => x) <$> [1, 2, 3] 
-- evaluates to [fun _ => 1, fun _ => 2, fun _ => 3].
-- If f is Option, then (fun x _ => x) <$> some "hello" 
-- evaluates to some (fun _ => "hello"). 
-- In each case, the values in the functor are replaced by functions 
-- that return the original value, 
-- ignoring their argument. 
-- When combined with seq, 
-- this function discards the values from seq's second argument.

-- const has additional arg id 
-- fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
-- ===>
-- fun a b => Seq.seq ((fun _ => id) <$> a) b
-- ===>
-- fun a b => Seq.seq ((fun _ => fun x => x) <$> a) b
-- ===>
-- fun a b => Seq.seq ((fun _ x => x) <$> a) b
-- (fun _ x => x) <$> [1, 2, 3] is equivalent to [fun x => x, fun x => x, fun x => x], 
-- and (fun _ x => x) <$> some "hello" is equivalent to some (fun x => x). 
-- In other words, (fun _ x => x) <$> a preserves the overall shape of a, 
-- but each value is replaced by the identity function.

-- Monad
class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β 

class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u + 1) v) where
  map       f x := bind x (Function.comp pure f)
  seq       f x := bind f fun y => Functor.map y (x ())
  seqLeft   x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight  x y := bind x fun _ => y ()


