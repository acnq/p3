-- A Monad Construction Kit 
-- monad transformer consists:
-- 1. definition/datatype T taking a monad as an arg.
-- has a type (Type u → Type v) → Type u → Type v
-- 2. instance T m relying  on the instance of Monad m 
-- 3. MonadLift instance translate actions of m α into T m α 
-- for ∀ m  

-- Failure with OptionT 
namespace Hidden
def OptionT (m : Type u → Type v) (α : Type u) : Type v := 
  m (Option α)
end Hidden 

def getSomeInput : OptionT IO String := do 
  let input ← (← IO.getStdin).getLine 
  let trimmed := input.trim 
  if trimmed == "" then 
    failure 
  else pure trimmed   

structure UserInfo where
  name : String 
  favoriteBeetle : String

def getUserInfo : OptionT IO UserInfo := do 
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favorite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩ 

def interact : IO Unit := do 
  match ← getUserInfo with
  | none => IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ => IO.println s!"Hello {name}, whose favorite beetle is {beetle}."

-- The Monad Instance 

-- instance [Monad m] : Monad (OptionT m) where
--   pure x := pure (some x)
--   bind action next := do 
--     match (← action) with 
--       | none => pure none 
--       | some v => next v 

-- application type mismatch
--   pure (some x)
-- argument
--   some x
-- has type
--   Option α✝ : Type ?u.28
-- but is expected to have type
--   α✝ : Type ?u.28

instance [Monad m] : Monad (OptionT m) where
  pure x := (pure (some x) : m (Option _))
  bind action next := (do
    match (← action) with
    | none => pure none 
    | some v => next v : m (Option _))

namespace Hidden3
structure OptionT (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Option α)
end Hidden3

namespace Hidden4
def OptionT.mk (x : m (Option α)) : OptionT m α := x 
def OptionT.run (x : OptionT m α) : m (Option α) := x 
end Hidden4

instance [Monad m] : Monad (OptionT m) where 
  pure x := OptionT.mk (pure (some x))
  bind action next := OptionT.mk do 
    match ← action with 
    | none => pure none 
    | some v => next v 

-- An Alternative Instance 
instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.mk (pure none)
  orElse x y := OptionT.mk do 
    match ← x with 
    | some result => pure (some result)
    | none => y ()

-- Lifting 
instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do 
    pure (some (← action))

-- Exception

namespace Hidden4
def ExceptT (ε : Type u) (m : Type u →  Type v) (α : Type u) : Type v :=
  m (Except ε α)

def ExceptT.mk {ε α : Type u} (x : m (Except ε α)) : ExceptT ε m α := x 
def ExceptT.run {ε α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x 
end Hidden4 

instance {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (ExceptT ε m) where 
  pure x := ExceptT.mk (pure (Except.ok x))
  bind result next := ExceptT.mk do 
    match ← result with
    | .error e => pure (.error e)
    | .ok x => next x  

-- details: ε α the same universe level 
-- otherwise 
namespace Hidden5
-- def ExceptT.mk (x : m (Except ε α)) : ExceptT ε m α := x 
-- instance {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (ExceptT ε m) where
--   pure x := ExceptT.mk (pure (Except.ok x))
--   bind result next := ExceptT.mk do 
--     match (← result) with 
--     | .error e => pure (.error e)
--     | .ok x => next x 

-- end Hidden5
-- stuck at solving universe constraint
--   max ?u.12286 ?u.12287 =?= u
-- while trying to unify
--   ExceptT ε m α✝
-- with
--   (ExceptT ε m α✝) ε m α✝
end Hidden5

instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk (pure action)

instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk (.ok <$> action)

-- Type classes for Exceptions
namespace Hidden
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where 
  throw : ε → m α 
  tryCatch : m α → (ε → m α) → m α 
end Hidden 

inductive Err where
  | divByZero 
  | notANumber : String → Err 

def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int := 
  if k == 0 then 
    throw .divByZero
  else pure (n / k)

def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int := 
  match s.toInt? with 
  | none => throw (.notANumber s)
  | some i => pure i 

def divFrontend_ [Monad m] [MonadExcept Err m] (n k : String) : m String := 
  tryCatch (do pure (toString (← divBackend (← asNumber n) (← asNumber k))))
    fun 
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure s!"Not a number : \"{s}\""

def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String := 
  try 
    pure (toString (← divBackend (← asNumber n) (← asNumber k)))
  catch 
    | .divByZero => pure "Division by zero!"
    | .notANumber s => pure s!"Not a number : \"{s}\""

namespace Hidden 
def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) := 
  σ → m (α × σ)
end Hidden 

instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do 
    let (v, s') ← result s 
    next v s'

structure LetterCounts where
  vowels : Nat 
  consonants : Nat 
deriving Repr 

inductive Err2 where
  | notALetter : Char → Err2 
deriving Repr 

def vowels := 
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants := 
  let lowerConsonants := "bcdefghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

def countLetters (str : String) : StateT LetterCounts (Except Err2) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else -- modified or non-English letter
            pure st
        else throw (.notALetter c)
      set st'
      loop cs
  loop str.toList

-- modify : transforms the state using a function
def countLetters2 (str : String) : StateT LetterCounts (Except Err2) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

-- modifyGet : allows the function to both compute a return value 
-- and transform an old state in a single step.
-- The function returns a pair in which the first element is the return value, 
-- and the second element is the new state; 
-- modify just adds the constructor of Unit to the pair used in modifyGet

namespace Hidden
def modify [MonadState σ m] (f : σ → σ) : m Unit := 
  modifyGet fun s => ((), f s)

class MonadState (σ : outParam (Type u)) (m : Type u → Type v) : Type (max (u + 1) v) where 
  get : m σ 
  set : σ → m PUnit
  modifyGet : (σ → α × σ) → m α
end Hidden 

-- `Of` Classes and `The` Functions
-- `MonadStateOf` is like `MonadState`, but without an `outParam` modifier.

-- `getThe`
-- (σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → m σ 

-- `modifyThe`
-- (σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → (σ → σ) → m PUnit

-- Transformers and `Id`





