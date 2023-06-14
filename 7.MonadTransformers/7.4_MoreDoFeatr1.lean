-- More do Features
-- do-notation provides syntax for using monad transformers

-- Single-Branched `if`
structure LetterCounts where
  vowels : Nat 
  consonants : Nat 
deriving Repr 
inductive Err where
  | notALetter : Char → Err
deriving Repr 

def vowels := 
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)
def consonants := 
  let lowerConsonants := "bcdefghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)


def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
      else throw (.notALetter c) -- else pure () is automatically inserted
      loop cs
  loop str.toList

def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit 
  | [] => pure ()
  | x :: xs => do 
    if ← p x then 
      modify (· + 1)
    count p xs 

-- unless E1 do STMT = if not E1 then STMT
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit 
  | [] => pure ()
  | x :: xs => do 
    unless ← p x do 
      modify (· + 1)
    countNot p xs 

-- Early Return 
namespace Hidden 
def List.find? (p : α → Bool) : List α → Option α 
  | [] => none 
  | x :: xs => 
    if p x then 
      some x 
    else 
      find? p xs 

def List.find2? (p : α → Bool) : List α → Option α 
  | [] => none 
  | x :: xs => do 
    if p x then return x 
    find2? p xs 

def runCatch [Monad m] (action : ExceptT α m α) : m α := do 
  match ← action with 
  | Except.ok x => pure x 
  | Except.error x => pure x 


def List.find3? (p : α → Bool) : List α → Option α 
  | [] => failure 
  | x :: xs =>
    runCatch do 
      if p x then throw x else pure ()
      monadLift (find3? p xs)


def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).trim
  if name == "" then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0


-- lean --run EarlyReturn.lean

  
  
  
