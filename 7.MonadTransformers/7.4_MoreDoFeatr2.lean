-- Loops 

-- Looping with ForM 

namespace Hidden
class ForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where 
  forM [Monad m] : γ → (α → m PUnit) → m PUnit 


-- m is a monad with some desired effects, 
-- γ is the collection to be looped over, 
-- and α is the type of elements from the collection.

def List.forM [Monad m] : List α → (α → m PUnit) → m PUnit 
  | [], _ => pure ()
  | x :: xs, action => do 
    action x 
    forM xs action   

instance : ForM m (List α) α where 
  forM := List.forM

end Hidden 

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


def countLetters (str : String) : StateT LetterCounts (Except Err) Unit := 
  forM str.toList fun c => do 
    if c.isAlpha then 
      if vowels.contains c then 
        modify fun st => {st with vowels := st.vowels + 1}
      else if consonants.contains c then 
        modify fun st => {st with consonants := st.consonants + 1}
    else throw (.notALetter c)

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
  | Many.none, _ => pure ()
  | Many.more first rest, action => do 
    action first 
    forM (rest ()) action 

instance : ForM m (Many α) α where 
  forM := Many.forM

structure AllLessThan where 
  num : Nat 

def AllLessThan.forM [Monad m] (coll : AllLessThan) (action : Nat → m Unit) : m Unit := 
  let rec countdown : Nat → m Unit 
    | 0 => pure ()
    | n + 1 => do 
      action n 
      countdown n 
  countdown coll.num

instance : ForM m AllLessThan Nat where 
  forM := AllLessThan.forM 

#eval forM { num := 5 : AllLessThan } IO.println

structure LinesOf where 
  stream : IO.FS.Stream

partial def LinesOf.forM (readFrom : LinesOf) (action : String → IO Unit) : IO Unit := do 
  let line ← readFrom.stream.getLine 
  if line == ""  then return ()
  action line 
  forM readFrom action 

instance : ForM IO LinesOf String where 
  forM := LinesOf.forM 

def main (argv : List String) : IO UInt32 := do 
  if argv != [] then 
    IO.eprintln "Unexpected arguments"
    return 1 
  
  forM (LinesOf.mk (← IO.getStdin)) fun line => do 
    if line.any (·.isAlpha) then 
      IO.print line 

  return 0 
  