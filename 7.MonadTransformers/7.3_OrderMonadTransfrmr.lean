-- Ordering Monad Transformers

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
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)

#eval countLetters (m := M1) "hello" ⟨0, 0⟩ 
#eval countLetters (m := M2) "hello" ⟨0, 0⟩ 

#eval countLetters (m := M1) "hello!" ⟨0, 0⟩
#eval countLetters (m := M2) "hello!" ⟨0, 0⟩ 

def countWithFallback 
    [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit := 
  try 
    countLetters str
  catch _ =>
    countLetters "Fallback"

#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩

#eval countWithFallback (m := M1) "hello!" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello!" ⟨0, 0⟩

-- Communting Monads
-- 2 monad transformers are said to commute if they can be re-ordered 
-- without the meaning of the program changing