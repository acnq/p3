-- Applicative Functors

-- An applicative functor is a functor 
-- that has two additional operations available: 
-- pure and seq.
-- pure is like pure in Monad
-- seq is much like map: 
-- it allows a function to be used 
-- in order to transform the contents of a datatype.

instance : Applicative Option where
  pure x := .some x 
  seq f x := 
    match f with
      | none => none
      | some g => g <$> x ()


instance : Applicative (Except ε) where
  pure x := .ok x 
  seq f x := 
    match f with 
      | .error e => .error e 
      | .ok g => g <$> x ()

structure Pair (α β : Type) : Type where
  first : α 
  second : β 

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

-- challenge in Applicative : How to define pure
-- def Pair.pure (x : β) : Pair α β := Pair.mk _ x 

-- A Non-Monadic Applicative
-- User Input 
structure RawInput where
  name : String 
  birthYear : String 
deriving Repr

-- Subtypes
namespace Hidden
structure Subtype {α : Type} (p : α → Prop) where
  val : α
  property : p val  
end Hidden

-- if p has type α → Prop
--  the type Subtype p can be written as {x : α // p x} or even {x // p x}
def FastPos : Type := {x : Nat // x > 0}

def one : FastPos := ⟨1, by simp⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none 

-- Validate Input 
structure CheckedInput (thisYear : Nat) : Type where 
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
deriving Repr 

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

instance : Functor (Validate ε) where
  map f 
    | .ok x => .ok (f x)
    | .errors errs => .errors errs 

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String 
def reportError (f : Field) (msg : String) : Validate (Field × String) α := 
  .errors {head := (f, msg), tail := []}

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} := 
  if h : name = "" then
    reportError "name" "Required"
    else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β := 
  match val with
    | .errors errs => .errors errs
    | .ok x => next x 

def checkYearIsNat (year : String) : Validate (Field × String) Nat := 
  match year.trim.toNat? with 
    | none => reportError "birth year" "Must be digits"
    | some n => pure n 

def checkBirthYear (thisYear year : Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} := 
  if h : year > 1900 then
    if h' : year ≤ thisYear then 
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

def checkInput (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat


#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}


