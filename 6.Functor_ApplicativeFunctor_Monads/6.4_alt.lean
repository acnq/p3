-- Alternatives
-- recovery from failure

abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) → 
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) → 
    NonEmptyString → 
    LegacyCheckedInput
  | company : 
    NonEmptyString → 
    LegacyCheckedInput
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


def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α := 
  match a with 
    | .ok x => .ok x 
    | .errors errs1 =>
      match b () with
        | .ok x => .ok x 
        | .errors errs2 => .errors (errs1 ++ errs2)

namespace Hidden
class OrElse (α : Type) where
  orElse : α → (Unit → α) → α
end Hidden

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def Field := String 
def reportError (f : Field) (msg : String) : Validate (Field × String) α := 
  .errors {head := (f, msg), tail := []}


def checkThat (condition : Bool) (field : Field) (msg : String) : Validate (Field × String) Unit := 
  if condition then pure () else reportError field msg 

structure RawInput where
  name : String 
  birthYear : String 
deriving Repr
def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} := 
  if h : name = "" then
    reportError "name" "Required"
    else pure ⟨name, h⟩

def checkCompany_ (input : RawInput) : Validate (Field × String) LegacyCheckedInput := 
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" <*>
    checkName input.name

namespace Hidden
class SeqRight (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β
end Hidden

def checkCompany__ (input : RawInput) : Validate (Field × String) LegacyCheckedInput := 
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name 

def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput := 
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  .company <$> checkName input.name

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def checkYearIsNat (year : String) : Validate (Field × String) Nat := 
  match year.trim.toNat? with 
    | none => reportError "birth year" "Must be digits"
    | some n => pure n 
def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β := 
  match val with
    | .errors errs => .errors errs
    | .ok x => next x 

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput := 
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
      pure input.name 

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput := 
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*> 
      checkName input.name

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input 

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩
#eval checkLegacyInput ⟨"", "1970"⟩

-- Alternative Class

-- · describes applicative functors 
-- that have additional operators for failure and recovery
namespace Hidden
class Alternative (f : Type → Type) extends Applicative f where
  failure : f α 
  orElse : f α → (Unit → f α) → f α
end Hidden 

instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse

instance : Alternative Option where
  failure := none
  orElse 
    | some x, _ => some x
    | none, y => y ()

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.orElse : Many α → (Unit → Many α) → Many α 
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
instance : Monad Many where
  pure := Many.one
  bind := Many.bind 
def Many.take : Nat → Many α → List α 
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more  x xs => x :: (xs ()).take n 

def Many.takeAll : Many α → List α 
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse

-- guard : causes failure when a decidable proposition is false
namespace Hidden2
def guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then 
    pure ()
  else failure
end Hidden2

def Many.countdown : Nat → Many Nat 
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do 
  let k ← Many.countdown (n + 1)
  guard (k % 2 == 0)
  guard (n % k == 0)
  pure k 

#eval (evenDivisors 20).takeAll 