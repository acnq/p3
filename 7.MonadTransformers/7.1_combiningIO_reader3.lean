namespace Hidden
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) := 
  ρ → m α 
end Hidden 

-- ρ : env that is accessible to reader
-- m : monad being transformed
-- α : type of values being returned by the mnadic computation
-- both α and ρ are in the same univ 
-- cause' the operator  that retrieves env in monad will have type m ρ
structure Config where
  useASCII : Bool := false
  currentPrefix : String := "" 

abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α 

def read [Monad m] : ReaderT ρ m ρ := 
  fun env => pure env 

namespace Hidden
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) : Type (max (u + 1) v) where
  read : m ρ
instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := fun env => pure env 

export MonadReader (read)
end Hidden

instance [Monad m] : Monad (ReaderT ρ m) where
  pure x := fun _ => pure x 
  bind result next := fun env => do 
    let v ← result env 
    next v env 


namespace Hidden
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where 
  monadLift : {α : Type u} → m α → n α 
end Hidden 

-- The method monadLift translates from the monad m to the monad n

instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action 

def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg
inductive Entry where
  | file : String → Entry
  | dir : String → Entry

def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none 
  | some name =>
    pure (some (if (← path.isDir) then .dir name else .file name))


def Config.preFile (cfg : Config) := 
  if cfg.useASCII then "|--" else "├──"
def Config.preDir (cfg : Config) := 
  if cfg.useASCII then "|  " else "│  "

def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← MonadReader.read).currentPrefix} {file}" -- the book isn't right here
def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← MonadReader.read).currentPrefix} {dir}/" -- the same as above
def Config.inDirectory (cfg : Config) : Config := 
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}


namespace Hidden
class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α 
export MonadWithReader (withReader)
end Hidden 

instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action := 
    fun cfg => action (change cfg)

def doList [Applicative f] : List α → (α → f Unit) → f Unit 
  | [], _ => pure ()
  | x :: xs , action => 
    action x *>
    doList xs action

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do 
  match ← toEntry path with 
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) => 
      showDirName name 
      let contents ← path.readDir 
      withReader (·.inDirectory)
        (doList contents.toList fun d =>
          dirTree d.path)
def usage : String := 
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"
          
def configFromArgs: List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _ => none 


def main (args : List String) : IO UInt32 := do 
  match configFromArgs args with 
  | some config => 
    (dirTree (← IO.currentDir)).run config 
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {args}"
    IO.eprintln usage 
    pure 1 

-- lean --run 7.1_combiningIO_reader3.lean