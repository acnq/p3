structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""


def ConfigIO (α : Type) : Type := 
  Config → IO α 

instance : Monad ConfigIO where
  pure x := fun _ => pure x 
  bind result next := fun cfg => do
    let v ← result cfg 
    next v cfg 
def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg 

def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg

def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α := 
  fun cfg => action (change cfg)

def runIO (action : IO α) : ConfigIO α := 
  fun _ => action

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

def Config.fileName (cfg : Config) (file : String) : String := 
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"
def Config.dirName (cfg : Config) (dir : String) : String := 
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"
def Config.inDirectory (cfg : Config) : Config := 
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}


def showFileName (file : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).fileName file))

def showDirName (dir : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).dirName dir))
def doList [Applicative f] : List α → (α → f Unit) → f Unit 
  | [], _ => pure ()
  | x :: xs , action => 
    action x *>
    doList xs action

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do 
  match ← runIO (toEntry path) with 
    | none => pure ()
    | some (.file name) => showFileName name 
    | some (.dir name) => 
      showDirName name 
      let contents ← runIO path.readDir 
      locally (·.inDirectory)
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

-- Monad transformer 
-- takes a monad as an argument and returns a new monad.
-- consists of 
-- A definition of the transformer, typically function from types to types
-- Monad instance 
-- An operator to "lift" an action 
-- from the inner monad to the transformed monad
