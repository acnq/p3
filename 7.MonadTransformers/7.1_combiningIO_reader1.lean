-- Combining IO and Reader 

-- Implementation
structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""

def usage : String := 
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

def configFromArgs: List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _ => none 



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

def showFileName (cfg : Config) (file : String) : IO Unit := do
  IO.println (cfg.fileName file)
def showDirName (cfg : Config) (dir : String) :IO Unit := do
  IO.println (cfg.dirName dir)
def doList [Applicative f] : List α → (α → f Unit) → f Unit 
  | [], _ => pure ()
  | x :: xs , action => 
    action x *>
    doList xs action

partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
  match ← toEntry path with 
  | none => pure ()
  | some (.file name) => showFileName cfg name 
  | some (.dir name) => 
    showDirName cfg name 
    let contents ← path.readDir
    let newConfig := cfg.inDirectory
    doList contents.toList fun d=>
      dirTree newConfig d.path 
open String
def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    dirTree config (← IO.currentDir)
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {args}\n" -- the original code {" ".separate args}\n" seems problematic
    IO.eprintln usage
    pure 1

-- lean --run 7.1_combiningIO_reader1.lean
