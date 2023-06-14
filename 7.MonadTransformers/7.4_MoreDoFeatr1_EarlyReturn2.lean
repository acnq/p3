def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if argv != [] then 
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    pure 1 
  else
    stdout.putStrLn "How would you like to be addressed?"
    stdout.flush

    let name := (← stdin.getLine).trim
    if name == "" then 
      stderr.putStrLn s!"No name provided"
      pure 1 
    else 
      stdout.putStrLn s!"Hello, {name}!"
      pure 0 

def greet (name : String) : String := 
  "Hello, " ++ Id.run do return name 

#eval greet "David"

