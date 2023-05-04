-- 2 combining IO Actions
def main : IO Unit := do 
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout -- action use ← s

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace -- ordinary function use :=

  stdout.putStrLn s!"Hello, {name}!"   