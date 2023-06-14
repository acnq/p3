-- Additional Conveniences

-- Pipe Operators
-- The pipeline E1 |> E2 is short for E2 E1
#eval some 5 |> toString 

def times3 (n : Nat) : Nat := n * 3 
#eval 5 |> times3 |> toString |> ("It is " ++ ·)

#eval ("It is " ++ ·) <| toString <| times3 <| 5 
-- ===>
#eval ("It is " ++ ·) (toString (times3 5))

#eval [1, 2, 3] |>.reverse |>.drop 1 |>.reverse

-- Infinite Loops 
def spam : IO Unit := do 
  repeat IO.println "Spam!"

def bufsize : USize := 20 * 1024 -- USize is like size_t, unsigned integer

partial def dump (stream : IO.FS.Stream) : IO Unit := do 
  let buf ← stream.read bufsize 
  if buf.isEmpty then 
    pure ()
  else 
    let stdout ← IO.getStdout
    stdout.write buf 
    dump stream   

-- ===>
def dump2 (stream : IO.FS.Stream) : IO Unit := do 
  let stdout ← IO.getStdout
  repeat do 
    let buf ← stream.read bufsize
    if buf.isEmpty then break 
    stdout.write buf 

-- While Loops 
def dump3 (stream : IO.FS.Stream) : IO Unit := do 
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do 
    stdout.write buf 
    buf ← stream.read bufsize

 
