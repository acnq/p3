-- Structures

#check 1.2

#check -454.2123215

#check 0.0

#check 0

#check (0 : Float)

structure Point where 
  x : Float
  y : Float
deriving Repr

def origin : Point := {x := 0.0, y := 0.0}

#eval origin

-- If the deriving Repr line
-- in Point's definition were omitted, 
-- then attempting #eval origin 
-- would yield an error similar to 
-- that which occurs when 
-- omitting a function's argument:

-- expression
--   origin
-- has type
--   Point
-- but instance
--   Lean.MetaEval Point
-- failed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `Lean.MetaEval` class

#eval origin.x

#eval origin.y

def addPoints (p1 : Point) (p2 : Point) : Point := 
  {x := p1.x + p2.x, y := p1.y + p2.y}

#eval addPoints {x := 1.5, y := 32} {x := -8, y := 0.2}

def distance (p1 : Point) (p2 : Point) : Float := 
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance {x := 1.0, y := 2.0} { x := 5.0, y := -1.0}

structure Point3D where 
  x : Float
  y : Float 
  z : Float 
deriving Repr 

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0}

-- must specify structure's type
-- #check {x := 0.0, y := 0.0}
-- invalid {...} notation, expected type is not known

#check ({ x := 0.0, y := 0.0} : Point)

#check { x := 0.0, y := 0.0 : Point}


-- updating structures
def zeroX (p : Point) : Point := 
  {x := 0, y := p.y}

def zeroX' (p : Point) : Point := 
  {p with x := 0}

def fourAndThree : Point := 
  {x := 4.3, y := 3.4}

#eval fourAndThree

#eval zeroX' fourAndThree

#eval fourAndThree

-- Behind the Scenes
-- constructors simply gather the data 
-- to be stored in the newly-allocated data structure. 
-- It is not possible to 
-- provide a custom constructor that pre-processes data or rejects invalid arguments.
#check Point.mk 1.5 2.8

#check (Point.mk)

structure Point' where 
  point :: 
  x : Float
  y : Float
deriving Repr

-- accessor
#check (Point'.x)
#check (Point'.y)

#eval origin.x
#eval Point.x origin

#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point := 
  {x := f p.x, y := f p.y}

#eval fourAndThree.modifyBoth Float.floor

-- Exercise

-- 1.
structure RectangularPrism where 
  height : Float
  width : Float
  depth : Float
deriving Repr

-- 2. 
def volume (p : RectangularPrism) : Float := 
  p.width * p.height * p.depth

#eval volume { width := 1.0, height := 2.0, depth := 3.0 : RectangularPrism}

-- 3.
structure Segment where
  A : Point
  B : Point
deriving Repr

def length (s : Segment) : Float := 
  distance s.A s.B

#eval length {A := {x := 0.0, y := 0.0 : Point}, B := {x := 4.0, y := 3.0 : Point}, : Segment} 


-- 4. 
structure Hamster where
  name : String
  fluffy : Bool
deriving Repr

structure Book where 
  makeBook ::
  title : String 
  author : String
  price : Float
deriving Repr

#check RectangularPrism.mk
#check Hamster.mk
#check Book.makeBook


