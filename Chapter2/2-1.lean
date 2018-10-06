/- declare some constants -/
constant m : nat -- m is a natural number
constant n : nat
constants b1 b2 : bool -- declare two constants at once
constant t : int

/- check their types -/
#check m -- output: nat
#check n
#check n + 0 -- nat
#check m * (n + 0)-- nat
#check b1 -- bool
#check b1 && b2 -- "&&" is boolean and
#check b1 || b2 -- boolean or
#check tt -- boolean "true"
#check tt || b1 && b2
#check if tt then b1 else b2

constant f : nat → nat -- type the arrow as "\to" or "\r"
constant f' : nat → nat -- alternative ASCII notation
constant f'' : nat → ℕ 
constant p : nat × nat -- type the product as "\times"
constant q : prod nat nat -- alternative notation
constant g : nat -> nat -> nat
constant g' : nat -> (nat -> nat) -- has the same type as g->
constant h : nat × nat -> nat
constant F : (nat -> nat) -> nat -- a "functional"
#check f -- N -> N
#check f n -- N
#check g m n -- N
#check g m -- N -> N
#check (m, n) -- N × N
#check p.1 -- N
#check p.fst -- N
#check p.2 -- N
#check (m, n).1 -- N
#check (p.1, n) -- N × N
#check F f -- N


