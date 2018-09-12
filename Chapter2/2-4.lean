
constants α β γ : Type
def myfoo : ℕ -> ℕ -> ℕ → ℕ := λ α β γ, α + β + γ
#reduce myfoo
#check myfoo
#print myfoo

def myprod (a : ℕ) (b : ℕ) := a * b
#print myprod
#check myprod
#reduce myprod

-- Testing if lean can do recursion without any extra keywords
def canLeanRecurse (a : ℕ) : ℕ := if a > 5 then 6 else canLeanRecurse (a+1)
-- Answer seems to be no

-- Nice, you can use Haskell/Idris' '$' operator
def doTwice (f : ℕ -> ℕ) (n : ℕ) : ℕ := f $ f n
#print doTwice
#reduce doTwice

def double (n : ℕ) : ℕ := n * 2

-- Exercise # 1
def quadruple (n : ℕ) : ℕ := doTwice double n
def quadprod8 (n : ℕ) : ℕ := nat.mul 8 $ quadruple n
#print quadprod8
#reduce quadprod8
#eval quadruple 3
#eval quadprod8 3

-- Exercise # 1-2
def Do_Twice (f : (ℕ → ℕ) → (ℕ → ℕ)) (g : ℕ → ℕ) : ℕ → ℕ := f $ g
#reduce Do_Twice doTwice double
#eval Do_Twice doTwice double 2
 
-- Exercise # 2
def curry (α β γ : Type) (f : α × β -> γ) : α -> β -> γ 
    := λ α β, f (α, β)
#print curry
def uncurry (α β γ : Type) (f : α -> β -> γ) : α × β -> γ 
    := λ (p : (α × β)), f p.1 p.2
#print uncurry