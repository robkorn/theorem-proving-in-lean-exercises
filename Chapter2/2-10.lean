

-- Exercise # 1
def double (x : nat) := x * 2

def doTwice (f : ℕ -> ℕ) (n : ℕ) : ℕ := f $ f n
#print doTwice
#reduce doTwice

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

-- Exericse # 3
universe u
constant vec : Type u → ℕ → Type u
constant myVec : vec nat 2

constant vecAdd : Π {a : Type u} {n : nat} {m : nat}, vec a n -> vec a m -> vec a (n+m)
#check vecAdd
#check vecAdd myVec myVec
constant vecReverse : Π {a : Type u} {n : nat}, vec a n -> vec a n
#check vecReverse
#check vecReverse myVec

-- Exercise # 4
namespace Matrices
    constant matrix : Type u -> ℕ -> ℕ -> Type u
    variables {m n p : ℕ}

    constant matAdd : Π {a : Type}, matrix a m n -> matrix a m n -> matrix a m n
    constant matMult : Π {a : Type}, matrix a m n -> matrix a n p -> matrix a m p
    constant matMultVec : Π {a : Type}, matrix a m n -> vec a m -> vec a n 

    constant foo : matrix nat 4 2
    constant bar : matrix nat 2 3
    #check matAdd foo foo
    #check matMult foo bar
    #check matMultVec bar myVec
end Matrices