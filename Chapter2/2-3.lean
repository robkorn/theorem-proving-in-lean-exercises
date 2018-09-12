-- #check fun x : nat, x + 6
-- #check λ x y : nat, x + 7

-- constants α β : Type
-- constants a1 a2 : α
-- constants b1 b2 : β
-- constant f : α -> α
-- constant g : α -> β
-- constant h : α -> β -> α
-- constant p : α -> α -> bool
-- #check fun x : α, f x -- α -> α
-- #check λ x : α, f x -- α -> α
-- #check λ x : α, f (f x) -- α -> α
-- #check λ x : α, h x b1 -- α -> α
-- #check λ y : β, h a1 y -- β -> α
-- #check λ x : α, p (f (f x)) (h (f a1) b2) -- α -> bool
-- #check λ x : α, λ y : β, h (f x) y -- α -> β -> α
-- #check λ (x : α) (y : β), h (f x) y -- α -> β -> α
-- #check λ x y, h (f x) y -- α -> β -> α

-- #check λ (b : nat) (c : int), b

-- constant γ : Type
-- constant mf : α -> β
-- constant mg : β -> γ
-- constant b : β
-- #check λ x : α, x -- α -> α
-- #check λ x : α, b -- α -> β
-- #check λ x : α, mg (mf x) -- α -> γ
-- #check λ x, mg (mf x)

-- #check λ b : β, λ x : α, x -- β -> α -> α
-- #check λ (b : β) (x : α), x -- β -> α -> α
-- #check λ (g : β -> γ) (f : α -> β) (x : α), g (f x)
-- -- (β -> γ) -> (α -> β) -> α -> γ

-- #check λ (α β : Type) (b : β) (x : α), x
-- #check λ (α β γ : Type) (g : β -> γ) (f : α -> β) (x : α), g (f x)


constants α β γ : Type
constant f : α -> β
constant g : β -> γ
constant h : α -> α
constants (a : α) (b : β)

#check (λ x : α, x) a -- α
#check (λ x : α, b) a -- β
#check (λ x : α, b) (h a) -- β
#check (λ x : α, g (f x)) (h (h a)) -- γ
#check (λ (v : β -> γ) (u : α -> β) x, v (u x)) g f a -- γ
#check (λ (Q R S : Type) (v : R -> S) (u : Q -> R) (x : Q),
v (u x)) α β γ g f a -- γ
#reduce (λ (Q R S : Type) (v : R -> S) (u : Q -> R) (x : Q),
v (u x)) α β γ g f a -- γ


#eval 23523342 * 234234