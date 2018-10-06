
variables p q : Prop


-- Equivilant
example (h : p ∧ q) : q ∧ p := 
have hp : p, from and.left h,
have hq : q, from and.right h,
show q ∧ p, from ⟨hq, hp⟩

example (h : p ∧ q) : q ∧ p := 
have hp : p, from and.left h,
suffices hq: q, from and.intro hq hp,
show q, from and.right h
-- 