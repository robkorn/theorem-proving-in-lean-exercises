
universe u

#check @eq.refl.{u}
#check @eq.symm.{u}
#check @eq.trans
-- If '@' is used but no universe is specified it uses a default one it seems

namespace prev
variables (α : Type u) (a b c d : α)
variables (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d := (hab.trans hcb.symm).trans hcd
end prev

namespace refl
variables (α β : Type u)

example (f : α → β) (a : α) : (λx, f x) a = f a := eq.refl (f a)
example (f : α → β) (a : α) : (λx, f x) a = f a := eq.refl _
example (f : α → β) (a : α) : (λx, f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := eq.refl a
example (a : α) (b : α) : (a, b).1 = a := eq.refl _
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := eq.refl 5
example : 2 + 3 = 5 := eq.refl _
example : 2 + 3 = 5 := rfl
end refl

namespace reflequiv

example (α : Type u) (a b : α) (p : α → Prop) (h1 :a = b) (h2 : p a) : p b :=
eq.subst h1 h2

example (α : Type u) (a b : α) (p : α → Prop)
  (h1 : a = b) (h2 : p a) : p b :=
h1 ▸ h2
end reflequiv

namespace cong

variable α : Type
variables a b : α
variables f g : α → ℕ
variable h₁ : a = b
variable h₂ : f = g
example : f a = f b := congr_arg _ h₁
example : f a = g a := congr_fun h₂ _
example : f a = g b := congr h₂ h₁
end cong

namespace ints

variables x y z : ℤ
example (x y z : ℕ) : x * (y + z) = x * y + x * z := mul_add x y z
example (x y z : ℕ) : (x + y) * z = x * z + y * z := add_mul x y z
example (x y z : ℕ) : x + y + z = x + (y + z) := add_assoc x y z

example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y,
  from left_distrib (x + y) x y,
have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
  from (right_distrib x y y) ▸ (right_distrib x y x) ▸ h1,
(add_assoc (x * x + y * x) (x * y) (y * y)).symm ▸ h2
-- or:
-- h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm

end ints
