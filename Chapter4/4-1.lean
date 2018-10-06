
namespace uni
variables (α : Type) (p q : α → Prop)

example : (∀x : α, p x ∧ q x) → ∀ y : α, p y :=
λ h : ∀ x : α, p x ∧ q x,
λ y : α,
show p y, from (h y).left
end uni


namespace trans
variables (α : Type) (r : α → α → Prop)
variables trans_r : ∀ {x y z}, r x y → r y z → r x z

variables a b c : α
variables (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r
#check trans_r hab
#check trans_r hab hbc
end trans

namespace equivalence

variables (α : Type) (r : α → α → Prop)

variable refl_r : ∀ x, r x x
variable symm_r : ∀ {x y}, r x y → r y x
variable trans_r : ∀ {x y z}, r x y → r y z → r x z

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
trans_r (trans_r hab $ symm_r hcb) hcd


end equivalence
