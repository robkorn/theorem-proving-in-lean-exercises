
import data.list.basic


section
variables (x y z : nat) (p : nat → Prop)
variable (h : p (x * y))

example : (x + 0) * (0 + y * 1 + z * 0) = x * y :=
by simp

include h

example : p ((x + 0) * (0 + y * 1 + z * 0)) :=
by { simp, assumption }


end

section

universe u
variable {α : Type}
open list
example (xs : list nat) :

reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs :=
by simp

example (xs ys : list α) :
length (reverse (xs ++ ys)) = length xs + length ys :=
by simp

variables (x y z : nat) (p : nat → Prop)

example (h : p ((x + 0) * (0 + y * 1 + z * 0))) :
p (x * y) :=
by { simp at h, assumption }

end

section
variables (w x y z : nat) (p : nat → Prop)

local attribute [simp] mul_comm mul_assoc mul_left_comm

example (h : p (x * y + z * w * x)) :
  p (x * w * z + y * x) :=
by { simp at *, assumption }

example (h1 : p (1 * x + y)) (h2 : p (x * z * 1)) :
  p (y + 0 + x) ∧ p (z * x) :=
by { simp at *, split; assumption }

end
