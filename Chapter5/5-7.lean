
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

def f (m n : nat) : nat := m + n + m
example {m n : nat} (h : n = 1) (h' : 0 = m) : (f m n) * m = m :=
by simp [h, h'.symm, f]

end

section

variables (p q r : Prop)
example (hp : p) : p ∧ q ↔ q :=
by simp *
example (hp : p) : p ∨ q :=
by simp *
example (hp : p) (hq : q) : p ∧ (q ∨ r) :=
by simp *

end

namespace test
open list

universe u

variables {α : Type} (x y z : α) (xs ys zs : list α)

def mk_symm (xs : list α) := xs ++ reverse xs

theorem reverse_mk_symm (xs : list α) :
reverse (mk_symm xs) = mk_symm xs :=
by { unfold mk_symm, simp }

example (xs ys : list nat) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp [reverse_mk_symm]

example (xs ys : list nat) (p : list nat → Prop)
(h : p (reverse (xs ++ (mk_symm ys)))) :
  p (mk_symm ys ++ reverse xs) :=
by simp [reverse_mk_symm] at h; assumption

end test

section

open list

variables {α : Type}

def mk_symm (xs : list α) := xs ++ reverse xs

@[simp] theorem reverse_mk_symm (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]

example (xs ys : list nat) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp

example (xs ys : list nat) (p : list nat → Prop)
(h : p (reverse (xs ++ (mk_symm ys)))) :
  p (mk_symm ys ++ reverse xs) :=
by simp at h; assumption


end

