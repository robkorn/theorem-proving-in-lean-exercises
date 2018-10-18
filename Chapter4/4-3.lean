namespace calcc
variables (a b c d e : ℕ)
variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

theorem T : a = e :=
calc
  a     = b : h1
    ... = c + 1 : h2
    ... = d + 1 : congr_arg _ h3
    ... = 1 + d : add_comm d (1 : ℕ)
    ... = e : h4.symm
end calcc

namespace tactics
variables (a b c d e : ℕ)
variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

include h1 h2 h3 h4
theorem T : a = e :=
calc
  a     = b : by rw h1
    ... = c + 1 : by rw h2
    ... = d + 1 : by rw h3
    ... = 1 + d : by rw add_comm
    ... = e     : by rw h4

theorem T₁ : a = e :=
calc
  a     = d + 1 : by rw [h1, h2, h3]
    ... = 1 + d : by rw add_comm
    ... = e     : by rw h4

theorem T₂ : a = e :=
by rw [h1, h2, h3, add_comm, h4]
#print T₂
#check T₂

theorem T₃ : a = e :=
by simp [h1, h2, h3, h4]

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
calc
  (x + y) * (x + y) = (x + y) * x + (x + y) * y : by rw left_distrib
    ... = x * x + y * x + (x + y) * y           : by rw add_mul
    ... = x * x + y * x + (x * y + y * y)       : by rw add_mul
    ... = x * x + y * x + x * y + y * y         : by rw ← add_assoc

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by rw [mul_add, add_mul, add_mul, ← add_assoc]

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by simp [left_distrib, right_distrib]

end tactics

