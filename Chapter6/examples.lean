variables m n : ℕ
variables i j : ℤ

#check ↑m + i
#check ↑(m + n) + i
#check ↑m + ↑n + i

#check eq
#check @eq
#check eq.symm
#check @eq.symm
#print eq.symm

#check and
#check and.intro
#check @and.intro
-- a user-defined function
def foo {α : Type} (x : α) : α := x
#check foo
#check @foo
#reduce foo
#reduce (foo nat.zero)
#print foo


#print instances ring

#check neg_neg
#check @neg_neg
#check add_group
#check @add_le_add_left

