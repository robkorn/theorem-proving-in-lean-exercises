
#check let y:= 20 in y * y

def e (a : ℕ) : ℕ :=
    let y := a + a in y * y

#reduce e 2


def foo := let a := nat in λ x : a, x + 2
#print foo
-- def bar := (λ a, λ x : a, x + 2) nat