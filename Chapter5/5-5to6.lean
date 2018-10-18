section
  example (p q : Prop) (hp : p) : p ∨ q :=
  begin left, assumption end


  example (p q : Prop) (hqp : q ∨ p) : p ∨ q :=
  begin
    cases hqp with hq hp,
      right, assumption,
      left, assumption,
  end


  example (p q : Prop) (hqp : q ∧ p) : p ∧ q :=
  begin
    cases hqp with hq hp,
    split; assumption,
  end

  example (p q : Prop) (hp : p) : p ∨ q :=
  begin { left, assumption } <|> { right, assumption} end
  example (p q : Prop) (hq : q) : p ∨ q :=
  by { left, assumption } <|> { right, assumption}


  example (p q : Prop) (hqp : q ∨ p) : p ∨ q :=
  begin
    cases hqp with hq hp; {left, assumption} <|> {right, assumption}
  end

  meta def my_tac : tactic unit :=
  `[ repeat { {left, assumption} <|> right <|> assumption } ]
  example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by my_tac
  example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by my_tac
  example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by my_tac

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ q ∧ r :=
  by split; try {split}; assumption

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ q ∧ r :=
  begin
    split,
    all_goals { try {split} },
    any_goals { assumption }
  end

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
  begin
    repeat { any_goals { split }},
    all_goals { assumption }
  end

  example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
  by repeat { any_goals { split <|> assumption} }

  variables (f : ℕ → ℕ) (k : ℕ)

  example (h1 : f 0 = 0) (h2 : k = 0) :
    f k = 0 :=
  begin
      rw h2,
      rw h1
  end

  example (x y : ℕ) (p : ℕ → Prop) (q : Prop) (h : q → x = y)
    (h' : p y) (hq : q) : p x :=
  by { rw (h hq), assumption }

  variables (a b : nat)

  example (h1 : a = b) (h2 : f a = 0) : f b = 0 :=
  begin
    rw [←h1 , h2 ]
  end

  example (a b c : nat) : a + b + c = a + c + b :=
  begin
    rw [add_assoc, add_comm b, ←add_assoc]
  end

  example (a b c : nat) : a + b + c = a + c + b :=
  begin
    rw [add_assoc, add_assoc, add_comm b]
  end

  example (a b c : nat) : a + b + c = a + c + b :=
  begin
    rw [add_assoc, add_assoc, add_comm _ b]
  end

end

section
  variables (f : nat → nat) (a : nat)
  example (h : a + 0 = 0) : f a = f 0 :=
    by { rw add_zero at h, rw h }
end

section

universe u

def tuple (α : Type u) (n : nat) :=
  { l : list α // list.length l = n }

variables {α : Type u} {n : nat}

example (h : n = 0) (t : tuple α n) : tuple α 0 :=
begin
  rw h at t,
  exact t
end

example {α : Type u} [ring α] (a b c : α) :
  a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
begin
  rw [mul_zero, mul_zero, zero_mul, zero_mul],
  repeat { rw add_zero }
end

example {α : Type u} [group α] {a b : α} (h : a * b = 1) :
  a⁻¹ = b :=
by rw [←(mul_one a⁻¹ ), ←h, inv_mul_cancel_left]



end

