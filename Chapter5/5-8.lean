

-- Exercise # 1

theorem and_com {p q : Prop} : p ∧ q ↔ q ∧ p :=
begin
  apply iff.intro,
  all_goals {intro h, constructor, {exact h.right}, {exact h.left}}
end


section
universe u

variables (α β : Type u)

example (α : Type u) (a b : α) (p : α → Prop) (h1 :a = b) (h2 : p a) : p b :=
  by {rw h1 at h2, assumption}

end

section

variables x y z : ℤ
example (x y z : ℕ) : x * (y + z) = x * y + x * z :=
  by {apply left_distrib}

end

section
variables (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
begin
  cases h with x pqx,
  constructor, rw and_comm, assumption
end


-- Exercise # 2
example (p q r : Prop) (hp : p) :
  (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
  by {split, any_goals {split}, all_goals { {left, assumption} <|> {right, left, assumption} <|> {right, right, assumption}}}

end
