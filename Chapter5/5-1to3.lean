theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro hp,
  exact and.intro hq hp
end

theorem test' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
by exact and.intro hp (and.intro hq hp)

#print test


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  intro h,
  apply or.elim (and.right h),
    intro hq,
    apply or.inl,
    apply and.intro,
      exact h.left,
    exact hq,
   intro hr,
   apply or.inr,
   apply and.intro,
     exact h.left,
     exact hr,
   intro h,
   apply or.elim h,
     intro hpq,
     apply and.intro,
     exact hpq.left,
     apply or.inl,
     exact hpq.right,
   intro hpr,
   apply and.intro,
     exact hpr.left,
   apply or.inr,
   exact hpr.right
end


example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros a b c h1 h2,
  exact eq.trans (eq.symm h2) h1,
end

variables x y z w : ℕ
example (h1 : x = y) (h2 : y = z) (h3 : z = w) : x = w :=
begin
  apply eq.trans h1,
  apply eq.trans h2,
  assumption
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity a,
  symmetry,
  repeat { assumption},
end

example : ∃ a : ℕ, 5 = a :=
begin
  apply exists.intro,
  reflexivity,
end

example : ∃ a : ℕ, a = a :=
begin
  fapply exists.intro,
  exact 0,
  reflexivity
end

example (x : ℕ) : x = x :=
begin
  revert x,
  intro y,
  refl,
end

example (p q : Prop) : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with hp hq,
  right, exact hp,
  left, exact hq,
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  constructor, exact hq, exact hp,
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  constructor, left, exact px,
end

universes u v
def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
begin
  intro p,
  cases p with ha hb,
  constructor, exact hb, exact ha
end

def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
begin
  intro p,
  cases p with ha hb,
  right, exact ha,
  left, exact hb
end

open nat
example (P : ℕ → Prop) (h0 : P 0) (h1 : ∀ n, P (succ n)) (m : ℕ) :
  P m :=
begin
  cases m with m', exact h0,
  exact h1 m',
end

example (p q : Prop) : p ∧ ¬ p → q :=
begin
  intro h, cases h, contradiction
end

