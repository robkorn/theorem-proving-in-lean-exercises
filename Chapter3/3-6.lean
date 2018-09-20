namespace andOrCom
    theorem and_com {p q : Prop} : p ∧ q ↔ q ∧ p := 
    iff.intro
        (λ h : p ∧ q, and.intro h.right h.left)
        (λ h : q ∧ p, and.intro h.right h.left)
    #check and_com

    lemma or_lem_1 {p q : Prop} : p ∨ q → q ∨ p :=
    λ h : p ∨ q,
    h.elim (λ hp : p, or.inr hp) (λ hq : q, or.inl hq)
    lemma or_lem_2 {p q : Prop} : q ∨ p → p ∨ q :=
    λ h : q ∨ p,
    h.elim (λ hq : q, or.inr hq) (λ hp : p, or.inl hp)
    theorem or_com {p q : Prop} : p ∨ q ↔ q ∨ p :=
    iff.intro
        or_lem_1
        or_lem_2
    #check or_com
end andOrCom

namespace andOrAssoc

    lemma aal1 {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
    λ h : (p ∧ q) ∧ r,
    have hp : p, from (h.left).left,
    have hq : q, from (h.left).right,
    have hr : r, from h.right,
    ⟨hp, hq, hr⟩
    lemma aal2 {p q r : Prop} : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
    λ h : p ∧ (q ∧ r),
    have hp : p, from h.left,
    have hq : q, from (h.right).left,
    have hr : r, from (h.right).right,
    ⟨⟨hp, hq⟩, hr⟩
    theorem and_assoc {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    iff.intro
        aal1
        aal2

end andOrAssoc