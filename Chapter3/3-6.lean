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

    lemma oal1 {p q r : Prop} : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
    λ h : (p ∨ q) ∨ r,
    h.elim 
        (assume hpq : p ∨ q,
            hpq.elim
                (assume hp : p,
                    show p ∨ q ∨ r, from or.inl hp)
                (assume hq : q,
                    show p ∨ q ∨ r, from or.inr $ or.inl hq))
        (assume hr : r,
            show p ∨ q ∨ r, from or.inr $ or.inr hr)
    lemma oal2 {p q r : Prop} : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
    λ h : p ∨ (q ∨ r),
    h.elim 
        (assume hp : p,
            show (p ∨ q) ∨ r, from or.inl $ or.inl hp)
        (assume hqr : q ∨ r,
            hqr.elim
                (assume hq : q,
                    show (p ∨ q) ∨ r, from or.inl $ or.inr hq)
                (assume hr : r,
                    show (p ∨ q) ∨ r, from or.inr hr))
    theorem or_assoc {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    iff.intro
        oal1
        oal2
end andOrAssoc

namespace andOrDistrib
    lemma aod1 {p q r : Prop} : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    λ h : p ∧ (q ∨ r),
    have hp : p, from h.left,
    have hqr : (q ∨ r), from h.right,
    hqr.elim 
        (assume hq : q,
            show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
        (assume hr : r,
            show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩)


    lemma aod2 {p q r : Prop} : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) :=
    λ h : (p ∧ q) ∨ (p ∧ r),
    h.elim 
        (assume hpq : p ∧ q,
        have hp : p, from hpq.left,
        have hq : q, from hpq.right,
        and.intro
            (show p, from hp)
            (show q ∨ r, from or.inl hq))
        (assume hpr : p ∧ r,
        have hp : p, from hpr.left,
        have hr : r, from hpr.right,
        and.intro
            (show p, from hp)
            (show q ∨ r, from or.inr hr))
    theorem and_or_distrib {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    iff.intro
        aod1
        aod2



lemma oad1 {p q r : Prop} : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
λ h : p ∨ (q ∧ r),
h.elim
    (assume hp : p,
     and.intro
        (show p ∨ q,from or.inl hp)
        (show p ∨ r, from or.inl hp))
    (assume hqr : q ∧ r,
     have hq : q, from hqr.left,
     have hr : r, from hqr.right,
     and.intro
        (show p ∨ q, from or.inr hq)
        (show p ∨ r, from or.inr hr))

lemma oad2 {p q r : Prop} : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) := 
λ h : (p ∨ q) ∧ (p ∨ r),
have hpq : p ∨ q, from h.left,
have hpr : p ∨ r, from h.right,
sorry

theorem or_and_distrib {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro
    (oad1)
    (oad2)

end andOrDistrib