
variables p q : Prop

#check p → q → p ∧ q
#check ¬p -> p ↔ false
#check p ∨ q → q ∨ p

namespace conjunction

    example (hp : p) (hq : q) : p ∧ q := and.intro hp hq
    #check assume (hp : p) (hq : q), and.intro hp hq

    example (h : p ∧ q) : p := and.elim_left h
    example (h : p ∧ q) : q := and.elim_right h

    -- Equivilant
    example (h : p ∧ q) : q ∧ p := and.intro (and.right h) (and.left h)
    example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

    variables (hp : p) (hq : q)
    #check (⟨hp, hq⟩ : p ∧ q)

end conjunction

namespace disjunction
    example (hp : p) : p ∨ q := or.intro_left q hp
    example (hq : q) : p ∨ q := or.intro_right p hq

    -- Equivilant
    example (h : p ∨ q) : q ∨ p :=
        or.elim h
            (assume hp : p,
                show q ∨ p, from or.intro_right q hp)
            $ assume hq : q,
                 or.intro_left p hq
    example (h : p ∨ q) : q ∨ p :=
        or.elim h (λ hp : p, or.inr hp) (λ hq : q, or.inl hq)
    example (h : p ∨ q) : q ∨ p :=
        h.elim (assume hp : p, or.inr hp) (assume hq : q, or.inl hq)

    namespace neg
        example (hpq : p → q) (hnq : ¬q) : ¬p :=
        λ hp : p,
        show false, from hnq $ hpq hp

        -- Equivilant
        example (hp : p) (hnp : ¬p) : q := false.elim $ hnp hp
        example (hp : p) (hnp : ¬p) : q := absurd hp hnp
    end neg

    theorem and_swap : p ∧ q ↔ q ∧ p :=
    iff.intro 
        (λ h : p ∧ q,
            show q ∧ p, from ⟨h.right, h.left⟩)
        (λ h : q ∧ p,
            show p ∧ q, from ⟨h.right, h.left⟩)
    #check and_swap p q

    variable h : p ∧ q
    variable j : q ∧ p
    example : q ∧ p := iff.mp (and_swap p q) h
    example : p ∧ q := iff.mpr (and_swap p q) j

    theorem short_and_swap : p ∧ q ↔ q ∧ p :=
    ⟨λ h, ⟨h.right, h.left⟩, λ h, ⟨h.right, h.left⟩⟩
    example (h : p ∧ q) : q ∧ p := (short_and_swap p q).mp h
            
end disjunction