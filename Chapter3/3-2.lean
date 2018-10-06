
namespace hidden
    constants p q : Prop

    theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
    #print t1

    theorem tt1 : p -> q -> p :=
    assume hp : p,
    assume hq : q,
    show p, from hp

    lemma ttt1 : p -> q -> q :=
    λ hp : p,
    assume hq : q,
    show q, from hq

    lemma tl (hp : p) (hq : q) : p :=
    show p, from hp
    #check tl

    axiom hp : p
    theorem t2 : q -> p := t1 hp

    theorem t1more (p q : Prop) (hp : p) (hq : q) : p := hp
    #check t1more

    theorem t1m1 : ∀ (p q : Prop), p -> q -> p :=
    assume (p q : Prop),
    λ hp : p,
    λ hq : q,
    show p, from hp
    #check t1m1

    lemma t1m2 : Π (p q : Prop), p -> q -> p :=
    λ (p q : Prop) (hp : p) (hq : q),
    show p, from hp
    #check t1m2

    variables p q : Prop
    theorem t1m3 : p -> q -> p := 
    λ hp : p,
    λ hq : q,
    show p, from hp
    #check t1m3

    variable {hp : p}
    theorem t1m4 : q -> p :=
    λ hq : q,
    hp
end hidden

namespace pairs
    variables p q r s : Prop

    theorem t1 : p -> q -> p :=
    λ hp : p,
    assume hq : q,
    hp

    #check t1 p q
    #check t1 r s
    #check t1 (r → s) (s → r)

    variable h : r → s
    #check t1 (r → s) (s → r) h
end pairs

namespace composition
    variables p q r s : Prop
    theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
    assume h₃ : p,
    show r, from h₁ $ h₂ h₃

    theorem myt2 : (q → r) → (p → q) → (p → r) :=
    λ h₁ : q → r,
    λ h₂ : p → q,
    λ h₃ : p,
    show r, from h₁ $ h₂ h₃
end composition
