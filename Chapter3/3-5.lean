
open classical

variable p : Prop
#check em p

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
    (λ hp: p, hp)
    (λ hnp : ¬p, absurd hnp h)

example (h : ¬¬p) : p :=
by_cases 
    (λ h1 : p, h1)
    (λ h2 : ¬p, absurd h2 h)
