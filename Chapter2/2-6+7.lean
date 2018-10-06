
def compose (α β γ : Type) (g : β → γ) (f : α → β) (z : α) : γ :=
    g $ f z

section a
    variables (α β γ : Type)

    def doTwice (f : α → α) (x : α) : α :=
        f $ f x
end a

section bar
    variables (α β γ : nat)

end bar

namespace abracadabra
    constant bob : nat
    def bob2 := 2

    def bob2x (x : nat) : nat := bob2 * x

    #reduce bob2x
    #print bob2x
end abracadabra


#reduce abracadabra.bob2x
#print abracadabra.bob2x

open abracadabra
#reduce bob2x
#print bob2x

#check list.nil
open list
#check nil
#check cons
#check append