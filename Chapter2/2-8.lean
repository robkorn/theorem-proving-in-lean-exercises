
namespace hidden

    universe u
    constant list : Type u -> Type u

    constant cons : Π α : Type u, α → list α → list α
    constant nil : Π α : Type u, list α
    constant head : Π α : Type u, list α -> α
    constant tail : Π α : Type u, list α -> list α
    constant append : Π α : Type u, list α -> list α -> list α


end hidden

open list
#check list -- Type u_1 -> Type u_1
#check @cons -- Π {α : Type u_1}, α -> list α -> list α
#check @nil -- Π {α : Type u_1}, list α
#check @head -- Π {α : Type u_1} [_inst_1 : inhabited α], list α -> α
#check @tail -- Π {α : Type u_1}, list α -> list α
#check @append -- Π {α : Type u_1}, list α -> list α -> list α

variable α  : Type 
variable β : α → Type
variable a : α
variable b : β a

#check sigma.mk α b