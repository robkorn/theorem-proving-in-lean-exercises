#check nat -- Type
#check bool -- Type
#check nat -> bool -- Type
#check nat × bool -- Type
#check nat -> nat -- ...
#check nat × nat -> nat
#check nat -> nat -> nat
#check nat -> (nat -> nat)
#check nat -> nat -> bool
#check (nat -> nat) -> nat

constants α β : Type
constant F : Type -> Type
constant G : Type -> Type -> Type
#check α -- Type
#check F α -- Type
#check F nat -- Type
#check G α -- Type -> Type
#check G α β -- Type
#check G α nat -- Type

#check prod α β -- Type
#check prod nat nat -- Type

#check list α -- Type
#check list nat -- Type

#check Type
#check Type 0
#check Type 1

#check Prop
#check list
#check prod

universe u
constant ab : Type u
#check ab