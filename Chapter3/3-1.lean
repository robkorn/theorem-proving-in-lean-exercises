
namespace hidden
    constant and : Prop -> Prop -> Prop
    constant or : Prop → Prop → Prop
    constant not : Prop → Prop
    constant implies : Prop -> Prop -> Prop

    variables p q r : Prop
    #check and p q

    constant Proof : Prop -> Type
    constant and_comm : Π p q : Prop,
        Proof (implies (and p q) (and q p))
    #check and_comm p q

    constant modus_ponens :
        Π p q : Prop, Proof (implies p q) → Proof p → Proof q
    #check modus_ponens

    constant implies_intro :
        Π p q : Prop, (Proof p -> Proof q) -> Proof (implies p q)
end hidden