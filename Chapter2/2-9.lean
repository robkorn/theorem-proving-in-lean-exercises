namespace hidden
    universe u
    namespace list
        constant cons : Π {a : Type u}, a -> list a -> list a
        constant nil : Π {a : Type u}, list a
        constant append : Π {a : Type u}, list a -> list a -> list a
        #print cons
    end list


def ident {a : Type u} (x : a) := x
def identTy {a : Type u} (x : a) := a
#check ident
#check identTy

#check id
#check @id

end hidden
