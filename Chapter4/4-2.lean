
universe u

#check @eq.refl.{u}
#check @eq.symm.{u}
#check @eq.trans
-- If '@' is used but no universe is specified it uses a default one it seems

namespace prev
variables (α : Type u) (a b c d : α)
variables (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d := (hab.trans hcb.symm).trans hcd
end prev
