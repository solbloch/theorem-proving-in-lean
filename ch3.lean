-- Chapter 3
namespace hidden
  constant and : Prop → Prop → Prop
  constant or : Prop → Prop → Prop
  constant not : Prop → Prop
  constant implies : Prop → Prop → Prop

  variables p q r : Prop

  #check and p q                      -- Prop
  #check or (and p q) r               -- Prop
  #check implies (and p q) (and q p)  -- Prop
end hidden

variables p q : Prop

#check p → q → p ∧ q
#check ¬p → p ↔ false
#check p ∨ q → q ∧ p
