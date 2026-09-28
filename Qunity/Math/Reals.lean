namespace Qunity

inductive RealConstant where
  | pi
  | e
  | nat (n : Nat)
  | neg (r : RealConstant)
  | add (a b : RealConstant)
  | mul (a b : RealConstant)
  | div (a b : RealConstant)
  | sin (a : RealConstant)
  | cos (a : RealConstant)
  | tan (a : RealConstant)
  | arcsin (a : RealConstant)
  | arccos (a : RealConstant)
  | arctan (a : RealConstant)
  | exp (a : RealConstant)
  | ln (a : RealConstant)
  | sqrt (a : RealConstant)
deriving DecidableEq

scoped notation "π" => RealConstant.pi

instance : Add RealConstant where
  add := RealConstant.add
instance : Div RealConstant where
  div := RealConstant.div
instance : Mul RealConstant where
  mul := RealConstant.mul
instance : Neg RealConstant where
  neg := RealConstant.neg

instance (n : Nat) : OfNat RealConstant n where
  ofNat := .nat n

end Qunity
