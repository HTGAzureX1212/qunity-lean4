namespace Qunity

inductive DataType where
  | void
  | unit
  | sum (A B : DataType)
  | product (A B : DataType)
deriving DecidableEq

inductive ProgramType
  | coherentMap (A B : DataType)
  | quantumChannel (A B : DataType)
deriving DecidableEq

infixr:50 " ⊕ " => DataType.sum
infixr:50 " ⊗ " => DataType.product

infixr:50 " ⇝ " => ProgramType.coherentMap
infixr:50 " ⇛ " => ProgramType.quantumChannel

end Qunity
