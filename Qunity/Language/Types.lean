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

infixr:60 " ⊕ " => DataType.sum
infixr:80 " ⊗ " => DataType.product

infixr:60 " ⇝ " => ProgramType.coherentMap
infixr:60 " ⇛ " => ProgramType.quantumChannel

end Qunity
