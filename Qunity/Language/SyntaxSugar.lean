import Qunity.Language.Syntax
import Qunity.Language.Types
import Qunity.Math.Reals

namespace Qunity

def Bit : DataType := .unit ⊕ .unit

class TensorPower (T : Type) where
  tensorPower : T -> Nat -> T
instance : TensorPower DataType where
  tensorPower := fun T =>
    Nat.rec DataType.unit (fun _ T' => T ⊗ T')
instance : TensorPower Expression where
  tensorPower := fun e =>
    Nat.rec Expression.unit (fun _ e' => Expression.pair e e')

infixr:80 " ^⊗ " => TensorPower.tensorPower

def Expression.apply (e : Expression) (f : Program) : Expression :=
  .application f e
infixl:50 " ▹ " => Expression.apply

def Program.compose (f f' : Program) (T : DataType) (x : String) : Program :=
  .lambda (.var x) T ((.var x ▹ f') ▹ f)

def letIn (e₁ : Expression) (T : DataType) (e₂ e₃ : Expression) :=
  e₂ ▹ .lambda e₁ T e₃

def zero : Expression := .application (.left .unit .unit) .unit

def one : Expression := .application (.right .unit .unit) .unit
def nothing (T : DataType) : Expression := .application (.left .unit T) .unit

def Maybe (T : DataType) : DataType := .unit ⊕ T

def adjoint (f : Program) (T : DataType) (x : String) : Program :=
  .lambda (.application f (.var x)) T (.var x)
def just (T : DataType) : Program := .right .unit T

def gphase (T : DataType) (r : RealConstant) : Program := .rphase T (.var "x") r r

def fst (T₁ T₂ : DataType) (x₀ x₁ : String) : Program :=
  .lambda (#(.var x₀, .var x₁)) (T₁ ⊗ T₂) (.var x₀)
def snd (T₁ T₂ : DataType) (x₀ x₁ : String) : Program :=
  .lambda (#(.var x₀, .var x₁)) (T₁ ⊗ T₂) (.var x₁)

open scoped RealConstant
def had : Program :=
  .u₃ (π / 2) 0 π

def plus : Expression := zero ▹ had
def minus : Expression := one ▹ had

def equals (e : Expression) (T : DataType) : Program :=
  .lambda (.var "x") T (.tryCatch ((.var "x") ▹ .lambda e T one) zero)

def reflect (e : Expression) (T : DataType) : Program :=
  .rphase T e 0 π

end Qunity
