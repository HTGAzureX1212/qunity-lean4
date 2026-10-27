import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Qunity.Language.Types
import Qunity.Math.Reals
import Qunity.Semantics.Valuation
import Qunity.Typing.Rules

namespace Qunity

noncomputable def RealConstant.eval : RealConstant → ℝ
  | .pi => Real.pi
  | .e => Real.exp 1
  | .nat n => n
  | .neg r => -(eval r)
  | .add a b => (eval a) + (eval b)
  | .mul a b => (eval a) * (eval b)
  | .div a b => (eval a) / (eval b)
  | .sin a => Real.sin (eval a)
  | .cos a => Real.cos (eval a)
  | .tan a => Real.tan (eval a)
  | .arcsin a => Real.arcsin (eval a)
  | .arccos a => Real.arccos (eval a)
  | .arctan a => Real.arctan (eval a)
  | .exp a => Real.exp (eval a)
  | .ln a => Real.log (eval a)
  | .sqrt a => Real.sqrt (eval a)

def ProgramDenotation : ProgramType -> Type
  | T ⇝ T' => Value T → Value T' → ℂ
  | T ⇛ T' => Value T → Value T → Value T' → Value T' → ℂ

end Qunity
