import Qunity.Language.Types
import Qunity.Math.Reals

namespace Qunity

mutual
  inductive Expression where
    | unit
    | var (x : String)
    | pair (e₁ e₂ : Expression)
    | coherentControl (e : Expression) (T : DataType) (branches : List (Expression × Expression)) (T' : DataType)
    | tryCatch (e₁ e₂ : Expression)
    | application (f : Program) (e : Expression)

  inductive Program where
    | u₃ (θ φ ρ: RealConstant)
    | left (T₁ T₂ : DataType)
    | right (T₁ T₂ : DataType)
    | lambda (e₁ : Expression) (T : DataType) (e₂ : Expression)
    | rphase (T : DataType) (e : Expression) (γ γ' : RealConstant)
end

scoped notation "#(" e₁ ", " e₂ ")" => Expression.pair e₁ e₂
scoped notation "try " e₁ " catch " e₂ => Expression.tryCatch e₁ e₂

end Qunity
