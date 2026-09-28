import Qunity.Language.Syntax
import Qunity.Language.SyntaxSugar
import Qunity.Language.Types
import Qunity.Typing.Context

namespace Qunity

open Context

mutual
  inductive HasPureType : Context -> Context -> Expression -> DataType -> Prop
  where
    | hasTypeUnit : HasPureType Γ [] .unit .unit
    | hasTypeCVar : HasPureType (Γ₁ ++ [(x, T)] ++ Γ₂) [] (.var x) T
    | hasTypeQVar : x ∉ Γ.dom → HasPureType Γ [(x, T)] (.var x) T
    | hasTypePurePair :
        HasPureType Γ (Δ ++ Δ₀) e₀ T₀ →
        HasPureType Γ (Δ ++ Δ₁) e₁ T₁ →
        HasPureType Γ (Δ ++ Δ₀ ++ Δ₁) (.pair e₀ e₁) (T₀ ⊗ T₁)
    -- | hasTypeCtrl
    | hasTypePureApp :
        HasProgramType f (T ⇝ T') ->
        HasPureType Γ Δ e T ->
        HasPureType Γ Δ (e ▹ f) T'
    -- | hasTypePurePerm

  inductive HasMixedType : Context -> Expression -> DataType -> Prop
  where
    | hasTypeMix : HasPureType [] Δ e T -> HasMixedType Δ e T
    -- | hasMixedTypePerm
    | hasMixedTypePair :
        HasMixedType (Δ ++ Δ₀) e₀ T₀ →
        HasMixedType (Δ ++ Δ₁) e₁ T₁ →
        HasMixedType (Δ ++ Δ₁ ++ Δ₂) #(e₁, e₂) (T₀ ⊗ T₁)
    | hasTypeTry :
        HasMixedType Δ₀ e₀ T →
        HasMixedType Δ₁ e₁ T →
        HasMixedType (Δ₀ ++ Δ₁) (try e₁ catch e₂) T
    | hasMixedTypeApp :
        HasProgramType f (T ⇛ T') →
        HasMixedType Δ e T →
        HasMixedType Δ (e ▹ f) T'

  inductive HasProgramType : Program -> ProgramType -> Prop
  where
    | hasTypeGate : HasProgramType (.u₃ θ φ ρ) (Bit ⇝ Bit)
    | hasTypeLeft : HasProgramType (.left T₀ T₁) (T₀ ⇝ T₀ ⊕ T₁)
    | hasTypeRight : HasProgramType (.right T₀ T₁) (T₁ ⇝ T₀ ⊕ T₁)
    | hasCoherentTypeAbs :
        HasPureType [] Δ e T →
        HasPureType [] Δ e' T' →
        HasProgramType (.lambda e T e') (T ⇝ T')
    | hasTypeRphase :
        HasPureType [] Δ e T →
        HasProgramType (.rphase T e γ γ') (T ⇝ T)
    | hasTypeChannel :
        HasProgramType f (T ⇝ T') →
        HasProgramType f (T ⇛ T')
    | hasChannelTypeAbs :
        HasPureType [] (Δ ++ Δ₀) e T →
        HasMixedType Δ e' T' →
        HasProgramType (.lambda e T e') (T ⇛ T')

end

end Qunity
