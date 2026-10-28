import Qunity.Language.Syntax
import Qunity.Language.SyntaxSugar
import Qunity.Language.Types
import Qunity.Typing.Context
import Qunity.Typing.Rules

namespace Qunity

mutual
  inductive BranchDerivation :
      Context → Context → Context → Context →
      List ((Expression × Expression) × Context) →
      DataType → DataType → Type
  where
    | nil (Γ Γ' Δ Δ' : Context) (T T' : DataType) :
        BranchDerivation Γ Γ' Δ Δ' [] T T'
    | cons {Γ Γ' Δ Δ' Γⱼ eⱼ eⱼ' l T T'} :
        PureDerivation [] Γⱼ eⱼ T →
        PureDerivation (Γ ++ Γ' ++ Γⱼ) (Δ ++ Δ') eⱼ' T' →
        BranchDerivation Γ Γ' Δ Δ' l T T' →
        BranchDerivation Γ Γ' Δ Δ'
          (((eⱼ, eⱼ'), Γⱼ) :: l) T T'

  inductive PureDerivation :
      Context → Context → Expression → DataType → Type
  where
    | hasTypeUnit {Γ : Context} :
        Context.WellFormed Γ →
        PureDerivation Γ [] .unit .unit
    | hasTypeCVar {Γ₁ Γ₂ : Context} {x : Variable}
        {T : DataType} :
        Context.WellFormed (Γ₁ ++ [(x, T)] ++ Γ₂) →
        PureDerivation (Γ₁ ++ [(x, T)] ++ Γ₂) [] (.var x) T
    | hasTypeQVar {Γ : Context} {x : Variable} {T : DataType} :
        Context.WellFormed Γ →
        x ∉ Γ.dom →
        PureDerivation Γ [(x, T)] (.var x) T
    | hasTypePurePair
        {Γ Δ Δ₀ Δ₁ : Context}
        {e₀ e₁ : Expression}
        {T₀ T₁ : DataType} :
        Context.WellFormed Γ →
        Context.WellFormed (Δ ++ Δ₀ ++ Δ₁) →
        PureDerivation Γ (Δ ++ Δ₀) e₀ T₀ →
        PureDerivation Γ (Δ ++ Δ₁) e₁ T₁ →
        PureDerivation Γ (Δ ++ Δ₀ ++ Δ₁)
          (.pair e₀ e₁) (T₀ ⊗ T₁)
    | hasTypeCtrl
        (Γ Γ' Δ Δ' : Context)
        (l : List ((Expression × Expression) × Context))
        (e : Expression) (T T' : DataType) :
        Context.WellFormed (Γ ++ Γ' ++ Δ ++ Δ') →
        MixedDerivation (Γ ++ Δ) e T →
        Ortho T (l.map (Prod.fst ∘ Prod.fst)) →
        BranchDerivation Γ Γ' Δ Δ' l T T' →
        (∀ x, x ∈ Context.dom Δ →
          Erases x T' (l.map (Prod.snd ∘ Prod.fst))) →
        PureDerivation (Γ ++ Γ') (Δ ++ Δ')
          (.coherentControl e T (l.map Prod.fst) T') T'
    | hasTypePureApp
        {Γ Δ : Context} {e : Expression} {f : Program}
        {T T' : DataType} :
        ProgramDerivation f (T ⇝ T') →
        PureDerivation Γ Δ e T →
        PureDerivation Γ Δ (e ▹ f) T'
    | hasTypePurePerm
        {Γ Γ' Δ Δ' : Context}
        {e : Expression} {T : DataType} :
        Context.WellFormed Γ' →
        Context.WellFormed Δ' →
        PureDerivation Γ Δ e T →
        List.Perm Γ Γ' →
        List.Perm Δ Δ' →
        PureDerivation Γ' Δ' e T

  inductive MixedDerivation :
      Context → Expression → DataType → Type
  where
    | hasTypeMix {Δ : Context} {e : Expression} {T : DataType} :
        Context.WellFormed Δ →
        PureDerivation [] Δ e T →
        MixedDerivation Δ e T
    | hasMixedTypePerm
        {Δ Δ' : Context} {e : Expression} {T : DataType} :
        Context.WellFormed Δ' →
        MixedDerivation Δ e T →
        List.Perm Δ Δ' →
        MixedDerivation Δ' e T
    | hasMixedTypePair
        {Δ Δ₀ Δ₁ : Context}
        {e₀ e₁ : Expression}
        {T₀ T₁ : DataType} :
        Context.WellFormed (Δ ++ Δ₀ ++ Δ₁) →
        MixedDerivation (Δ ++ Δ₀) e₀ T₀ →
        MixedDerivation (Δ ++ Δ₁) e₁ T₁ →
        MixedDerivation (Δ ++ Δ₀ ++ Δ₁)
          (.pair e₀ e₁) (T₀ ⊗ T₁)
    | hasTypeTry
        {Δ₀ Δ₁ : Context}
        {e₀ e₁ : Expression} {T : DataType} :
        Context.WellFormed (Δ₀ ++ Δ₁) →
        MixedDerivation Δ₀ e₀ T →
        MixedDerivation Δ₁ e₁ T →
        MixedDerivation (Δ₀ ++ Δ₁) (.tryCatch e₀ e₁) T
    | hasMixedTypeApp
        {Δ : Context} {e : Expression} {f : Program}
        {T T' : DataType} :
        ProgramDerivation f (T ⇛ T') →
        MixedDerivation Δ e T →
        MixedDerivation Δ (e ▹ f) T'

  inductive ProgramDerivation :
      Program → ProgramType → Type
  where
    | hasTypeGate {θ φ ρ : RealConstant} :
        ProgramDerivation (.u₃ θ φ ρ) (Bit ⇝ Bit)
    | hasTypeLeft {T₀ T₁ : DataType} :
        ProgramDerivation (.left T₀ T₁) (T₀ ⇝ T₀ ⊕ T₁)
    | hasTypeRight {T₀ T₁ : DataType} :
        ProgramDerivation (.right T₀ T₁) (T₁ ⇝ T₀ ⊕ T₁)
    | hasCoherentTypeAbs
        {Δ : Context} {e e' : Expression}
        {T T' : DataType} :
        PureDerivation [] Δ e T →
        PureDerivation [] Δ e' T' →
        ProgramDerivation (.lambda e T e') (T ⇝ T')
    | hasTypeRphase
        {Δ : Context} {e : Expression}
        {T : DataType} {γ γ' : RealConstant} :
        PureDerivation [] Δ e T →
        ProgramDerivation (.rphase T e γ γ') (T ⇝ T)
    | hasTypeChannel
        {f : Program} {T T' : DataType} :
        ProgramDerivation f (T ⇝ T') →
        ProgramDerivation f (T ⇛ T')
    | hasChannelTypeAbs
        {Δ Δ₀ : Context}
        {e e' : Expression} {T T' : DataType} :
        PureDerivation [] (Δ ++ Δ₀) e T →
        MixedDerivation Δ e' T' →
        ProgramDerivation (.lambda e T e') (T ⇛ T')
end

mutual
  theorem PureDerivation.toProp
      (d : PureDerivation Γ Δ e T) :
      HasPureType Γ Δ e T :=
    match d with
    | .hasTypeUnit hΓ =>
        HasPureType.hasTypeUnit hΓ
    | .hasTypeCVar hΓ =>
        HasPureType.hasTypeCVar hΓ
    | .hasTypeQVar hΓ hx =>
        HasPureType.hasTypeQVar hΓ hx
    | .hasTypePurePair hΓ hΔ h₀ h₁ =>
        HasPureType.hasTypePurePair
          hΓ hΔ h₀.toProp h₁.toProp
    | .hasTypeCtrl _ _ _ _ _ _ _ _ hWF hMixed hOrtho hBranches hErases =>
        HasPureType.hasTypeCtrl
          _ _ _ _ _ _ _ _
          hWF hMixed.toProp hOrtho hBranches.toProp hErases
    | .hasTypePureApp hf he =>
        HasPureType.hasTypePureApp hf.toProp he.toProp
    | .hasTypePurePerm hΓ hΔ h hPermΓ hPermΔ =>
        HasPureType.hasTypePurePerm
          hΓ hΔ h.toProp hPermΓ hPermΔ
  termination_by structural d

  theorem MixedDerivation.toProp
      (d : MixedDerivation Δ e T) :
      HasMixedType Δ e T :=
    match d with
    | .hasTypeMix hΔ hPure =>
        HasMixedType.hasTypeMix hΔ hPure.toProp
    | .hasMixedTypePerm hΔ' h hPerm =>
        HasMixedType.hasMixedTypePerm hΔ' h.toProp hPerm
    | .hasMixedTypePair hΔ h₀ h₁ =>
        HasMixedType.hasMixedTypePair
          hΔ h₀.toProp h₁.toProp
    | .hasTypeTry hΔ h₀ h₁ =>
        HasMixedType.hasTypeTry
          hΔ h₀.toProp h₁.toProp
    | .hasMixedTypeApp hf he =>
        HasMixedType.hasMixedTypeApp hf.toProp he.toProp
  termination_by structural d

  theorem ProgramDerivation.toProp
      (d : ProgramDerivation f F) :
      HasProgramType f F :=
    match d with
    | .hasTypeGate =>
        HasProgramType.hasTypeGate
    | .hasTypeLeft =>
        HasProgramType.hasTypeLeft
    | .hasTypeRight =>
        HasProgramType.hasTypeRight
    | .hasCoherentTypeAbs h₀ h₁ =>
        HasProgramType.hasCoherentTypeAbs
          h₀.toProp h₁.toProp
    | .hasTypeRphase h =>
        HasProgramType.hasTypeRphase h.toProp
    | .hasTypeChannel h =>
        HasProgramType.hasTypeChannel h.toProp
    | .hasChannelTypeAbs hPure hMixed =>
        HasProgramType.hasChannelTypeAbs
          hPure.toProp hMixed.toProp
  termination_by structural d

  theorem BranchDerivation.toProp
      (d : BranchDerivation Γ Γ' Δ Δ' l T T') :
      Branches Γ Γ' Δ Δ' l T T' :=
    match d with
    | .nil Γ Γ' Δ Δ' T T' =>
        Branches.nil Γ Γ' Δ Δ' T T'
    | .cons hInput hOutput rest =>
        Branches.cons
          hInput.toProp
          hOutput.toProp
          rest.toProp
  termination_by structural d
end

mutual
  theorem HasPureType.exists_derivation
      (h : HasPureType Γ Δ e T) :
      Nonempty (PureDerivation Γ Δ e T) :=
    match h with
    | .hasTypeUnit hΓ =>
        ⟨.hasTypeUnit hΓ⟩
    | .hasTypeCVar hΓ =>
        ⟨.hasTypeCVar hΓ⟩
    | .hasTypeQVar hΓ hx =>
        ⟨.hasTypeQVar hΓ hx⟩
    | .hasTypePurePair hΓ hΔ h₀ h₁ =>
        match h₀.exists_derivation, h₁.exists_derivation with
        | ⟨d₀⟩, ⟨d₁⟩ => ⟨.hasTypePurePair hΓ hΔ d₀ d₁⟩
    | .hasTypeCtrl Γ Γ' Δ Δ' l e T T' hWF hMix hOrtho b hErase =>
        match hMix.exists_derivation,
              b.exists_derivation with
        | ⟨dMix⟩, ⟨dB⟩ =>
            ⟨.hasTypeCtrl Γ Γ' Δ Δ' l e T T' hWF dMix hOrtho dB hErase⟩
    | .hasTypePureApp hf he =>
        match hf.exists_derivation,
              he.exists_derivation with
        | ⟨df⟩, ⟨de⟩ => ⟨.hasTypePureApp df de⟩
    | .hasTypePurePerm hΓ' hΔ' h hΓ hΔ =>
        match h.exists_derivation with
        | ⟨d⟩ => ⟨.hasTypePurePerm hΓ' hΔ' d hΓ hΔ⟩
    termination_by structural h

  theorem HasMixedType.exists_derivation
      (h : HasMixedType Δ e T) :
      Nonempty (MixedDerivation Δ e T) :=
    match h with
    | .hasTypeMix hΔ hp =>
        match HasPureType.exists_derivation hp with
        | ⟨d⟩ => ⟨.hasTypeMix hΔ d⟩
    | .hasMixedTypePerm hΔ' h hperm =>
        match h.exists_derivation with
        | ⟨d⟩ => ⟨.hasMixedTypePerm hΔ' d hperm⟩
    | .hasMixedTypePair hΔ h₀ h₁ =>
        match h₀.exists_derivation, h₁.exists_derivation with
        | ⟨d₀⟩, ⟨d₁⟩ => ⟨.hasMixedTypePair hΔ d₀ d₁⟩
    | .hasTypeTry hΔ h₀ h₁ =>
        match h₀.exists_derivation, h₁.exists_derivation with
        | ⟨d₀⟩, ⟨d₁⟩ => ⟨.hasTypeTry hΔ d₀ d₁⟩
    | .hasMixedTypeApp hf he =>
        match hf.exists_derivation,
              he.exists_derivation with
        | ⟨df⟩, ⟨de⟩ => ⟨.hasMixedTypeApp df de⟩
    termination_by structural h

  theorem HasProgramType.exists_derivation
      (h : HasProgramType f F) :
      Nonempty (ProgramDerivation f F) :=
    match h with
    | .hasTypeGate => ⟨.hasTypeGate⟩
    | .hasTypeLeft => ⟨.hasTypeLeft⟩
    | .hasTypeRight => ⟨.hasTypeRight⟩
    | .hasCoherentTypeAbs hp hq =>
        match HasPureType.exists_derivation hp,
              HasPureType.exists_derivation hq with
        | ⟨dp⟩, ⟨dq⟩ => ⟨.hasCoherentTypeAbs dp dq⟩
    | .hasTypeRphase hp =>
        match HasPureType.exists_derivation hp with
        | ⟨d⟩ => ⟨.hasTypeRphase d⟩
    | .hasTypeChannel hf =>
        match hf.exists_derivation with
        | ⟨d⟩ => ⟨.hasTypeChannel d⟩
    | .hasChannelTypeAbs hp hm =>
        match hp.exists_derivation,
              hm.exists_derivation with
        | ⟨dp⟩, ⟨dm⟩ => ⟨.hasChannelTypeAbs dp dm⟩
    termination_by structural h

  theorem Branches.exists_derivation
      (h : Branches Γ Γ' Δ Δ' l T T') :
      Nonempty (BranchDerivation Γ Γ' Δ Δ' l T T') :=
    match h with
    | .nil Γ Γ' Δ Δ' T T' =>
        ⟨.nil Γ Γ' Δ Δ' T T'⟩
    | .cons hp hq b =>
        match hp.exists_derivation,
              hq.exists_derivation,
              b.exists_derivation with
        | ⟨dp⟩, ⟨dq⟩, ⟨db⟩ => ⟨.cons dp dq db⟩
    termination_by structural h
end

end Qunity
