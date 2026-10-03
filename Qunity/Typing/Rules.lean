import Mathlib.Data.Finset.Basic
import Qunity.Language.Syntax
import Qunity.Language.SyntaxSugar
import Qunity.Language.Types
import Qunity.Typing.Context

namespace Qunity

mutual
  def FreeVariables : Expression -> Finset Variable
    | .unit => ∅
    | .var x => {x}
    | .pair e₁ e₂
    | .tryCatch e₁ e₂ => FreeVariables e₁ ∪ FreeVariables e₂
    | .coherentControl e _ l _ =>
        FreeVariables e ∪ FreeVariablesBranches l
    | .application _ e => FreeVariables e

  def FreeVariablesBranches : List (Expression × Expression) → Finset Variable
    | [] => ∅
    | (e₁, e₂) :: l =>
      FreeVariables e₁ ∪ FreeVariables e₂ ∪ FreeVariablesBranches l
end

inductive Erases (x : String) : DataType -> List Expression -> Prop
where
  | erasesVar (n : Nat) (T : DataType) : Erases x T (.replicate n (.var x))
  | erasesGphase (T : DataType) (l1 : List Expression) (e : Expression) (l2 : List Expression) (γ : RealConstant) :
      Erases x T (l1 ++ e :: l2) →
      Erases x T (l1 ++ (e ▹ gphase T γ) :: l2)
  | erasesCtrl (T T' : DataType) (e : Expression) (l : List (Expression × Expression))  (l1 l2 : List Expression) :
      Erases x T (l1 ++ l.map Prod.snd ++ l2) →
      Erases x T (l1 ++ Expression.coherentControl e T l T' :: l2)
  | erasesPair0 (T₀ T₁ : DataType) (l : List (Expression × Expression)) :
      Erases x T₀ (l.map Prod.fst) →
      Erases x (T₀ ⊗ T₁) (l.map (Function.uncurry Expression.pair))
  | erasesPair1 (T₀ T₁ : DataType) (l : List (Expression × Expression)) :
      Erases x T₁ (l.map Prod.snd) →
      Erases x (T₀ ⊗ T₁) (l.map (Function.uncurry Expression.pair))

inductive Spanning : DataType -> List Expression -> Prop where
  | spanningVoid : Spanning .void []
  | spanningUnit : Spanning .unit [.unit]
  | spanningVar : Spanning T [.var x]
  | spanningSum :
      Spanning T es →
      Spanning T' e's →
      Spanning (T ⊕ T') (es.map (.application (.left T T')) ++ e's.map (.application (.right T T')))
  | spanningPair (l : List (Expression × List Expression)) :
      Spanning T (l.map Prod.fst) →
      (∀ (e l'), (e, l') ∈ l → Spanning T' l') →
      (∀ (e l'), (e, l') ∈ l → Disjoint (FreeVariables e) ((FreeVariables <$> l').foldl (· ∪ ·) ∅)) →
      Spanning (T ⊗ T') (l.flatMap fun (e, l') => l'.map fun e' => #(e, e'))
  | spanningPerm : Spanning T es → List.Perm es e's → Spanning T e's

def Ortho (T : DataType) (l : List Expression) : Prop :=
  ∃ l', List.Sublist l' l ∧ Spanning T l'

mutual
  open Context

  inductive HasPureType : Context -> Context -> Expression -> DataType -> Prop
  where
    | hasTypeUnit : WellFormed Γ → HasPureType Γ [] .unit .unit
    | hasTypeCVar : WellFormed (Γ₁ ++ [(x, T)] ++ Γ₂) →
        HasPureType (Γ₁ ++ [(x, T)] ++ Γ₂) [] (.var x) T
    | hasTypeQVar : WellFormed Γ → x ∉ Γ.dom → HasPureType Γ [(x, T)] (.var x) T
    | hasTypePurePair :
        WellFormed Γ →
        WellFormed (Δ ++ Δ₀ ++ Δ₁) →
        HasPureType Γ (Δ ++ Δ₀) e₀ T₀ →
        HasPureType Γ (Δ ++ Δ₁) e₁ T₁ →
        HasPureType Γ (Δ ++ Δ₀ ++ Δ₁) (.pair e₀ e₁) (T₀ ⊗ T₁)
    | hasTypeCtrl (Γ Γ' Δ Δ' : Context) (l : List ((Expression × Expression) × Context)) (e : Expression) (T T' : DataType) :
        WellFormed (Γ ++ Γ' ++ Δ ++ Δ') →
        HasMixedType (Γ ++ Δ) e T →
        Ortho T (l.map (Prod.fst ∘ Prod.fst)) →
        (∀ (Γⱼ : Context) (eⱼ eⱼ' : Expression), ((eⱼ, eⱼ'), Γⱼ) ∈ l → HasPureType [] Γⱼ eⱼ T) →
        (∀ (Γⱼ : Context) (eⱼ eⱼ' : Expression), ((eⱼ, eⱼ'), Γⱼ) ∈ l → HasPureType (Γ ++ Γ' ++ Γⱼ) (Δ ++ Δ') eⱼ' T') →
        (∀ (x : Variable), x ∈ Context.dom Δ → Erases x T' (l.map (Prod.snd ∘ Prod.fst))) →
        HasPureType (Γ ++ Γ') (Δ ++ Δ') (.coherentControl e T (l.map Prod.fst) T') T'
    | hasTypePureApp :
        HasProgramType f (T ⇝ T') ->
        HasPureType Γ Δ e T ->
        HasPureType Γ Δ (e ▹ f) T'
    | hasTypePurePerm :
        WellFormed Γ' →
        WellFormed Δ' →
        HasPureType Γ Δ e T →
        List.Perm Γ Γ' →
        List.Perm Δ Δ' →
        HasPureType Γ' Δ' e T

  inductive HasMixedType : Context -> Expression -> DataType -> Prop
  where
    | hasTypeMix : WellFormed Δ → HasPureType [] Δ e T -> HasMixedType Δ e T
    | hasMixedTypePerm :
        WellFormed Δ' →
        HasMixedType Δ e T →
        List.Perm Δ Δ' →
        HasMixedType Δ' e T
    | hasMixedTypePair :
        WellFormed (Δ ++ Δ₀ ++ Δ₁) →
        HasMixedType (Δ ++ Δ₀) e₀ T₀ →
        HasMixedType (Δ ++ Δ₁) e₁ T₁ →
        HasMixedType (Δ ++ Δ₀ ++ Δ₁) #(e₀, e₁) (T₀ ⊗ T₁)
    | hasTypeTry :
        WellFormed (Δ₀ ++ Δ₁) →
        HasMixedType Δ₀ e₀ T →
        HasMixedType Δ₁ e₁ T →
        HasMixedType (Δ₀ ++ Δ₁) (try e₀ catch e₁) T
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

open Context

lemma disjoint_of_shared_prefix {Γ A B C : Context}
    (dAB : Disjoint Γ (A ++ B))
    (dAC : Disjoint Γ (A ++ C)) :
    Disjoint Γ (A ++ B ++ C) := by
  simp only [Context.Disjoint] at dAB dAC ⊢
  intro x hx hmem
  rw [List.map_append, List.mem_append] at hmem
  cases hmem with
  | inl hmem => exact dAB hx hmem
  | inr hmem =>
    exact dAC hx (by
      rw [List.map_append, List.mem_append]
      exact Or.inr hmem)

mutual
  theorem HasPureType.context_well_formed (h : HasPureType Γ Δ e T) :
      (Γ ++ Δ).WellFormed :=
    match h with
    | .hasTypeUnit hΓ => by simpa using hΓ
    | .hasTypeCVar hΓ => by simpa using hΓ
    | .hasTypeQVar hΓ hx => by
        rename_i x
        have hw : WellFormed ((x, T) :: Γ) := WellFormed.cons hΓ hx
        have hp : ((x, T) :: Γ).Perm (Γ ++ [(x, T)]) := by
          change ([(x, T)] ++ Γ).Perm (Γ ++ [(x, T)])
          exact List.perm_append_comm
        exact (permutation_preserves_well_formedness hp).mp hw
    | .hasTypePurePair hΓ hΔ h₀ h₁ =>
        concatenation_well_formed_iff_disjoint.mpr ⟨hΓ, hΔ,
          disjoint_of_shared_prefix
            (concatenation_well_formed_iff_disjoint.mp
              (HasPureType.context_well_formed h₀)).2.2
            (concatenation_well_formed_iff_disjoint.mp
              (HasPureType.context_well_formed h₁)).2.2⟩
    | .hasTypeCtrl _ _ _ _ _ _ _ _ hWF _ _ _ _ _ => by
        rw [← List.append_assoc]
        exact hWF
    | .hasTypePureApp _ he =>
        HasPureType.context_well_formed he
    | .hasTypePurePerm _ _ he hpermΓ hpermΔ =>
        (permutation_preserves_well_formedness (hpermΓ.append hpermΔ)).mp
          (HasPureType.context_well_formed he)
    termination_by structural h

  theorem HasMixedType.context_well_formed (h : HasMixedType Δ e T) :
      Δ.WellFormed :=
    match h with
    | .hasTypeMix hΔ _ | .hasMixedTypePerm hΔ _ _
    | .hasMixedTypePair hΔ _ _ | .hasTypeTry hΔ _ _ => hΔ
    | .hasMixedTypeApp _ he => HasMixedType.context_well_formed he
    termination_by structural h
end

end Qunity
