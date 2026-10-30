import Qunity.Semantics.Denotations
import Qunity.Semantics.Derivations
import Qunity.Semantics.Valuation
import Qunity.Typing.Context

namespace Qunity

structure UniqueUpTo (n : Nat) : Prop where
  pure : ∀ {Γ Δ e T} (d₁ d₂ : PureDerivation Γ Δ e T),
    d₁.depth ≤ n → d₂.depth ≤ n →
    ∀ σ τ v, pureAmplitude d₁ σ τ v = pureAmplitude d₂ σ τ v
  mixed : ∀ {Δ e T} (d₁ d₂ : MixedDerivation Δ e T),
    d₁.depth ≤ n → d₂.depth ≤ n →
    ∀ τ τ' v v', mixedAmplitude d₁ τ τ' v v' =
      mixedAmplitude d₂ τ τ' v v'
  prog : ∀ {f F} (d₁ d₂ : ProgramDerivation f F),
    d₁.depth ≤ n → d₂.depth ≤ n →
    programAmplitude d₁ = programAmplitude d₂
  branch : ∀ {Γ Γ' Δ Δ' l T T'} (b₁ b₂ : BranchDerivation Γ Γ' Δ Δ' l T T'),
    b₁.depth ≤ n → b₂.depth ≤ n →
    ∀ (prob : Value T → ℂ) σ τ v,
      branchAmplitude b₁ prob σ τ v = branchAmplitude b₂ prob σ τ v

@[simp]
theorem pureAmplitude_preserved_perm {Γ Γ' Δ Δ' e T}
    (hΓ' : Context.WellFormed Γ') (hΔ' : Context.WellFormed Δ')
    (d : PureDerivation Γ Δ e T)
    (hΓ : List.Perm Γ Γ') (hΔ : List.Perm Δ Δ')
    (σ : Valuation Γ') (τ : Valuation Δ') (v : Value T) :
    pureAmplitude (.hasTypePurePerm hΓ' hΔ' d hΓ hΔ) σ τ v =
      pureAmplitude d (σ.reorder hΓ) (τ.reorder hΔ) v := by simp [pureAmplitude]

@[simp] theorem mixedAmplitude_preserved_perm
    {Δ Δ' e T}
    (hΔ' : Context.WellFormed Δ')
    (d : MixedDerivation Δ e T)
    (hperm : List.Perm Δ Δ')
    (τ τ' : Valuation Δ') (v v' : Value T) :
    mixedAmplitude (.hasMixedTypePerm hΔ' d hperm) τ τ' v v' =
      mixedAmplitude d (τ.reorder hperm) (τ'.reorder hperm) v v' := by simp [mixedAmplitude]

@[simp]
theorem mixedAmplitude_mix_to_pure
    {Δ e T}
    (hΔ : Context.WellFormed Δ)
    (dp : PureDerivation [] Δ e T)
    (τ τ' : Valuation Δ) (v v' : Value T) :
    mixedAmplitude (.hasTypeMix hΔ dp) τ τ' v v' =
      pureAmplitude dp .nil τ v * star (pureAmplitude dp .nil τ' v') := by simp [mixedAmplitude]

@[simp] theorem programAmplitude_channel
    {f T T'}
    (df : ProgramDerivation f (T ⇝ T')) :
    programAmplitude (.hasTypeChannel df) =
      fun v v' w w' =>
        programAmplitude df v w * star (programAmplitude df v' w') := by
  simp [programAmplitude]
  funext v v' w w'
  rfl

theorem unique_up_to (n : Nat) : UniqueUpTo n := by
  induction n with
  | zero => sorry
  | succ n ih => sorry

end Qunity
