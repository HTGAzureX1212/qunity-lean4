import Qunity.Semantics.Denotations
import Qunity.Semantics.Derivations
import Qunity.Semantics.Valuation
import Qunity.Typing.Context

namespace Qunity

structure AmplitudeUniqueUpTo (n : Nat) : Prop where
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

theorem PureDerivation.eq_of_depth_zero
    {Γ Δ e T} (d : PureDerivation Γ Δ e T) (hd : d.depth = 0) :
    (e = .unit ∧ T = .unit ∧ Δ = [] ∧
      ∃ hΓ : Context.WellFormed Γ,
        HEq d (PureDerivation.hasTypeUnit (Γ := Γ) hΓ)) ∨
    (∃ Γ₁ Γ₂ x,
      e = .var x ∧
      Δ = [] ∧
      Γ = Γ₁ ++ [(x, T)] ++ Γ₂ ∧
      ∃ hΓ : Context.WellFormed (Γ₁ ++ [(x, T)] ++ Γ₂),
        HEq d (PureDerivation.hasTypeCVar
          (Γ₁ := Γ₁) (Γ₂ := Γ₂) (x := x) (T := T) hΓ)) ∨
    (∃ x,
      e = .var x ∧
      Δ = [(x, T)] ∧
      ∃ hΓ : Context.WellFormed Γ,
        ∃ hx : x ∉ Context.dom Γ,
          HEq d (PureDerivation.hasTypeQVar
            (Γ := Γ) (x := x) (T := T) hΓ hx)) := by
  cases d with
  | hasTypeUnit hΓ =>
    exact Or.inl ⟨rfl, rfl, rfl, hΓ, HEq.rfl⟩
  | hasTypeCVar hΓ =>
    rename_i Γ₁ Γ₂ x
    exact Or.inr (Or.inl
      ⟨Γ₁, Γ₂, x, rfl, rfl, rfl, hΓ, HEq.rfl⟩)
  | hasTypeQVar hΓ hx =>
    rename_i x
    exact Or.inr (Or.inr
      ⟨x, rfl, rfl, hΓ, hx, HEq.rfl⟩)
  | hasTypePurePair =>
    simp [PureDerivation.depth] at hd
  | hasTypeCtrl =>
    simp [PureDerivation.depth] at hd
  | hasTypePureApp =>
    simp [PureDerivation.depth] at hd
  | hasTypePurePerm =>
    simp [PureDerivation.depth] at hd

private theorem PureDerivation.cvar_amplitude_of_depth_zero
    {Γ Δ : Context} {e : Expression}
    {x : Variable} {T : DataType}
    (d : PureDerivation Γ Δ e T)
    (hd : d.depth = 0)
    (he : e = .var x)
    (hΔ : Δ = [])
    (hx : (x, T) ∈ Γ)
    (σ : Valuation Γ)
    (τ : Valuation Δ)
    (v : Value T) :
    pureAmplitude d σ τ v =
      (if v = (σ.lookup x T).get (by
        apply Valuation.lookup_isSome
        exact hx) then 1 else 0) := by
  revert Δ e
  intro Δ e d hd he hΔ τ
  cases d with
  | hasTypeUnit hΓ =>
      cases he
  | hasTypeCVar hΓ =>
      cases he
      cases hΔ
      cases τ
      simp [pureAmplitude]
  | hasTypeQVar hΓ hx' =>
      cases hΔ
  | hasTypePurePair =>
      cases he
  | hasTypeCtrl =>
      cases he
  | hasTypePureApp =>
      cases he
  | hasTypePurePerm =>
      simp [PureDerivation.depth] at hd

lemma well_typed_well_defined_semantics_base_case : AmplitudeUniqueUpTo 0 where
  pure := by
    intro Γ Δ e T d₁ d₂ hd₁ hd₂ σ τ v
    have h1 := PureDerivation.eq_of_depth_zero d₁ (Nat.eq_zero_of_le_zero hd₁)
    have h2 := PureDerivation.eq_of_depth_zero d₂ (Nat.eq_zero_of_le_zero hd₂)
    rcases h1 with
      ⟨he, hT, hΔ, hΓ, hEq⟩ |
      ⟨Γ₁, Γ₂, x, he, hΔ, hΓeq, hΓ, hEq⟩ |
      ⟨x, he, hΔ, hΓ, hx, hEq⟩
    · -- unit
      rcases h2 with ⟨he', hT', hΔ', hΓ', hEq₂⟩ |
        ⟨_, _, _, he', _, _, _, _⟩ |
        ⟨_, he', _, _, _, _⟩
      · cases he'
        cases hT'
        cases hΔ'
        cases hEq
        cases hEq₂
        simp
      · cases he; cases he'
      · cases he; cases he'
    · -- CVar
      rcases h2 with
        ⟨he', _, _, _, _⟩ |
        ⟨_, _, x', he', _, _, _, _⟩ |
        ⟨_, he', _, _, _, _⟩
      · cases he; cases he'
      · have hxx : x = x' := by
          have h : Expression.var x = Expression.var x' :=
            he.symm.trans he'
          injection h
        subst x'
        subst e
        subst Δ
        cases τ
        have hx : (x, T) ∈ Γ := by
          rw [hΓeq]
          exact List.mem_append_left Γ₂
            (List.mem_append_right Γ₁
              (List.mem_singleton_self (x, T)))
        calc
          pureAmplitude d₁ σ .nil v =
              (if v = (σ.lookup x T).get (by
                apply Valuation.lookup_isSome
                exact hx) then 1 else 0) :=
              d₁.cvar_amplitude_of_depth_zero (Nat.eq_zero_of_le_zero hd₁) rfl rfl hx σ .nil v
          _ = pureAmplitude d₂ σ .nil v :=
            (d₂.cvar_amplitude_of_depth_zero (Nat.eq_zero_of_le_zero hd₂) rfl rfl hx σ .nil v).symm
      · sorry
    · -- qvar
      rcases h2 with ⟨he', _, _, _, _⟩ |
        ⟨_, _, _, he', _, _, _, _⟩ |
        ⟨x', he', hΔ', hΓ', hx', hEq₂⟩
      · cases he; cases he'
      · sorry
      · sorry
  mixed := by sorry
  prog := by sorry
  branch := by sorry

theorem well_typed_well_defined_semantics (n : Nat) : AmplitudeUniqueUpTo n := by
  induction n with
  | zero => exact well_typed_well_defined_semantics_base_case
  | succ n ih => sorry

end Qunity
