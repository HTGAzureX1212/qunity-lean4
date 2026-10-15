import Qunity.Language.Types
import Qunity.Typing.Rules

namespace Qunity

open Context

theorem HasPureType.unit_inverse (h : HasPureType Γ Δ e T) :
    e = .unit → T = .unit ∧ Δ = [] ∧ WellFormed Γ :=
  match h with
  | .hasTypeUnit hΓ => by
      intro
      exact ⟨rfl, rfl, hΓ⟩
  | .hasTypeCVar _ | .hasTypeQVar .. | .hasTypePurePair ..
  | .hasTypeCtrl .. | .hasTypePureApp .. => by
      intro he
      nomatch he
  | .hasTypePurePerm hΓ' _ h _ hΔperm => by
      intro he
      have ⟨rfl, hΔeq, _⟩ := unit_inverse h he
      exact ⟨rfl, nil_permutation.mp (hΔeq ▸ hΔperm), hΓ'⟩

theorem HasPureType.var_inverse (h : HasPureType Γ Δ e T) :
    e = .var x → (Δ = [] ∧ (x, T) ∈ Γ) ∨ (Δ = [(x, T)] ∧ x ∉ Γ.dom) :=
  match h with
  | .hasTypeCVar _ => by
      intro he
      cases he
      exact .inl ⟨rfl, by simp⟩
  | .hasTypeQVar _ hx => by
      intro he
      cases he
      exact .inr ⟨rfl, hx⟩
  | .hasTypeUnit _ | .hasTypePurePair .. | .hasTypeCtrl ..
  | .hasTypePureApp .. => by
      intro he
      nomatch he
  | .hasTypePurePerm _ _ h hΓperm hΔperm => by
      intro he
      cases var_inverse h he with
      | inl h' =>
          rcases h' with ⟨hΔ, hmem⟩
          exact .inl ⟨nil_permutation.mp (hΔ ▸ hΔperm), hΓperm.mem_iff.mp hmem⟩
      | inr h' =>
          rcases h' with ⟨hΔ, hnotin⟩
          exact .inr ⟨permutation_singleton.mp (hΔ ▸ hΔperm.symm),
            mt (permutation_preserves_dom_membership hΓperm).mpr hnotin⟩

theorem HasPureType.pair_inverse (h : HasPureType Γ Δ e T) :
    e = .pair e₀ e₁ →
      ∃ T₀ T₁ Δs Δ₀ Δ₁,
        T = T₀ ⊗ T₁ ∧
        Δ.Perm (Δs ++ Δ₀ ++ Δ₁) ∧
        HasPureType Γ (Δs ++ Δ₀) e₀ T₀ ∧
        HasPureType Γ (Δs ++ Δ₁) e₁ T₁ :=
  match h with
  | .hasTypePurePair _ _ h₀ h₁ => by
      intro he
      cases he
      exact ⟨_, _, _, _, _, rfl, .refl _, h₀, h₁⟩
  | .hasTypeUnit _ | .hasTypeCVar _ | .hasTypeQVar ..
  | .hasTypeCtrl .. | .hasTypePureApp .. => by
      intro he
      nomatch he
  | .hasTypePurePerm _ _ h hΓperm hΔperm => by
      intro he
      obtain ⟨T₀, T₁, Δs, Δ₀, Δ₁, rfl, hsplit, h₀, h₁⟩ :=
        pair_inverse h he
      exact ⟨T₀, T₁, Δs, Δ₀, Δ₁, rfl, hΔperm.symm.trans hsplit,
        (context_permutation_invariant hΓperm (.refl (Δs ++ Δ₀))).mp h₀,
        (context_permutation_invariant hΓperm (.refl (Δs ++ Δ₁))).mp h₁⟩

theorem HasPureType.ctrl_inverse (h : HasPureType Γ Δ e T) :
    e = .coherentControl e_c Tctrl branches Tret →
      T = Tret ∧
      ∃ (Γ₀ Γ' Δ₀ Δ' : Context) (l : List ((Expression × Expression) × Context)),
        Γ.Perm (Γ₀ ++ Γ') ∧
        Δ.Perm (Δ₀ ++ Δ') ∧
        branches = l.map Prod.fst ∧
        WellFormed (Γ₀ ++ Γ' ++ Δ₀ ++ Δ') ∧
        HasMixedType (Γ₀ ++ Δ₀) e_c Tctrl ∧
        Ortho Tctrl (l.map (Prod.fst ∘ Prod.fst)) ∧
        (∀ Γⱼ eⱼ eⱼ', ((eⱼ, eⱼ'), Γⱼ) ∈ l → HasPureType [] Γⱼ eⱼ Tctrl) ∧
        (∀ Γⱼ eⱼ eⱼ', ((eⱼ, eⱼ'), Γⱼ) ∈ l →
          HasPureType (Γ₀ ++ Γ' ++ Γⱼ) (Δ₀ ++ Δ') eⱼ' Tret) ∧
        (∀ x, x ∈ Context.dom Δ₀ →
          Erases x Tret (l.map (Prod.snd ∘ Prod.fst))) :=
  match h with
  | .hasTypeCtrl Γ₀ Γ₁ Δ₀ Δ₁ l _ _ _ hWF hMix hOrtho hPat hBod hErase => by
    intro he
    cases he
    exact ⟨rfl, Γ₀, Γ₁, Δ₀, Δ₁, l, .refl _, .refl _, rfl, hWF, hMix, hOrtho, hPat, hBod, hErase⟩
  | .hasTypeUnit _ | .hasTypeCVar _ | .hasTypeQVar ..
  | .hasTypePurePair .. | .hasTypePureApp .. => by
    intro he
    nomatch he
  | .hasTypePurePerm _ _ h hΓperm hΔperm => by
    intro he
    obtain ⟨rfl, Γ₀, Γ₁, Δ₀, Δ₁, l, hΓsplit, hΔsplit, rfl, hWF, hMix, hOrtho,
        hPat, hBod, hErase⟩ := ctrl_inverse h he
    exact ⟨rfl, Γ₀, Γ₁, Δ₀, Δ₁, l, hΓperm.symm.trans hΓsplit, hΔperm.symm.trans hΔsplit, rfl,
        hWF, hMix, hOrtho, hPat, hBod, hErase⟩

theorem HasPureType.application_inverse (h : HasPureType Γ Δ e T') :
    e = .application f arg →
      ∃ T, HasProgramType f (T ⇝ T') ∧ HasPureType Γ Δ arg T :=
  match h with
  | .hasTypePureApp hf he' => by
    intro he
    cases he
    exact ⟨_, hf, he'⟩
  | .hasTypeUnit _ | .hasTypeCVar _ | .hasTypeQVar ..
  | .hasTypePurePair .. | .hasTypeCtrl .. => by
    intro he
    nomatch he
  | .hasTypePurePerm _ _ h hΓperm hΔperm => by
    intro he
    obtain ⟨T , hf, he'⟩ := application_inverse h he
    exact ⟨T, hf, (context_permutation_invariant hΓperm hΔperm).mp he'⟩

theorem HasPureType.no_try_catch (h : HasPureType Γ Δ e T) :
    e = .tryCatch e₀ e₁ → False :=
  match h with
  | .hasTypeUnit _ | .hasTypeCVar _ | .hasTypeQVar ..
  | .hasTypePurePair .. | .hasTypeCtrl .. | .hasTypePureApp .. => by
    intro he
    nomatch he
  | .hasTypePurePerm _ _ h _ _ => by
    intro he
    exact no_try_catch h he

theorem HasMixedType.unit_inverse (h : HasMixedType Δ e T) :
    e = .unit → T = .unit ∧ Δ = [] :=
  match h with
  | .hasTypeMix _ hp => by
    intro he
    have ⟨rfl, rfl, _⟩ := HasPureType.unit_inverse hp he
    exact ⟨rfl, rfl⟩
  | .hasMixedTypeApp .. | .hasMixedTypePair .. | .hasTypeTry .. => by
    intro he
    nomatch he
  | .hasMixedTypePerm _ h hPerm => by
    intro he
    have ⟨rfl, hΔeq⟩ := unit_inverse h he
    exact ⟨rfl, nil_permutation.mp (hΔeq ▸ hPerm)⟩

theorem HasMixedType.var_inverse (h : HasMixedType Δ e T) :
    e = .var x → Δ = [(x, T)] :=
  match h with
  | .hasTypeMix _ hp => by
    intro he
    cases HasPureType.var_inverse hp he with
    | inl h' =>
      rcases h' with ⟨_, hmem⟩
      simp at hmem
    | inr h' =>
      rcases h' with ⟨hΔ, _⟩
      exact hΔ
  | .hasMixedTypePair .. | .hasTypeTry .. | .hasMixedTypeApp .. => by
      intro he
      nomatch he
  | .hasMixedTypePerm _ h hPerm => by
      intro he
      exact permutation_singleton.mp (var_inverse h he ▸ hPerm.symm)

theorem HasMixedType.pair_inverse (h : HasMixedType Δ e T) :
    e = .pair e₀ e₁ →
      ∃ T₀ T₁ Δs Δ₀ Δ₁,
        T = (T₀ ⊗ T₁) ∧
        Δ.Perm (Δs ++ Δ₀ ++ Δ₁) ∧
        HasMixedType (Δs ++ Δ₀) e₀ T₀ ∧
        HasMixedType (Δs ++ Δ₁) e₁ T₁ :=
  match h with
  | .hasTypeMix _ hp => by
      intro he
      obtain ⟨T₀, T₁, Δs, Δ₀, Δ₁, rfl, hsplit, h₀, h₁⟩ :=
        HasPureType.pair_inverse hp he
      have hWF₀ : WellFormed ([] ++ (Δs ++ Δ₀)) :=
        HasPureType.context_well_formed h₀
      have hWF₁ : WellFormed ([] ++ (Δs ++ Δ₁)) :=
        HasPureType.context_well_formed h₁
      exact ⟨T₀, T₁, Δs, Δ₀, Δ₁, rfl, hsplit,
        .hasTypeMix hWF₀ h₀,
        .hasTypeMix hWF₁ h₁⟩
  | .hasMixedTypePair _ h₀ h₁ => by
      intro he
      cases he
      exact ⟨_, _, _, _, _, rfl, .refl _, h₀, h₁⟩
  | .hasTypeTry .. | .hasMixedTypeApp .. => by
      intro he
      nomatch he
  | .hasMixedTypePerm _ h hperm => by
      intro he
      obtain ⟨T₀, T₁, Δs, Δ₀, Δ₁, rfl, hsplit, h₀, h₁⟩ := pair_inverse h he
      exact ⟨T₀, T₁, Δs, Δ₀, Δ₁, rfl, hperm.symm.trans hsplit, h₀, h₁⟩

theorem HasMixedType.try_catch_inverse (h : HasMixedType Δ e T) :
    e = .tryCatch e₀ e₁ →
      ∃ Δ₀ Δ₁, Δ.Perm (Δ₀ ++ Δ₁) ∧
        HasMixedType Δ₀ e₀ T ∧ HasMixedType Δ₁ e₁ T :=
  match h with
  | .hasTypeMix _ hp => by
      intro he
      exact (HasPureType.no_try_catch hp he).elim
  | .hasTypeTry _ h₀ h₁ => by
      intro he
      cases he
      exact ⟨_, _, .refl _, h₀, h₁⟩
  | .hasMixedTypePair .. | .hasMixedTypeApp .. => by
      intro he
      nomatch he
  | .hasMixedTypePerm _ h hperm => by
      intro he
      obtain ⟨Δ₀, Δ₁, hsplit, h₀, h₁⟩ := try_catch_inverse h he
      exact ⟨Δ₀, Δ₁, hperm.symm.trans hsplit, h₀, h₁⟩

theorem HasMixedType.application_inverse (h : HasMixedType Δ e T') :
    e = .application f arg →
      ∃ T, HasProgramType f (T ⇛ T') ∧ HasMixedType Δ arg T :=
  match h with
  | .hasTypeMix hΔ hp => by
      intro he
      obtain ⟨T, hf, he'⟩ := HasPureType.application_inverse hp he
      exact ⟨T, .hasTypeChannel hf, .hasTypeMix hΔ he'⟩
  | .hasMixedTypeApp hf he' => by
      intro he
      cases he
      exact ⟨_, hf, he'⟩
  | .hasMixedTypePair .. | .hasTypeTry .. => by
      intro he
      nomatch he
  | .hasMixedTypePerm _ h hperm => by
      intro he
      obtain ⟨T, hf, he'⟩ := application_inverse h he
      exact ⟨T, hf, (context_permutation_disjoint hperm).mp he'⟩

theorem HasMixedType.ctrl_inverse (h : HasMixedType Δ e T) :
    e = .coherentControl e_c Tctrl branches Tret →
      T = Tret ∧
      ∃ (Δ₀ Δ₁ : Context) (l : List ((Expression × Expression) × Context)),
        Δ.Perm (Δ₀ ++ Δ₁) ∧
        branches = l.map Prod.fst ∧
        HasMixedType Δ₀ e_c Tctrl ∧
        Ortho Tctrl (l.map (Prod.fst ∘ Prod.fst)) ∧
        (∀ Γⱼ eⱼ eⱼ', ((eⱼ, eⱼ'), Γⱼ) ∈ l → HasPureType [] Γⱼ eⱼ Tctrl) ∧
        (∀ Γⱼ eⱼ eⱼ', ((eⱼ, eⱼ'), Γⱼ) ∈ l →
          HasPureType Γⱼ (Δ₀ ++ Δ₁) eⱼ' Tret) ∧
        (∀ x, x ∈ Context.dom Δ₀ →
          Erases x Tret (l.map (Prod.snd ∘ Prod.fst))) :=
  match h with
  | .hasTypeMix _ hp => by
      intro he
      obtain ⟨rfl, Γ₀, Γ₁, Δ₀, Δ₁, l, hΓsplit, hΔsplit, rfl, _, hMix, hOrtho,
          hPat, hBod, hErase⟩ := HasPureType.ctrl_inverse hp he
      obtain ⟨hΓ₀, hΓ₁⟩ := List.append_eq_nil_iff.mp (nil_permutation.mp hΓsplit)
      subst hΓ₀
      subst hΓ₁
      exact ⟨rfl, Δ₀, Δ₁, l, hΔsplit, rfl, hMix, hOrtho, hPat, hBod, hErase⟩
  | .hasMixedTypePair .. | .hasTypeTry .. | .hasMixedTypeApp .. => by
      intro he
      nomatch he
  | .hasMixedTypePerm _ h hperm => by
      intro he
      obtain ⟨rfl, Δ₀, Δ₁, l, hsplit, rfl, hMix, hOrtho, hPat, hBod, hErase⟩ :=
        ctrl_inverse h he
      exact ⟨rfl, Δ₀, Δ₁, l, hperm.symm.trans hsplit, rfl, hMix, hOrtho, hPat,
        hBod, hErase⟩

theorem HasProgramType.gate_inverse (h : HasProgramType f F) :
    f = .u₃ θ φ ρ → F = (Bit ⇝ Bit) ∨ F = (Bit ⇛ Bit) :=
  match h with
  | .hasTypeGate => by
      intro he
      cases he
      exact .inl rfl
  | .hasTypeChannel h' => by
      intro he
      match h' with
      | .hasTypeGate =>
          cases he
          exact .inr rfl
      | .hasTypeLeft | .hasTypeRight | .hasCoherentTypeAbs .. | .hasTypeRphase .. =>
          nomatch he
  | .hasTypeLeft | .hasTypeRight | .hasCoherentTypeAbs .. | .hasTypeRphase ..
  | .hasChannelTypeAbs .. => by
      intro he
      nomatch he

theorem HasProgramType.left_inverse (h : HasProgramType f F) :
    f = .left T₀ T₁ → F = (T₀ ⇝ T₀ ⊕ T₁) ∨ F = (T₀ ⇛ T₀ ⊕ T₁) :=
  match h with
  | .hasTypeLeft => by
      intro he
      cases he
      exact .inl rfl
  | .hasTypeChannel h' => by
      intro he
      match h' with
      | .hasTypeLeft =>
          cases he
          exact .inr rfl
      | .hasTypeGate | .hasTypeRight | .hasCoherentTypeAbs .. | .hasTypeRphase .. =>
          nomatch he
  | .hasTypeGate | .hasTypeRight | .hasCoherentTypeAbs .. | .hasTypeRphase ..
  | .hasChannelTypeAbs .. => by
      intro he
      nomatch he

theorem HasProgramType.right_inverse (h : HasProgramType f F) :
    f = .right T₀ T₁ → F = (T₁ ⇝ T₀ ⊕ T₁) ∨ F = (T₁ ⇛ T₀ ⊕ T₁) :=
  match h with
  | .hasTypeRight => by
      intro he
      cases he
      exact .inl rfl
  | .hasTypeChannel h' => by
      intro he
      match h' with
      | .hasTypeRight =>
          cases he
          exact .inr rfl
      | .hasTypeGate | .hasTypeLeft | .hasCoherentTypeAbs .. | .hasTypeRphase .. =>
          nomatch he
  | .hasTypeGate | .hasTypeLeft | .hasCoherentTypeAbs .. | .hasTypeRphase ..
  | .hasChannelTypeAbs .. => by
      intro he
      nomatch he

theorem HasProgramType.rphase_inverse (h : HasProgramType f F) :
    f = .rphase T e γ γ' →
      (F = (T ⇝ T) ∨ F = (T ⇛ T)) ∧ ∃ Δ, HasPureType [] Δ e T :=
  match h with
  | .hasTypeRphase hp => by
      intro he
      cases he
      exact ⟨.inl rfl, _, hp⟩
  | .hasTypeChannel h' => by
      intro he
      match h' with
      | .hasTypeRphase hp =>
          cases he
          exact ⟨.inr rfl, _, hp⟩
      | .hasTypeGate | .hasTypeLeft | .hasTypeRight | .hasCoherentTypeAbs .. =>
          nomatch he
  | .hasTypeGate | .hasTypeLeft | .hasTypeRight | .hasCoherentTypeAbs ..
  | .hasChannelTypeAbs .. => by
      intro he
      nomatch he

theorem HasProgramType.lambda_inverse (h : HasProgramType f F) :
    f = .lambda e T e' →
      (∃ T', F = (T ⇝ T') ∧
          ∃ Δ, HasPureType [] Δ e T ∧ HasPureType [] Δ e' T') ∨
      (∃ T', F = (T ⇛ T') ∧
          ((∃ Δ, HasPureType [] Δ e T ∧ HasPureType [] Δ e' T') ∨
            ∃ Δ Δ₀, HasPureType [] (Δ ++ Δ₀) e T ∧ HasMixedType Δ e' T')) :=
  match h with
  | .hasCoherentTypeAbs hp hb => by
      intro he
      cases he
      exact .inl ⟨_, rfl, _, hp, hb⟩
  | .hasChannelTypeAbs hp hb => by
      intro he
      cases he
      exact .inr ⟨_, rfl, .inr ⟨_, _, hp, hb⟩⟩
  | .hasTypeChannel h' => by
      intro he
      match h' with
      | .hasCoherentTypeAbs hp hb =>
          cases he
          exact .inr ⟨_, rfl, .inl ⟨_, hp, hb⟩⟩
      | .hasTypeGate | .hasTypeLeft | .hasTypeRight | .hasTypeRphase .. =>
          nomatch he
  | .hasTypeGate | .hasTypeLeft | .hasTypeRight | .hasTypeRphase .. => by
      intro he
      nomatch he

end Qunity
