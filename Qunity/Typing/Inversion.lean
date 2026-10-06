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
    e = .unit → T = .unit ∧ Δ = [] := by sorry

end Qunity
