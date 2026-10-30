import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Qunity.Language.Types
import Qunity.Math.Reals
import Qunity.Semantics.Assignment
import Qunity.Semantics.Derivations
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

noncomputable def gateAmplitude (θ φ ρ : RealConstant) :
    Value Bit → Value Bit → ℂ :=
  fun v w =>
    let θr := θ.eval; let φr := φ.eval; let ρr := ρ.eval
    match v, w with
    | .inl .unit, .inl .unit => (Real.cos (θr / 2) : ℂ)
    | .inl .unit, .inr .unit =>
        Complex.exp (Complex.I * φr) * (Real.sin (θr / 2) : ℂ)
    | .inr .unit, .inl .unit =>
        -Complex.exp (Complex.I * ρr) * (Real.sin (θr / 2) : ℂ)
    | .inr .unit, .inr .unit =>
        Complex.exp (Complex.I * (φr + ρr)) * (Real.cos (θr / 2) : ℂ)
    | _, _ => 0

def leftAmplitude (v : Value T₀) (w : Value (T₀ ⊕ T₁)) : ℂ :=
  match w with
  | .inl v' => if v = v' then 1 else 0
  | .inr _ => 0

def rightAmplitude (v : Value T₁) (w : Value (T₀ ⊕ T₁)) : ℂ :=
  match w with
  | .inr v' => if v = v' then 1 else 0
  | .inl _ => 0

noncomputable section
  mutual
    def branchAmplitude
        (b : BranchDerivation Γ Γ' Δ Δ' l T T')
        (prob : Value T → ℂ)
        (σ : Valuation (Γ ++ Γ'))
        (τ : Valuation (Δ ++ Δ'))
        (v : Value T') : ℂ :=
      match b with
      | .nil .. => 0
      | .cons (Γⱼ := Γⱼ) dPat dBody b' =>
          let thisBranch :=
            ((Value.enum T).map fun u =>
              let matched :=
                ((Valuation.enum Γⱼ).map fun σⱼ =>
                  star (pureAmplitude dPat .nil σⱼ u) *
                    pureAmplitude dBody (σ.append σⱼ) τ v).sum
              prob u * matched).sum
          thisBranch + branchAmplitude b' prob σ τ v
    termination_by b.depth
    decreasing_by
      all_goals
        simp [BranchDerivation.depth]

    def pureAmplitude (d : PureDerivation Γ Δ e T)
        (σ : Valuation Γ) (τ : Valuation Δ) (v: Value T) : ℂ :=
      match d with
      | .hasTypeUnit _ =>
        match τ, v with
        | .nil, .unit => 1
        | _, _ => 0
      | .hasTypeCVar (x := x) (T := T) (Γ₁ := Γ₁) (Γ₂ := Γ₂) _ =>
        let σx := (σ.lookup x T).get (by
        apply Valuation.lookup_isSome
        exact List.mem_append_left Γ₂
          (List.mem_append_right Γ₁
            (List.mem_singleton_self (x, T))))
        if v = σx then 1 else 0
      | .hasTypeQVar (x := x) (T := T) _ _ =>
        let w := τ.singleton
        if v = w then 1 else 0
      | .hasTypePurePair
          (Δ := Δ) (Δ₀ := Δ₀) (Δ₁ := Δ₁) _ _ d₀ d₁ =>
        let (v₀, v₁) := Value.unpair v
        let τ' : Valuation (Δ ++ (Δ₀ ++ Δ₁)) :=
          List.append_assoc Δ Δ₀ Δ₁ ▸ τ
        let p := Valuation.split
          (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ'
        let q := Valuation.split
          (Γ := Δ₀) (Δ := Δ₁) p.2
        pureAmplitude d₀ σ (p.1.append q.1) v₀ *
          pureAmplitude d₁ σ (p.1.append q.2) v₁
      | .hasTypePureApp (T := T) df de =>
        ((Value.enum T).map fun w =>
          programAmplitude df w v * pureAmplitude de σ τ w).sum
      | .hasTypePurePerm _ _ d hΓ hΔ =>
          pureAmplitude d (σ.reorder hΓ) (τ.reorder hΔ) v
      | .hasTypeCtrl Γ₀ Γ₁ Δ₀ Δ₁ l e Tctrl Tret _ dMix _ dB _ =>
          let σΓ := (Valuation.split (Γ := Γ₀) (Δ := Γ₁) σ).1
          let τΔ := (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1
          let τCtrl := σΓ.append τΔ
          let prob := fun u : Value Tctrl =>
            mixedAmplitude dMix τCtrl τCtrl u u
          branchAmplitude dB prob σ τ v
    termination_by d.depth
    decreasing_by
      all_goals
        simp [PureDerivation.depth]

    def mixedAmplitude (d : MixedDerivation Δ e T)
        (τ τ' : Valuation Δ) (v v' : Value T) : ℂ :=
      match d with
      | .hasTypeMix _ dp =>
          pureAmplitude dp .nil τ v * star (pureAmplitude dp .nil τ' v')
      | .hasMixedTypePerm _ d hperm =>
          mixedAmplitude d (τ.reorder hperm) (τ'.reorder hperm) v v'
      | .hasMixedTypePair (Δ := Δ) (Δ₀ := Δ₀) (Δ₁ := Δ₁) _ d₀ d₁ =>
          let (v₀, v₁) := Value.unpair v
          let (v₀', v₁') := Value.unpair v'
          let τr : Valuation (Δ ++ (Δ₀ ++ Δ₁)) :=
            List.append_assoc Δ Δ₀ Δ₁ ▸ τ
          let τr' : Valuation (Δ ++ (Δ₀ ++ Δ₁)) :=
            List.append_assoc Δ Δ₀ Δ₁ ▸ τ'
          let p := Valuation.split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τr
          let q := Valuation.split (Γ := Δ₀) (Δ := Δ₁) p.2
          let p' := Valuation.split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τr'
          let q' := Valuation.split (Γ := Δ₀) (Δ := Δ₁) p'.2
          mixedAmplitude d₀ (p.1.append q.1) (p'.1.append q'.1) v₀ v₀' *
            mixedAmplitude d₁ (p.1.append q.2) (p'.1.append q'.2) v₁ v₁'
      | .hasTypeTry (Δ₀ := Δ₀) (Δ₁ := Δ₁) _ d₀ d₁ =>
          let p := Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ
          let p' := Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ'
          let τ₀ := p.1; let τ₁ := p.2
          let τ₀' := p'.1; let τ₁' := p'.2
          let tr1 : ℂ := if τ₁ = τ₁' then 1 else 0
          let tr0 : ℂ := if τ₀ = τ₀' then 1 else 0
          let trE0 : ℂ :=
            ((Value.enum T).map fun w =>
              mixedAmplitude d₀ τ₀ τ₀' w w).sum
          tr1 * mixedAmplitude d₀ τ₀ τ₀' v v' +
            (tr0 - trE0) * mixedAmplitude d₁ τ₁ τ₁' v v'
      | .hasMixedTypeApp (T := T) df de =>
          ((Value.enum T).map fun w =>
            ((Value.enum T).map fun w' =>
              programAmplitude df w w' v v' *
                mixedAmplitude de τ τ' w w').sum).sum
    termination_by d.depth
    decreasing_by
      all_goals
        simp [MixedDerivation.depth]

    def programAmplitude (d : ProgramDerivation f F) : ProgramDenotation F :=
      match d with
      | .hasTypeGate (θ := θ) (φ := φ) (ρ := ρ) =>
          gateAmplitude θ φ ρ
      | .hasTypeLeft => leftAmplitude
      | .hasTypeRight => rightAmplitude
      | .hasCoherentTypeAbs (Δ := Δ) dp dq =>
          fun v w =>
            ((Valuation.enum Δ).map fun τ =>
              pureAmplitude dq .nil τ w *
                star (pureAmplitude dp .nil τ v)).sum
      | .hasTypeRphase (Δ := Δ) (γ := γ) (γ' := γ') dp =>
          fun v w =>
            let Pvw : ℂ :=
              ((Valuation.enum Δ).map fun τ =>
                pureAmplitude dp .nil τ w *
                  star (pureAmplitude dp .nil τ v)).sum
            let ph (r : RealConstant) : ℂ :=
              Complex.exp (Complex.I * (r.eval : ℝ))
            if v = w then
              ph γ * Pvw + ph γ' * (1 - Pvw)
            else
              ph γ * Pvw + ph γ' * (0 - Pvw)
      | .hasTypeChannel df =>
          fun v v' w w' =>
            programAmplitude df v w * star (programAmplitude df v' w')
      | .hasChannelTypeAbs (Δ := Δ) (Δ₀ := Δ₀) dp dm =>
          fun v v' w w' =>
            ((Valuation.enum Δ).map fun τ =>
              ((Valuation.enum Δ).map fun τ' =>
                let ρττ' : ℂ :=
                  ((Valuation.enum Δ₀).map fun τ₀ =>
                    let τfull  := τ.append τ₀
                    let τfull' := τ'.append τ₀
                    star (pureAmplitude dp .nil τfull v) *
                      pureAmplitude dp .nil τfull' v').sum
                mixedAmplitude dm τ τ' w w' * ρττ').sum).sum
    termination_by d.depth
    decreasing_by
      all_goals
        simp [ProgramDerivation.depth]
  end
end

end Qunity
