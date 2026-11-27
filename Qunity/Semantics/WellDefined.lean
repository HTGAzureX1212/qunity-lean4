import Qunity.Semantics.Assignment
import Qunity.Semantics.Denotations
import Qunity.Semantics.Derivations
import Qunity.Typing.Context

namespace Qunity

/-! ## Agreement of valuations on their common domain -/

/-- Two valuations agree when they assign the same value to every `(x, S)`
present in both of their contexts. -/
def Valuation.Agreed {Γ₁ Γ₂ : Context}
    (σ₁ : Valuation Γ₁) (σ₂ : Valuation Γ₂) : Prop :=
  ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γ₁ → (x, S) ∈ Γ₂ →
    lookup σ₁ x S = lookup σ₂ x S

theorem Valuation.Agreed.refl {Γ : Context} (σ : Valuation Γ) : σ.Agreed σ :=
  fun _ _ _ _ => rfl

/-! ## Groundwork lemmas about `lookup`, `split`, `append`, `reorder`

These are the elementary facts that make the agreement hypotheses of the
successor step provable.  Each is an induction over the valuation (and, for
`reorder`, via the `Assignment` round-trip in `Qunity.Semantics.Assignment`).
-/

/-- Looking up in an appended valuation, left part. -/
theorem Valuation.lookup_append_left {Γ Δ : Context}
    (σ : Valuation Γ) (τ : Valuation Δ) :
    ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γ →
      lookup (σ.append τ) x S = lookup σ x S := by
  induction σ with
  | nil => intro x S h; cases h
  | cons v σ ih =>
      intro x S h
      simp only [append, Valuation.lookup]
      split_ifs with hc
      · rfl
      · rcases List.mem_cons.mp h with hEq | hm'
        · injection hEq with h₁ h₂
          exact absurd ⟨h₁.symm, h₂.symm⟩ hc
        · exact ih hm'

/-- Looking up in an appended valuation, right part.  The side condition is
needed because `lookup` scans left to right, so an entry in `Γ` would win. -/
theorem Valuation.lookup_append_right {Γ Δ : Context}
    (σ : Valuation Γ) (τ : Valuation Δ) :
    ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ → (x, S) ∉ Γ →
      lookup (σ.append τ) x S = lookup τ x S := by
  induction σ with
  | nil => intro x S _ _; rfl
  | cons v σ ih =>
      intro x S h hΓ
      simp only [append, Valuation.lookup]
      split_ifs with hc
      · exfalso
        obtain ⟨rfl, rfl⟩ := hc
        exact hΓ (by simp)
      · exact ih h (fun hm => hΓ (List.mem_cons_of_mem _ hm))

/-- The left component of a split answers lookups like the whole valuation. -/
theorem Valuation.lookup_split_left {Γ Δ : Context} :
    ∀ (τ : Valuation (Γ ++ Δ)) ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γ →
      lookup (split (Γ := Γ) (Δ := Δ) τ).1 x S = lookup τ x S := by
  induction Γ with
  | nil => intro τ x S h; cases h
  | cons p Γ' ih =>
      obtain ⟨y, T₀⟩ := p
      intro τ x S h
      cases τ with
      | cons v τ' =>
        simp only [split, Valuation.lookup]
        simp only [List.mem_cons] at h
        split_ifs with hc
        · rfl
        · rcases h with hEq | hm'
          · injection hEq with h₁ h₂
            exact absurd ⟨h₁.symm, h₂.symm⟩ hc
          · exact ih τ' hm'

/-- The right component of a split answers lookups like the whole valuation.
The side condition is needed because `lookup` scans left to right: if `(x, S)`
also occurs in `Γ`, the left component would win. -/
theorem Valuation.lookup_split_right {Γ Δ : Context} :
    ∀ (τ : Valuation (Γ ++ Δ)) ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ → (x, S) ∉ Γ →
      lookup (split (Γ := Γ) (Δ := Δ) τ).2 x S = lookup τ x S := by
  induction Γ with
  | nil => intro τ x S _ _; rfl
  | cons p Γ' ih =>
      obtain ⟨y, T₀⟩ := p
      intro τ x S h hΓ
      cases τ with
      | cons v τ' =>
        simp only [split, Valuation.lookup]
        simp only [List.mem_cons] at hΓ
        split_ifs with hc
        · exfalso
          obtain ⟨hyx, hST⟩ := hc
          subst hyx
          subst hST
          exact hΓ (by simp)
        · exact ih τ' h (fun hm => hΓ (Or.inr hm))

/-- Bridge between valuations and assignments: `toValuation` answers lookups
with the assignment's function. -/
theorem Assignment.lookup_toValuation {Γ : Context} :
    ∀ (a : Assignment Γ) ⦃x : Variable⦄ ⦃S : DataType⦄ (h : (x, S) ∈ Γ),
      Valuation.lookup a.toValuation x S = some (a.val x S h) := by
  induction Γ with
  | nil => intro a x S h; cases h
  | cons p Γ' ih =>
      obtain ⟨y, T₀⟩ := p
      intro a x S h
      simp only [toValuation, Valuation.lookup]
      simp only [List.mem_cons] at h
      split_ifs with hc
      · obtain ⟨hyx, hST⟩ := hc
        subst hyx
        subst hST
        rfl
      · rcases h with hEq | hm'
        · injection hEq with h₁ h₂
          exact absurd ⟨h₁.symm, h₂.symm⟩ hc
        · rw [ih ⟨fun z S' hm => a.val z S' (List.mem_cons_of_mem (y, T₀) hm)⟩ hm']

/-- An option that is known to be `some` is recovered by `Option.get`. -/
theorem option_some_get_eq {α : Type} (o : Option α) (p : o.isSome = true) :
    some (o.get p) = o := by
  cases o with
  | none => simp [Option.isSome] at p
  | some a => rfl

/-- Reordering a valuation along a permutation preserves all lookups. -/
theorem Valuation.lookup_reorder {Γ Γ' : Context} :
    ∀ (h : List.Perm Γ Γ') (σ : Valuation Γ')
      ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γ → (x, S) ∈ Γ' →
      lookup (σ.reorder h) x S = lookup σ x S := by
  intro h σ x S h₁ h₂
  show Valuation.lookup
    (Assignment.toValuation (Assignment.ofPerm h.symm σ.toAssignment)) x S
    = Valuation.lookup σ x S
  rw [Assignment.lookup_toValuation (a := Assignment.ofPerm h.symm σ.toAssignment) h₁]
  show some ((Valuation.lookup σ x S).get
      (Valuation.lookup_isSome σ (h.symm.mem_iff.mpr h₁)))
    = Valuation.lookup σ x S
  rw [option_some_get_eq (Valuation.lookup σ x S)
    (Valuation.lookup_isSome σ (h.symm.mem_iff.mpr h₁))]

/-- A singleton valuation is the lookup of its only variable. -/
theorem Valuation.singleton_eq_lookup {x : Variable} {T : DataType}
    (τ : Valuation [(x, T)]) :
    some τ.singleton = lookup τ x T := by
  cases τ with
  | cons v τ' =>
      cases τ'
      simp [singleton, Valuation.lookup]

/-- Looking up is invariant under transporting the context along an equality
of contexts. -/
theorem Valuation.lookup_typeCast {Γ Γ' : Context}
    (τ : Valuation Γ) (h : Γ = Γ') (x : Variable) (S : DataType) :
    Valuation.lookup (h ▸ τ) x S = Valuation.lookup τ x S := by
  cases h
  rfl

/-- Looking up in a valuation whose context was re-associated with
`List.append_assoc`. -/
theorem Valuation.lookup_append_assoc {Δ Δ₀ Δ₁ : Context}
    (τ : Valuation ((Δ ++ Δ₀) ++ Δ₁)) (x : Variable) (S : DataType) :
    Valuation.lookup (List.append_assoc Δ Δ₀ Δ₁ ▸ τ) x S
      = Valuation.lookup τ x S :=
  Valuation.lookup_typeCast τ (List.append_assoc Δ Δ₀ Δ₁) x S

/- **Not needed (and false in general).**  The identity
`(σ.append τ).reorder h = (σ.reorder h₁).append (τ.reorder h₂)` fails when `Γ`
and `Δ` share a variable: `reorder` maps *every* occurrence of a binding to the
value of its *first* occurrence in the source, so with `Γ = Δ = [(x, A)]`,
`σ = cons s nil`, `τ = cons t nil` the two sides are `cons s (cons t nil)` and
`cons s (cons s nil)`.  The v2 strategy never needs this identity anyway:
agreement is tested on lookups, and `lookup_reorder` together with
`lookup_append_left/right` computes the lookup of any reordered/appended
valuation directly. -/

/-- Agreement is inherited by left-appending a common valuation. -/
theorem Valuation.Agreed.append_left {Γ Δ₁ Δ₂ : Context}
    (σ : Valuation Γ) (τ₁ : Valuation Δ₁) (τ₂ : Valuation Δ₂)
    (h : τ₁.Agreed τ₂) :
    (σ.append τ₁).Agreed (σ.append τ₂) := by
  intro x S h₁ h₂
  by_cases hm : (x, S) ∈ Γ
  · rw [lookup_append_left σ τ₁ hm, lookup_append_left σ τ₂ hm]
  · have h₁' : (x, S) ∈ Δ₁ := by
      rcases List.mem_append.mp h₁ with h | h
      · exact absurd h hm
      · exact h
    have h₂' : (x, S) ∈ Δ₂ := by
      rcases List.mem_append.mp h₂ with h | h
      · exact absurd h hm
      · exact h
    rw [lookup_append_right σ τ₁ h₁' hm, lookup_append_right σ τ₂ h₂' hm]
    exact h h₁' h₂'

/-- Agreement survives reordering one side along a permutation: if the
valuations at the permuted contexts agree, so do the valuations transported
back along the permutation.  This is what makes the perm-stripping step of
the successor induction work. -/
theorem Valuation.Agreed.congr_reorder
    {Γ Γ' Δ Δ' Γ₂ Δ₂ : Context}
    (hΓ : List.Perm Γ Γ') (hΔ : List.Perm Δ Δ')
    (σ₁ : Valuation Γ') (τ₁ : Valuation Δ')
    (σ₂ : Valuation Γ₂) (τ₂ : Valuation Δ₂)
    (h : (σ₁.append τ₁).Agreed (σ₂.append τ₂)) :
    ((σ₁.reorder hΓ).append (τ₁.reorder hΔ)).Agreed (σ₂.append τ₂) := by
  intro x S hm₁ hm₂
  by_cases hx : (x, S) ∈ Γ
  · have hx' : (x, S) ∈ Γ' := hΓ.mem_iff.mp hx
    rw [lookup_append_left (σ₁.reorder hΓ) (τ₁.reorder hΔ) hx,
      lookup_reorder hΓ σ₁ hx hx']
    have hAg := h (List.mem_append_left Δ' hx') hm₂
    rw [lookup_append_left σ₁ τ₁ hx'] at hAg
    exact hAg
  · have hd : (x, S) ∈ Δ := by
      rcases List.mem_append.mp hm₁ with hm | hm
      · exact absurd hm hx
      · exact hm
    have hd' : (x, S) ∈ Δ' := hΔ.mem_iff.mp hd
    have hxn' : (x, S) ∉ Γ' := fun hm' => hx (hΓ.mem_iff.mpr hm')
    rw [lookup_append_right (σ₁.reorder hΓ) (τ₁.reorder hΔ) hd hx,
      lookup_reorder hΔ τ₁ hd hd']
    have hAg := h (List.mem_append_right Γ' hd') hm₂
    rw [lookup_append_right σ₁ τ₁ hd' hxn'] at hAg
    exact hAg

/-- Agreement survives reordering one side along a permutation, for single
(not appended) valuations. -/
theorem Valuation.Agreed.congr_reorder_single {Γ Γ'' Γ' : Context}
    (h : List.Perm Γ'' Γ) {τ : Valuation Γ} {τ' : Valuation Γ'}
    (hAg : τ.Agreed τ') : (τ.reorder h).Agreed τ' := by
  intro x S hm₁ hm₂
  rw [lookup_reorder h τ hm₁ (h.mem_iff.mp hm₁)]
  exact hAg (h.mem_iff.mp hm₁) hm₂

/-- The pair recombination, left factor: splitting a valuation over
`Δ ++ (Δ₀ ++ Δ₁)` and re-joining the left component with the left component
of the split of the remainder answers lookups like the original valuation,
on the domain `Δ ++ Δ₀`. -/
theorem Valuation.lookup_recombine_left {Δ Δ₀ Δ₁ : Context} :
    ∀ (τ : Valuation (Δ ++ (Δ₀ ++ Δ₁))) ⦃x : Variable⦄ ⦃S : DataType⦄,
      (x, S) ∈ Δ ++ Δ₀ →
      lookup ((split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).1.append
          (split (Γ := Δ₀) (Δ := Δ₁)
            (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).2).1) x S
        = lookup τ x S := by
  intro τ x S hm
  by_cases hx : (x, S) ∈ Δ
  · rw [lookup_append_left (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).1
        (split (Γ := Δ₀) (Δ := Δ₁)
          (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).2).1 hx,
      lookup_split_left τ hx]
  · have hm0 : (x, S) ∈ Δ₀ := by
      rcases List.mem_append.mp hm with h | h
      · exact absurd h hx
      · exact h
    rw [lookup_append_right (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).1
        (split (Γ := Δ₀) (Δ := Δ₁)
          (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).2).1 hm0 hx,
      lookup_split_left (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).2 hm0,
      lookup_split_right τ (List.mem_append_left Δ₁ hm0) hx]

/-- The pair recombination, right factor: same statement for the *right*
component of the split of the remainder, on the domain `Δ ++ Δ₁`.  The
hypothesis `(x, S) ∉ Δ₀` rules out a duplicated binding, which is available
because the typing rule requires `Δ ++ Δ₀ ++ Δ₁` well-formed. -/
theorem Valuation.lookup_recombine_right {Δ Δ₀ Δ₁ : Context} :
    ∀ (τ : Valuation (Δ ++ (Δ₀ ++ Δ₁))) ⦃x : Variable⦄ ⦃S : DataType⦄,
      (x, S) ∈ Δ ++ Δ₁ → (x, S) ∉ Δ₀ →
      lookup ((split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).1.append
          (split (Γ := Δ₀) (Δ := Δ₁)
            (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).2).2) x S
        = lookup τ x S := by
  intro τ x S hm hnd
  by_cases hx : (x, S) ∈ Δ
  · rw [lookup_append_left (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).1
        (split (Γ := Δ₀) (Δ := Δ₁)
          (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).2).2 hx,
      lookup_split_left τ hx]
  · have hm1 : (x, S) ∈ Δ₁ := by
      rcases List.mem_append.mp hm with h | h
      · exact absurd h hx
      · exact h
    rw [lookup_append_right (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).1
        (split (Γ := Δ₀) (Δ := Δ₁)
          (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).2).2 hm1 hx,
      lookup_split_right (split (Γ := Δ) (Δ := Δ₀ ++ Δ₁) τ).2 hm1 hnd,
      lookup_split_right τ (List.mem_append_right Δ₀ hm1) hx]

/-- Agreement is preserved when the right part of each merged valuation is
*replaced* by another valuation, provided the replacements answer lookups
like the originals on their whole domains and the domains only grow.  This
is the workhorse for the pair/try/app cases of the successor step. -/
theorem Valuation.Agreed.congr_replace
    {Γ₁ Γ₂ Δ₁ Δ₁' Δ₂ Δ₂' : Context}
    (σ₁ : Valuation Γ₁) (σ₂ : Valuation Γ₂)
    (τ₁ : Valuation Δ₁) (ρ₁ : Valuation Δ₁')
    (τ₂ : Valuation Δ₂) (ρ₂ : Valuation Δ₂')
    (h : (σ₁.append τ₁).Agreed (σ₂.append τ₂))
    (hL : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ₁' → lookup ρ₁ x S = lookup τ₁ x S)
    (hR : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ₂' → lookup ρ₂ x S = lookup τ₂ x S)
    (hsub₁ : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γ₁ ++ Δ₁' → (x, S) ∈ Γ₁ ++ Δ₁)
    (hsub₂ : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γ₂ ++ Δ₂' → (x, S) ∈ Γ₂ ++ Δ₂) :
    (σ₁.append ρ₁).Agreed (σ₂.append ρ₂) := by
  intro x S hm₁ hm₂
  by_cases hx₁ : (x, S) ∈ Γ₁
  · rw [lookup_append_left σ₁ ρ₁ hx₁]
    by_cases hx₂ : (x, S) ∈ Γ₂
    · rw [lookup_append_left σ₂ ρ₂ hx₂]
      have hAg := h (List.mem_append_left Δ₁ hx₁) (List.mem_append_left Δ₂ hx₂)
      rw [lookup_append_left σ₁ τ₁ hx₁, lookup_append_left σ₂ τ₂ hx₂] at hAg
      exact hAg
    · have d₂' : (x, S) ∈ Δ₂' := by
        rcases List.mem_append.mp hm₂ with h_ | h_
        · exact absurd h_ hx₂
        · exact h_
      have d₂ : (x, S) ∈ Δ₂ := by
        rcases List.mem_append.mp (hsub₂ hm₂) with h_ | h_
        · exact absurd h_ hx₂
        · exact h_
      rw [lookup_append_right σ₂ ρ₂ d₂' hx₂]
      have hAg := h (List.mem_append_left Δ₁ hx₁) (hsub₂ hm₂)
      rw [lookup_append_left σ₁ τ₁ hx₁, lookup_append_right σ₂ τ₂ d₂ hx₂] at hAg
      rw [hR d₂']
      exact hAg
  · have d₁ : (x, S) ∈ Δ₁' := by
      rcases List.mem_append.mp hm₁ with h_ | h_
      · exact absurd h_ hx₁
      · exact h_
    have d₁old : (x, S) ∈ Δ₁ := by
      rcases List.mem_append.mp (hsub₁ hm₁) with h_ | h_
      · exact absurd h_ hx₁
      · exact h_
    rw [lookup_append_right σ₁ ρ₁ d₁ hx₁]
    by_cases hx₂ : (x, S) ∈ Γ₂
    · rw [lookup_append_left σ₂ ρ₂ hx₂]
      have hAg := h (hsub₁ hm₁) (List.mem_append_left Δ₂ hx₂)
      rw [lookup_append_right σ₁ τ₁ d₁old hx₁, lookup_append_left σ₂ τ₂ hx₂] at hAg
      rw [hL d₁]
      exact hAg
    · have d₂' : (x, S) ∈ Δ₂' := by
        rcases List.mem_append.mp hm₂ with h_ | h_
        · exact absurd h_ hx₂
        · exact h_
      have d₂ : (x, S) ∈ Δ₂ := by
        rcases List.mem_append.mp (hsub₂ hm₂) with h_ | h_
        · exact absurd h_ hx₂
        · exact h_
      rw [lookup_append_right σ₂ ρ₂ d₂' hx₂]
      have hAg := h (hsub₁ hm₁) (hsub₂ hm₂)
      rw [lookup_append_right σ₁ τ₁ d₁old hx₁,
        lookup_append_right σ₂ τ₂ d₂ hx₂] at hAg
      rw [hL d₁, hR d₂']
      exact hAg

/-- Agreement is symmetric. -/
theorem Valuation.Agreed.symm {Γ₁ Γ₂ : Context}
    {σ₁ : Valuation Γ₁} {σ₂ : Valuation Γ₂} (h : σ₁.Agreed σ₂) :
    σ₂.Agreed σ₁ := fun _ _ hm₁ hm₂ => (h hm₂ hm₁).symm

/-- Agreement survives reordering *both* sides along permutations.  This is
what the perm-vs-perm case of the successor step needs. -/
theorem Valuation.Agreed.congr_reorder_both
    {Γ₁ Δ₁ Γ₁' Δ₁' Γ₂ Δ₂ Γ₂' Δ₂' : Context}
    (h₁ : List.Perm Γ₁ Γ₁') (h₁' : List.Perm Δ₁ Δ₁')
    (h₂ : List.Perm Γ₂ Γ₂') (h₂' : List.Perm Δ₂ Δ₂')
    (σ₁ : Valuation Γ₁') (τ₁ : Valuation Δ₁')
    (σ₂ : Valuation Γ₂') (τ₂ : Valuation Δ₂')
    (hAg : (σ₁.append τ₁).Agreed (σ₂.append τ₂)) :
    ((σ₁.reorder h₁).append (τ₁.reorder h₁')).Agreed
      ((σ₂.reorder h₂).append (τ₂.reorder h₂')) := by
  intro x S hm₁ hm₂
  by_cases hx₁ : (x, S) ∈ Γ₁
  · have hx₁' : (x, S) ∈ Γ₁' := h₁.mem_iff.mp hx₁
    rw [lookup_append_left (σ₁.reorder h₁) (τ₁.reorder h₁') hx₁,
      lookup_reorder h₁ σ₁ hx₁ hx₁']
    by_cases hx₂ : (x, S) ∈ Γ₂
    · have hx₂' : (x, S) ∈ Γ₂' := h₂.mem_iff.mp hx₂
      rw [lookup_append_left (σ₂.reorder h₂) (τ₂.reorder h₂') hx₂,
        lookup_reorder h₂ σ₂ hx₂ hx₂']
      have hAg' := hAg (List.mem_append_left Δ₁' hx₁')
        (List.mem_append_left Δ₂' hx₂')
      rw [lookup_append_left σ₁ τ₁ hx₁', lookup_append_left σ₂ τ₂ hx₂'] at hAg'
      exact hAg'
    · have hd₂ : (x, S) ∈ Δ₂ := by
        rcases List.mem_append.mp hm₂ with hm | hm
        · exact absurd hm hx₂
        · exact hm
      have hd₂' : (x, S) ∈ Δ₂' := h₂'.mem_iff.mp hd₂
      rw [lookup_append_right (σ₂.reorder h₂) (τ₂.reorder h₂') hd₂ hx₂,
        lookup_reorder h₂' τ₂ hd₂ hd₂']
      have hAg' := hAg (List.mem_append_left Δ₁' hx₁')
        (List.mem_append_right Γ₂' hd₂')
      rw [lookup_append_left σ₁ τ₁ hx₁', lookup_append_right σ₂ τ₂ hd₂'
        (fun hm => hx₂ (h₂.mem_iff.mpr hm))] at hAg'
      exact hAg'
  · have hd₁ : (x, S) ∈ Δ₁ := by
      rcases List.mem_append.mp hm₁ with hm | hm
      · exact absurd hm hx₁
      · exact hm
    have hd₁' : (x, S) ∈ Δ₁' := h₁'.mem_iff.mp hd₁
    rw [lookup_append_right (σ₁.reorder h₁) (τ₁.reorder h₁') hd₁ hx₁,
      lookup_reorder h₁' τ₁ hd₁ hd₁']
    by_cases hx₂ : (x, S) ∈ Γ₂
    · have hx₂' : (x, S) ∈ Γ₂' := h₂.mem_iff.mp hx₂
      rw [lookup_append_left (σ₂.reorder h₂) (τ₂.reorder h₂') hx₂,
        lookup_reorder h₂ σ₂ hx₂ hx₂']
      have hAg' := hAg (List.mem_append_right Γ₁' hd₁')
        (List.mem_append_left Δ₂' hx₂')
      rw [lookup_append_right σ₁ τ₁ hd₁'
        (fun hm => hx₁ (h₁.mem_iff.mpr hm)), lookup_append_left σ₂ τ₂ hx₂'] at hAg'
      exact hAg'
    · have hd₂ : (x, S) ∈ Δ₂ := by
        rcases List.mem_append.mp hm₂ with hm | hm
        · exact absurd hm hx₂
        · exact hm
      have hd₂' : (x, S) ∈ Δ₂' := h₂'.mem_iff.mp hd₂
      rw [lookup_append_right (σ₂.reorder h₂) (τ₂.reorder h₂') hd₂ hx₂,
        lookup_reorder h₂' τ₂ hd₂ hd₂']
      have hAg' := hAg (List.mem_append_right Γ₁' hd₁')
        (List.mem_append_right Γ₂' hd₂')
      rw [lookup_append_right σ₁ τ₁ hd₁'
        (fun hm => hx₁ (h₁.mem_iff.mpr hm)), lookup_append_right σ₂ τ₂ hd₂'
        (fun hm => hx₂ (h₂.mem_iff.mpr hm))] at hAg'
      exact hAg'

/-- A well-formed three-part context has no variable shared between the
middle part and the rest.  This is the freshness premise needed by
`Valuation.lookup_recombine_right` in the pair case. -/
theorem Context.wf_pair_append_fresh {Δ Δ₀ Δ₁ : Context}
    (h : WellFormed ((Δ ++ Δ₀) ++ Δ₁)) {x : Variable} {S : DataType}
    (h₀ : (x, S) ∈ Δ₀) (hm : (x, S) ∈ Δ ++ Δ₁) : False := by
  rw [well_formed_iff_variables_distinct, List.map_append, List.map_append] at h
  rcases List.nodup_append'.mp h with ⟨_, _, hD1⟩
  rw [List.append_assoc] at h
  rcases List.nodup_append'.mp h with ⟨_, _, hD2⟩
  have hxm : x ∈ List.map Prod.fst Δ ++ List.map Prod.fst Δ₁ := by
    rw [← List.map_append]
    exact List.mem_map_of_mem (f := Prod.fst) hm
  rcases List.mem_append.mp hxm with hm' | hm'
  · exact hD2 hm'
      (List.mem_append_left _ (List.mem_map_of_mem (f := Prod.fst) h₀))
  · exact hD1 (List.mem_append_right _ (List.mem_map_of_mem (f := Prod.fst) h₀))
      hm'

/-- A well-formed two-part context: no binding of the right part occurs in
the left part. -/
theorem Context.wf_append_right_fresh {A B : Context}
    (h : WellFormed (A ++ B)) {x : Variable} {S : DataType}
    (hm : (x, S) ∈ B) : (x, S) ∉ A := by
  rw [well_formed_iff_variables_distinct, List.map_append] at h
  rcases List.nodup_append'.mp h with ⟨_, _, hD⟩
  intro hmem
  exact hD (List.mem_map_of_mem (f := Prod.fst) hmem)
    (List.mem_map_of_mem (f := Prod.fst) hm)

/-- In the ctrl case, the agreement between the merged valuations descends
to the agreement between the *left components* of their splits at the ctrl
sub-contexts.  The freshness side conditions come from the well-formedness
premises of the ctrl rules. -/
theorem Valuation.Agreed.split_ctrl
    {Γa Γa' Δa Δa' Γb Γb' Δb Δb' : Context}
    (σ₁ : Valuation (Γa ++ Γa')) (τ₁ : Valuation (Δa ++ Δa'))
    (σ₂ : Valuation (Γb ++ Γb')) (τ₂ : Valuation (Δb ++ Δb'))
    (hW₁ : Context.WellFormed ((Γa ++ Γa') ++ (Δa ++ Δa')))
    (hW₂ : Context.WellFormed ((Γb ++ Γb') ++ (Δb ++ Δb')))
    (hAg : (σ₁.append τ₁).Agreed (σ₂.append τ₂)) :
    ((split (Γ := Γa) (Δ := Γa') σ₁).1.append
        (split (Γ := Δa) (Δ := Δa') τ₁).1).Agreed
      ((split (Γ := Γb) (Δ := Γb') σ₂).1.append
        (split (Γ := Δb) (Δ := Δb') τ₂).1) := by
  intro x S hm₁ hm₂
  by_cases hx₁ : (x, S) ∈ Γa
  · rw [lookup_append_left (split (Γ := Γa) (Δ := Γa') σ₁).1
        (split (Γ := Δa) (Δ := Δa') τ₁).1 hx₁,
      lookup_split_left σ₁ hx₁]
    rcases List.mem_append.mp hm₂ with hx₂ | hd₂
    · rw [lookup_append_left (split (Γ := Γb) (Δ := Γb') σ₂).1
          (split (Γ := Δb) (Δ := Δb') τ₂).1 hx₂,
        lookup_split_left σ₂ hx₂]
      have hA := hAg (List.mem_append_left (Δa ++ Δa') (List.mem_append_left Γa' hx₁))
        (List.mem_append_left (Δb ++ Δb') (List.mem_append_left Γb' hx₂))
      rw [lookup_append_left σ₁ τ₁ (List.mem_append_left Γa' hx₁), lookup_append_left σ₂ τ₂ (List.mem_append_left Γb' hx₂)] at hA
      exact hA
    · have hF₂ : (x, S) ∉ Γb ++ Γb' :=
        Context.wf_append_right_fresh hW₂ (List.mem_append_left Δb' hd₂)
      rw [lookup_append_right (split (Γ := Γb) (Δ := Γb') σ₂).1
          (split (Γ := Δb) (Δ := Δb') τ₂).1 hd₂
          (fun h => hF₂ (List.mem_append_left _ h)),
        lookup_split_left τ₂ hd₂]
      have hA := hAg (List.mem_append_left (Δa ++ Δa') (List.mem_append_left Γa' hx₁))
        (List.mem_append_right (Γb ++ Γb') (List.mem_append_left Δb' hd₂))
      rw [lookup_append_left σ₁ τ₁ (List.mem_append_left Γa' hx₁),
        lookup_append_right σ₂ τ₂ (List.mem_append_left Δb' hd₂)
          hF₂] at hA
      exact hA
  · have hd₁ : (x, S) ∈ Δa := by
      rcases List.mem_append.mp hm₁ with hm | hm
      · exact absurd hm hx₁
      · exact hm
    have hF₁ : (x, S) ∉ Γa ++ Γa' :=
      Context.wf_append_right_fresh hW₁ (List.mem_append_left Δa' hd₁)
    rw [lookup_append_right (split (Γ := Γa) (Δ := Γa') σ₁).1
        (split (Γ := Δa) (Δ := Δa') τ₁).1 hd₁
        (fun h => hF₁ (List.mem_append_left _ h)),
      lookup_split_left τ₁ hd₁]
    rcases List.mem_append.mp hm₂ with hx₂ | hd₂
    · rw [lookup_append_left (split (Γ := Γb) (Δ := Γb') σ₂).1
          (split (Γ := Δb) (Δ := Δb') τ₂).1 hx₂,
        lookup_split_left σ₂ hx₂]
      have hA := hAg (List.mem_append_right (Γa ++ Γa') (List.mem_append_left Δa' hd₁))
        (List.mem_append_left (Δb ++ Δb') (List.mem_append_left Γb' hx₂))
      rw [lookup_append_right σ₁ τ₁ (List.mem_append_left Δa' hd₁)
          hF₁,
        lookup_append_left σ₂ τ₂ (List.mem_append_left Γb' hx₂)] at hA
      exact hA
    · have hF₂ : (x, S) ∉ Γb ++ Γb' :=
        Context.wf_append_right_fresh hW₂ (List.mem_append_left Δb' hd₂)
      rw [lookup_append_right (split (Γ := Γb) (Δ := Γb') σ₂).1
          (split (Γ := Δb) (Δ := Δb') τ₂).1 hd₂
          (fun h => hF₂ (List.mem_append_left _ h)),
        lookup_split_left τ₂ hd₂]
      have hA := hAg (List.mem_append_right (Γa ++ Γa') (List.mem_append_left Δa' hd₁))
        (List.mem_append_right (Γb ++ Γb') (List.mem_append_left Δb' hd₂))
      rw [lookup_append_right σ₁ τ₁ (List.mem_append_left Δa' hd₁)
          hF₁,
        lookup_append_right σ₂ τ₂ (List.mem_append_left Δb' hd₂)
          hF₂] at hA
      exact hA

/-- The pair-split agreement, left factor: from the agreement between the
merged valuations of two `hasMixedTypePair` decompositions, the agreement
between the `Δ ++ Δ₀`-components of their pair splits.  No freshness needed:
every variable of `Δ ++ Δ₀` is answered by the left component or the left
component of the split of the remainder. -/
theorem Valuation.Agreed.split_pair_left {Δa Δ0a Δ1a Δb Δ0b Δ1b : Context}
    (τ₁ : Valuation ((Δa ++ Δ0a) ++ Δ1a)) (τ₂ : Valuation ((Δb ++ Δ0b) ++ Δ1b))
    (hAg : τ₁.Agreed τ₂) :
    (((Valuation.split (Γ := Δa) (Δ := Δ0a ++ Δ1a)
        (List.append_assoc Δa Δ0a Δ1a ▸ τ₁)).1).append
      ((Valuation.split (Γ := Δ0a) (Δ := Δ1a)
        (Valuation.split (Γ := Δa) (Δ := Δ0a ++ Δ1a)
          (List.append_assoc Δa Δ0a Δ1a ▸ τ₁)).2).1)).Agreed
    (((Valuation.split (Γ := Δb) (Δ := Δ0b ++ Δ1b)
        (List.append_assoc Δb Δ0b Δ1b ▸ τ₂)).1).append
      ((Valuation.split (Γ := Δ0b) (Δ := Δ1b)
        (Valuation.split (Γ := Δb) (Δ := Δ0b ++ Δ1b)
          (List.append_assoc Δb Δ0b Δ1b ▸ τ₂)).2).1)) := by
  intro x S hm₁ hm₂
  rw [Valuation.lookup_recombine_left (Δ := Δa) (Δ₀ := Δ0a) (Δ₁ := Δ1a)
      (List.append_assoc Δa Δ0a Δ1a ▸ τ₁) hm₁,
    Valuation.lookup_append_assoc τ₁ x S,
    Valuation.lookup_recombine_left (Δ := Δb) (Δ₀ := Δ0b) (Δ₁ := Δ1b)
      (List.append_assoc Δb Δ0b Δ1b ▸ τ₂) hm₂,
    Valuation.lookup_append_assoc τ₂ x S]
  exact hAg (List.mem_append_left Δ1a hm₁)
    (List.mem_append_left Δ1b hm₂)

/-- The pair-split agreement, right factor: same statement for the
`Δ ++ Δ₁`-components.  Here the freshness `(x, S) ∉ Δ₀` (available from the
well-formedness of the pair contexts) is needed, because `lookup` scans left
to right. -/
theorem Valuation.Agreed.split_pair_right {Δa Δ0a Δ1a Δb Δ0b Δ1b : Context}
    (τ₁ : Valuation ((Δa ++ Δ0a) ++ Δ1a)) (τ₂ : Valuation ((Δb ++ Δ0b) ++ Δ1b))
    (hW₁ : Context.WellFormed ((Δa ++ Δ0a) ++ Δ1a))
    (hW₂ : Context.WellFormed ((Δb ++ Δ0b) ++ Δ1b))
    (hAg : τ₁.Agreed τ₂) :
    (((Valuation.split (Γ := Δa) (Δ := Δ0a ++ Δ1a)
        (List.append_assoc Δa Δ0a Δ1a ▸ τ₁)).1).append
      ((Valuation.split (Γ := Δ0a) (Δ := Δ1a)
        (Valuation.split (Γ := Δa) (Δ := Δ0a ++ Δ1a)
          (List.append_assoc Δa Δ0a Δ1a ▸ τ₁)).2).2)).Agreed
    (((Valuation.split (Γ := Δb) (Δ := Δ0b ++ Δ1b)
        (List.append_assoc Δb Δ0b Δ1b ▸ τ₂)).1).append
      ((Valuation.split (Γ := Δ0b) (Δ := Δ1b)
        (Valuation.split (Γ := Δb) (Δ := Δ0b ++ Δ1b)
          (List.append_assoc Δb Δ0b Δ1b ▸ τ₂)).2).2)) := by
  intro x S hm₁ hm₂
  have hF0a : (x, S) ∉ Δ0a := by
    have hnd := Context.well_formed_iff_variables_distinct.mp hW₁
    rw [List.map_append, List.map_append] at hnd
    obtain ⟨hnd01, _, hD1⟩ := List.nodup_append'.mp hnd
    obtain ⟨_, _, hD0⟩ := List.nodup_append'.mp hnd01
    intro hmem0
    rcases List.mem_append.mp hm₁ with ha | hz
    · exact hD0 (List.mem_map_of_mem (f := Prod.fst) ha)
        (List.mem_map_of_mem (f := Prod.fst) hmem0)
    · exact hD1 (List.mem_append_right (Δa.map Prod.fst)
        (List.mem_map_of_mem (f := Prod.fst) hmem0))
        (List.mem_map_of_mem (f := Prod.fst) hz)
  have hF0b : (x, S) ∉ Δ0b := by
    have hnd := Context.well_formed_iff_variables_distinct.mp hW₂
    rw [List.map_append, List.map_append] at hnd
    obtain ⟨hnd01, _, hD1⟩ := List.nodup_append'.mp hnd
    obtain ⟨_, _, hD0⟩ := List.nodup_append'.mp hnd01
    intro hmem0
    rcases List.mem_append.mp hm₂ with ha | hz
    · exact hD0 (List.mem_map_of_mem (f := Prod.fst) ha)
        (List.mem_map_of_mem (f := Prod.fst) hmem0)
    · exact hD1 (List.mem_append_right (Δb.map Prod.fst)
        (List.mem_map_of_mem (f := Prod.fst) hmem0))
        (List.mem_map_of_mem (f := Prod.fst) hz)
  rw [Valuation.lookup_recombine_right (Δ := Δa) (Δ₀ := Δ0a) (Δ₁ := Δ1a)
      (List.append_assoc Δa Δ0a Δ1a ▸ τ₁) hm₁ hF0a,
    Valuation.lookup_append_assoc τ₁ x S,
    Valuation.lookup_recombine_right (Δ := Δb) (Δ₀ := Δ0b) (Δ₁ := Δ1b)
      (List.append_assoc Δb Δ0b Δ1b ▸ τ₂) hm₂ hF0b,
    Valuation.lookup_append_assoc τ₂ x S]
  rcases List.mem_append.mp hm₁ with ha | hz
  · rcases List.mem_append.mp hm₂ with ha' | hz'
    · exact hAg (List.mem_append_left Δ1a (List.mem_append_left Δ0a ha))
        (List.mem_append_left Δ1b (List.mem_append_left Δ0b ha'))
    · exact hAg (List.mem_append_left Δ1a (List.mem_append_left Δ0a ha))
        (List.mem_append_right (Δb ++ Δ0b) hz')
  · rcases List.mem_append.mp hm₂ with ha' | hz'
    · exact hAg (List.mem_append_right (Δa ++ Δ0a) hz)
        (List.mem_append_left Δ1b (List.mem_append_left Δ0b ha'))
    · exact hAg (List.mem_append_right (Δa ++ Δ0a) hz)
        (List.mem_append_right (Δb ++ Δ0b) hz')

/-- Agreement between the left components descends from the agreement
between the merged valuations. -/
theorem Valuation.Agreed.left_of_append
    {Γ₁ Δ₁ Γ₂ Δ₂ : Context}
    {σ₁ : Valuation Γ₁} {τ₁ : Valuation Δ₁}
    {σ₂ : Valuation Γ₂} {τ₂ : Valuation Δ₂}
    (hAg : (σ₁.append τ₁).Agreed (σ₂.append τ₂)) :
    σ₁.Agreed σ₂ := by
  intro x S hm₁ hm₂
  rw [← Valuation.lookup_append_left σ₁ τ₁ hm₁, ← Valuation.lookup_append_left σ₂ τ₂ hm₂]
  exact hAg (List.mem_append_left Δ₁ hm₁) (List.mem_append_left Δ₂ hm₂)

/-- Agreement between the right components descends from the agreement
between the merged valuations; the freshness side conditions rule out the
variables of the right part occurring in the left part. -/
theorem Valuation.Agreed.right_of_append
    {Γ₁ Δ₁ Γ₂ Δ₂ : Context}
    {σ₁ : Valuation Γ₁} {τ₁ : Valuation Δ₁}
    {σ₂ : Valuation Γ₂} {τ₂ : Valuation Δ₂}
    (hAg : (σ₁.append τ₁).Agreed (σ₂.append τ₂))
    (hnd₁ : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ₁ → (x, S) ∉ Γ₁)
    (hnd₂ : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ₂ → (x, S) ∉ Γ₂) :
    τ₁.Agreed τ₂ := by
  intro x S hm₁ hm₂
  rw [← Valuation.lookup_append_right σ₁ τ₁ hm₁ (hnd₁ hm₁),
    ← Valuation.lookup_append_right σ₂ τ₂ hm₂ (hnd₂ hm₂)]
  exact hAg (List.mem_append_right Γ₁ hm₁) (List.mem_append_right Γ₂ hm₂)

/-- Agreement of merged valuations survives inserting a branch valuation into
the classical part.  The branch contexts `J₁` and `J₂` need only be
permutation-related, and duplicate-freeness of the two branch composites
rules out the "cross" cases (a binding living in the master classical part on
one side and in the branch part on the other): those would be a repeated
binding, which the well-formedness of the branch bodies excludes. -/
theorem Valuation.Agreed.append_branch {A B J₁ J₂ Q R : Context}
    (hJ : List.Perm J₁ J₂)
    (hnd₁ : ((A ++ J₁) ++ Q).Nodup)
    (hnd₂ : ((B ++ J₂) ++ R).Nodup)
    (σ₁ : Valuation A) (σ₂ : Valuation B)
    (τ₁ : Valuation Q) (τ₂ : Valuation R)
    (σⱼ : Valuation J₂)
    (hAg : (σ₁.append τ₁).Agreed (σ₂.append τ₂)) :
    ((σ₁.append (σⱼ.reorder hJ)).append τ₁).Agreed
      ((σ₂.append σⱼ).append τ₂) := by
  intro x S hmL hmR
  have hndAJ₁ : (A ++ J₁).Nodup := List.Nodup.of_append_left hnd₁
  have hndBJ₂ : (B ++ J₂).Nodup := List.Nodup.of_append_left hnd₂
  have hdisjAJ₁ : List.Disjoint A J₁ := List.disjoint_of_nodup_append hndAJ₁
  have hdisjBJ₂ : List.Disjoint B J₂ := List.disjoint_of_nodup_append hndBJ₂
  have hdisjQ₁ : List.Disjoint (A ++ J₁) Q := List.disjoint_of_nodup_append hnd₁
  have hdisjR₂ : List.Disjoint (B ++ J₂) R := List.disjoint_of_nodup_append hnd₂
  rcases List.mem_append.mp hmL with hmL' | hmQ
  · -- left binding in the master classical part `A ++ J₁`
    rcases List.mem_append.mp hmL' with hmA | hmJ₁
    · -- left binding in `A`
      rcases List.mem_append.mp hmR with hmR' | hmR
      · rcases List.mem_append.mp hmR' with hmB | hmJ₂
        · -- A / B
          have hAB : Valuation.lookup σ₁ x S = Valuation.lookup σ₂ x S := by
            rw [← Valuation.lookup_append_left σ₁ τ₁ hmA,
              ← Valuation.lookup_append_left σ₂ τ₂ hmB]
            exact hAg (List.mem_append_left Q hmA) (List.mem_append_left R hmB)
          rw [Valuation.lookup_append_left (σ₁.append (σⱼ.reorder hJ)) τ₁
                (List.mem_append_left J₁ hmA),
              Valuation.lookup_append_left σ₁ (σⱼ.reorder hJ) hmA,
              Valuation.lookup_append_left (σ₂.append σⱼ) τ₂
                (List.mem_append_left J₂ hmB),
              Valuation.lookup_append_left σ₂ σⱼ hmB]
          exact hAB
        · -- A / J₂ impossible
          exact absurd (hJ.mem_iff.mpr hmJ₂)
            (List.disjoint_left.mp hdisjAJ₁ hmA)
      · -- A / R
        have hnotB : (x, S) ∉ B :=
          fun h => (List.disjoint_right.mp hdisjR₂ hmR) (List.mem_append_left J₂ h)
        have hAR : Valuation.lookup σ₁ x S = Valuation.lookup τ₂ x S := by
          rw [← Valuation.lookup_append_left σ₁ τ₁ hmA,
            ← Valuation.lookup_append_right σ₂ τ₂ hmR hnotB]
          exact hAg (List.mem_append_left Q hmA) (List.mem_append_right B hmR)
        rw [Valuation.lookup_append_left (σ₁.append (σⱼ.reorder hJ)) τ₁
              (List.mem_append_left J₁ hmA),
            Valuation.lookup_append_left σ₁ (σⱼ.reorder hJ) hmA,
            Valuation.lookup_append_right (σ₂.append σⱼ) τ₂ hmR
              (List.disjoint_right.mp hdisjR₂ hmR)]
        exact hAR
    · -- left binding in `J₁`
      rcases List.mem_append.mp hmR with hmR' | hmR
      · rcases List.mem_append.mp hmR' with hmB | hmJ₂
        · -- J₁ / B impossible
          exact absurd hmB (List.disjoint_right.mp hdisjBJ₂ (hJ.mem_iff.mp hmJ₁))
        · -- J₁ / J₂
          have hnotA : (x, S) ∉ A := List.disjoint_right.mp hdisjAJ₁ hmJ₁
          have hnotB : (x, S) ∉ B := List.disjoint_right.mp hdisjBJ₂ hmJ₂
          rw [Valuation.lookup_append_left (σ₁.append (σⱼ.reorder hJ)) τ₁
                (List.mem_append_right A hmJ₁),
              Valuation.lookup_append_right σ₁ (σⱼ.reorder hJ) hmJ₁ hnotA,
              Valuation.lookup_append_left (σ₂.append σⱼ) τ₂
                (List.mem_append_right B hmJ₂),
              Valuation.lookup_append_right σ₂ σⱼ hmJ₂ hnotB]
          exact Valuation.lookup_reorder hJ σⱼ hmJ₁ hmJ₂
      · -- J₁ / R impossible
        exact absurd (List.mem_append_right B (hJ.mem_iff.mp hmJ₁))
          (List.disjoint_right.mp hdisjR₂ hmR)
  · -- left binding in the quantum part `Q`
    rcases List.mem_append.mp hmR with hmR' | hmR
    · rcases List.mem_append.mp hmR' with hmB | hmJ₂
      · -- Q / B
        have hnotA : (x, S) ∉ A :=
          fun h => (List.disjoint_right.mp hdisjQ₁ hmQ) (List.mem_append_left J₁ h)
        have hQB : Valuation.lookup τ₁ x S = Valuation.lookup σ₂ x S := by
          rw [← Valuation.lookup_append_right σ₁ τ₁ hmQ hnotA,
            ← Valuation.lookup_append_left σ₂ τ₂ hmB]
          exact hAg (List.mem_append_right A hmQ) (List.mem_append_left R hmB)
        rw [Valuation.lookup_append_right (σ₁.append (σⱼ.reorder hJ)) τ₁ hmQ
              (List.disjoint_right.mp hdisjQ₁ hmQ),
            Valuation.lookup_append_left (σ₂.append σⱼ) τ₂
              (List.mem_append_left J₂ hmB),
            Valuation.lookup_append_left σ₂ σⱼ hmB]
        exact hQB
      · -- Q / J₂ impossible
        exact absurd hmQ
          (List.disjoint_left.mp hdisjQ₁ (List.mem_append_right A (hJ.mem_iff.mpr hmJ₂)))
    · -- Q / R
      have hnotA : (x, S) ∉ A :=
        fun h => (List.disjoint_right.mp hdisjQ₁ hmQ) (List.mem_append_left J₁ h)
      have hnotB : (x, S) ∉ B :=
        fun h => (List.disjoint_right.mp hdisjR₂ hmR) (List.mem_append_left J₂ h)
      have hQR : Valuation.lookup τ₁ x S = Valuation.lookup τ₂ x S := by
        rw [← Valuation.lookup_append_right σ₁ τ₁ hmQ hnotA,
          ← Valuation.lookup_append_right σ₂ τ₂ hmR hnotB]
        exact hAg (List.mem_append_right A hmQ) (List.mem_append_right B hmR)
      rw [Valuation.lookup_append_right (σ₁.append (σⱼ.reorder hJ)) τ₁ hmQ
            (List.disjoint_right.mp hdisjQ₁ hmQ),
          Valuation.lookup_append_right (σ₂.append σⱼ) τ₂ hmR
            (List.disjoint_right.mp hdisjR₂ hmR)]
      exact hQR

/-- Inversion for the `hasTypeCtrl` rule at the level of derivations.

Given a derivation `d` of a judgment whose expression is
`coherentControl e₀ Tc ls T'`, this produces the ctrl decomposition of `d`.
Because the expression index of the `hasTypeCtrl` constructor mentions
`l.map Prod.fst`, direct `cases` on `d` cannot invert the list equation;
this lemma performs the inversion by induction on `d` (permuting
derivations recurse to their inner derivation).

The exported data:

* `hPΓ hPΔ` — the decomposition contexts permute to the contexts of `d`;
* the branch list projects to `ls`;
* depth facts allowing `ih.mixed` and `ih.branch` to fire;
* for every valuation `σ τ` of `d`'s contexts, valuations `ρσ ρτ` of the
  decomposition contexts that answer lookups like `σ τ` on the
  decomposition domains, such that `pureAmplitude d σ τ v` equals the
  `branchAmplitude` of the decomposition at `ρσ ρτ`. -/
theorem PureDerivation.ctrl_amplitude {Γ Δ : Context} {e : Expression}
    {T : DataType} (d : PureDerivation Γ Δ e T) :
    ∀ (e₀ : Expression) (Tc : DataType) (ls : List (Expression × Expression)),
      e = Expression.coherentControl e₀ Tc ls T →
    ∃ Γa Γa' Δa Δa' : Context, ∃ l : List ((Expression × Expression) × Context),
      ∃ (_ : Context.WellFormed ((Γa ++ Γa') ++ Δa ++ Δa'))
         (dMix : MixedDerivation (Γa ++ Δa) e₀ Tc)
         (_ : Ortho Tc (l.map (Prod.fst ∘ Prod.fst)))
         (dB : BranchDerivation Γa Γa' Δa Δa' l Tc T)
         (_ : ∀ x, x ∈ Context.dom Δa → Erases x T (l.map (Prod.snd ∘ Prod.fst))),
        List.Perm (Γa ++ Γa') Γ ∧
        List.Perm (Δa ++ Δa') Δ ∧
        l.map Prod.fst = ls ∧
        Nat.succ dMix.depth ≤ PureDerivation.depth d ∧
        Nat.succ dB.depth ≤ PureDerivation.depth d ∧
        ∀ (σ : Valuation Γ) (τ : Valuation Δ) (v : Value T),
          ∃ (ρσ : Valuation (Γa ++ Γa')) (ρτ : Valuation (Δa ++ Δa')),
            (∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γa ++ Γa' →
                Valuation.lookup ρσ x S = Valuation.lookup σ x S) ∧
            (∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δa ++ Δa' →
                Valuation.lookup ρτ x S = Valuation.lookup τ x S) ∧
            pureAmplitude d σ τ v =
              branchAmplitude dB (fun u : Value Tc =>
                mixedAmplitude dMix
                  ((Valuation.split (Γ := Γa) (Δ := Γa') ρσ).1.append
                    (Valuation.split (Γ := Δa) (Δ := Δa') ρτ).1)
                  ((Valuation.split (Γ := Γa) (Δ := Γa') ρσ).1.append
                    (Valuation.split (Γ := Δa) (Δ := Δa') ρτ).1) u u) ρσ ρτ v :=
  match d with
  | .hasTypeUnit _ | .hasTypeCVar _ | .hasTypeQVar ..
  | .hasTypePurePair .. | .hasTypePureApp .. => by
      intro e₀ Tc ls hE
      nomatch hE
  | .hasTypePurePerm _ _ d' hΓ hΔ =>
      by
        intro e₀ Tc ls hE
        obtain ⟨Ga, Ga', Da, Da', l, hW, dMix, hOrtho, dB, hEr,
          hPΓ, hPΔ, hLmap, hD1, hD2, hEq⟩ := ctrl_amplitude d' e₀ Tc ls hE
        refine ⟨Ga, Ga', Da, Da', l, hW, dMix, hOrtho, dB, hEr,
          hPΓ.trans hΓ, hPΔ.trans hΔ, hLmap, ?_, ?_, ?_⟩
        · simp only [PureDerivation.depth]
          have := hD1
          omega
        · simp only [PureDerivation.depth]
          have := hD2
          omega
        · intro σ τ v
          obtain ⟨ρσ, ρτ, hrelσ, hrelτ, hamp⟩ :=
            hEq (σ.reorder hΓ) (τ.reorder hΔ) v
          refine ⟨ρσ, ρτ, ?_, ?_, ?_⟩
          · intro x S hx
            have hx' := hPΓ.mem_iff.mp hx
            exact (hrelσ hx).trans
              (Valuation.lookup_reorder hΓ σ hx' (hΓ.mem_iff.mp hx'))
          · intro x S hx
            have hx' := hPΔ.mem_iff.mp hx
            exact (hrelτ hx).trans
              (Valuation.lookup_reorder hΔ τ hx' (hΔ.mem_iff.mp hx'))
          · simp only [pureAmplitude]
            exact hamp
  | .hasTypeCtrl Ga Ga' Da Da' l _ _ _ hW dMix hOrtho dB hEr =>
      by
        intro e₀ Tc ls hE
        injection hE with h1 h2 h3
        subst h1
        subst h2
        refine ⟨Ga, Ga', Da, Da', l, hW, dMix, hOrtho, dB, hEr,
          List.Perm.refl _, List.Perm.refl _, h3, ?_, ?_, ?_⟩
        · simp only [PureDerivation.depth]
          omega
        · simp only [PureDerivation.depth]
          omega
        · intro σ τ v
          refine ⟨σ, τ, ?_, ?_, ?_⟩
          · intro x S hx
            rfl
          · intro x S hx
            rfl
          · simp only [pureAmplitude]
termination_by structural d

/-! ## Cancellation of permutation factors

Two list-cancellation facts used by the context-determination theorem: a
common multiset factor can be removed from an equation between permutations.
Both are proved by counting, so no duplicate-freeness side conditions are
needed. -/

theorem List.Perm.append_cancel_left {α : Type} [DecidableEq α]
    {A A' B B' : List α} (hA : List.Perm A A')
    (h : List.Perm (A ++ B) (A' ++ B')) : List.Perm B B' := by
  rw [List.perm_iff_count] at h ⊢
  intro x
  have h1 := h x
  have h2 := (List.perm_iff_count.mp hA) x
  simp only [List.count_append] at h1
  omega

theorem List.Perm.append_cancel_mid {α : Type} [DecidableEq α]
    {A A' J B B' : List α}
    (h : List.Perm (A ++ J ++ B) (A' ++ J ++ B')) :
    List.Perm (A ++ B) (A' ++ B') := by
  rw [List.perm_iff_count] at h ⊢
  intro x
  have h1 := h x
  simp only [List.count_append] at h1 ⊢
  omega

/-- A well-formed context is duplicate-free as a list of bindings. -/
theorem Context.WellFormed.nodup {Γ : Context} (h : Γ.WellFormed) : Γ.Nodup := by
  induction h with
  | nil => simp
  | cons hΓ hx ih =>
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hm
      exact hx ((Context.mem_dom_iff_in_context _ _).mpr
        (List.mem_map_of_mem (f := Prod.fst) hm))

/-- Combining two shared-prefix split equations into a permutation of the two
full contexts.  The duplicate-freeness hypotheses are essential: without them
the splits can overlap and the lengths need not agree. -/
theorem List.Perm.pair_combine {α : Type} [DecidableEq α]
    {Da₁ D0₁ D1₁ Da₂ D0₂ D1₂ : List α}
    (hnd₁ : (Da₁ ++ D0₁ ++ D1₁).Nodup) (hnd₂ : (Da₂ ++ D0₂ ++ D1₂).Nodup)
    (h0 : List.Perm (Da₁ ++ D0₁) (Da₂ ++ D0₂))
    (h1 : List.Perm (Da₁ ++ D1₁) (Da₂ ++ D1₂)) :
    List.Perm (Da₁ ++ D0₁ ++ D1₁) (Da₂ ++ D0₂ ++ D1₂) := by
  rw [List.perm_iff_count] at h0 h1 ⊢
  intro x
  have b₁ := (List.nodup_iff_count_le_one.mp hnd₁) x
  have b₂ := (List.nodup_iff_count_le_one.mp hnd₂) x
  have e0 := h0 x
  have e1 := h1 x
  simp only [List.count_append] at b₁ b₂ e0 e1 ⊢
  omega

/-! ## Enumeration length under permutations -/

theorem Valuation.enum_length : ∀ (Γ : Context),
    (Valuation.enum Γ).length =
      (Γ.map (fun p : Binding => (Value.enum p.2).length)).prod
  | [] => rfl
  | (x, T) :: Γ => by
      rw [Valuation.enum, List.length_flatMap]
      simp only [List.length_map]
      rw [Valuation.enum_length Γ]
      simp [List.sum_replicate, List.prod_cons]

theorem Valuation.enum_length_perm {Γ₁ Γ₂ : Context} (h : List.Perm Γ₁ Γ₂) :
    (Valuation.enum Γ₁).length = (Valuation.enum Γ₂).length := by
  rw [Valuation.enum_length, Valuation.enum_length]
  exact (h.map (fun p : Binding => (Value.enum p.2).length)).prod_eq

/-! ## Lookup at the head of a valuation -/

theorem Valuation.lookup_cons_self {x : Variable} {T : DataType} {Γ : Context}
    (v : Value T) (σ : Valuation Γ) :
    Valuation.lookup (Valuation.cons (x := x) (T := T) v σ) x T = some v := by
  simp [Valuation.lookup]

theorem Valuation.lookup_cons_tail {x y : Variable} {T S : DataType} {Γ : Context}
    (v : Value S) (σ : Valuation Γ) (h : ¬ (y = x ∧ S = T)) :
    Valuation.lookup (Valuation.cons (x := y) (T := S) v σ) x T
      = Valuation.lookup σ x T := by
  simp [Valuation.lookup, h]

/-! ## Valuation extensionality -/

theorem Valuation.ext {Γ : Context} (hnd : Γ.Nodup) {σ τ : Valuation Γ}
    (hl : ∀ (x : Variable) (S : DataType), (x, S) ∈ Γ →
      Valuation.lookup σ x S = Valuation.lookup τ x S) : σ = τ := by
  induction Γ with
  | nil =>
      cases σ
      cases τ
      rfl
  | cons p Γ ih =>
      obtain ⟨x, T⟩ := p
      cases σ with
      | cons v σ' =>
      cases τ with
      | cons w τ' =>
      have hv : v = w := by
        have hh := hl x T List.mem_cons_self
        rw [Valuation.lookup_cons_self, Valuation.lookup_cons_self] at hh
        exact Option.some.inj hh
      cases hv
      have ht : σ' = τ' := ih (List.nodup_cons.mp hnd).2 (fun x' S' hm => by
        have hne : ¬ ((x, T) = (x', S')) := fun heq =>
          (List.nodup_cons.mp hnd).1 (heq ▸ hm)
        have := hl x' S' (List.mem_cons_of_mem _ hm)
        rw [Valuation.lookup_cons_tail v σ' (fun hc => hne (by rw [hc.1, hc.2])),
          Valuation.lookup_cons_tail v τ' (fun hc => hne (by rw [hc.1, hc.2]))] at this
        exact this)
      rw [ht]

/-- When contexts are permutation-related, pairwise agreement transports
equality tests between valuations. This is the trace-test invariant needed by
the `try` rule. -/
theorem Valuation.Agreed.eq_iff_of_perm {Γ₁ Γ₂ : Context}
    (h : List.Perm Γ₁ Γ₂) (hnd₁ : Γ₁.Nodup) (hnd₂ : Γ₂.Nodup)
    (τ₁ τ₁' : Valuation Γ₁) (τ₂ τ₂' : Valuation Γ₂)
    (hAg : τ₁.Agreed τ₂) (hAg' : τ₁'.Agreed τ₂') :
    (τ₁ = τ₁') ↔ (τ₂ = τ₂') := by
  constructor
  · intro he
    apply Valuation.ext hnd₂
    intro x S hx
    have hx₁ : (x, S) ∈ Γ₁ := h.mem_iff.mpr hx
    calc
      Valuation.lookup τ₂ x S = Valuation.lookup τ₁ x S :=
        (hAg hx₁ hx).symm
      _ = Valuation.lookup τ₁' x S := by rw [he]
      _ = Valuation.lookup τ₂' x S := hAg' hx₁ hx
  · intro he
    apply Valuation.ext hnd₁
    intro x S hx
    have hx₂ : (x, S) ∈ Γ₂ := h.mem_iff.mp hx
    calc
      Valuation.lookup τ₁ x S = Valuation.lookup τ₂ x S := hAg hx hx₂
      _ = Valuation.lookup τ₂' x S := by rw [he]
      _ = Valuation.lookup τ₁' x S := (hAg' hx hx₂).symm

/-! ## Split and transport lemmas -/

/-- Splitting an appended valuation recovers the two summands. -/
theorem Valuation.split_append {Γ Δ : Context} :
    ∀ (σ : Valuation Γ) (ρ : Valuation Δ),
      (σ.append ρ).split = (σ, ρ) := by
  intro σ
  induction σ with
  | nil => intro ρ; rfl
  | cons v σ ih =>
      intro ρ
      show Valuation.split (Γ := _ :: _) (Δ := _) (.cons v (σ.append ρ)) = _
      rw [show Valuation.split (Γ := (_ : Context)) (Δ := _) (.cons v (σ.append ρ))
            = (.cons v (Valuation.split (Γ := _) (Δ := _) (σ.append ρ)).1,
               (Valuation.split (Γ := _) (Δ := _) (σ.append ρ)).2) from rfl,
        ih]

/-- A valuation is reconstructed from its split components. -/
theorem Valuation.split_append_inv : ∀ (Γ Δ : Context) (τ : Valuation (Γ ++ Δ)),
    τ = (Valuation.split (Γ := Γ) (Δ := Δ) τ).1.append
      (Valuation.split (Γ := Γ) (Δ := Δ) τ).2 := by
  intro Γ
  induction Γ with
  | nil => intro Δ τ; cases Δ <;> cases τ <;> rfl
  | cons p Γ ih =>
      obtain ⟨x, T⟩ := p
      intro Δ τ
      cases τ with
      | cons v τ' =>
          show Valuation.cons v τ' = _
          rw [show Valuation.split (Γ := (x, T) :: Γ) (Δ := Δ) (Valuation.cons v τ')
                = (Valuation.cons v (Valuation.split (Γ := Γ) (Δ := Δ) τ').1,
                   (Valuation.split (Γ := Γ) (Δ := Δ) τ').2) from rfl,
            show Valuation.append (Valuation.cons v
                  (Valuation.split (Γ := Γ) (Δ := Δ) τ').1)
                ((Valuation.split (Γ := Γ) (Δ := Δ) τ').2)
              = Valuation.cons v (Valuation.append
                  (Valuation.split (Γ := Γ) (Δ := Δ) τ').1
                  ((Valuation.split (Γ := Γ) (Δ := Δ) τ').2)) from rfl]
          exact congrArg (Valuation.cons (x := x) (T := T) (Γ := Γ ++ Δ) v)
            (ih Δ τ')

/-- The `T-MixedPair` rule re-associates its input valuation through
`List.append_assoc` before splitting.  This lemma (and the next) commute that
cast with the split, so the rule's `d₀`-input equals the cast-free
`(Δ ++ Δ₀)`-part of the valuation; the existing lookup lemmas
(`lookup_split_left/right`, `lookup_append_assoc`) compute all lookups, and
extensionality (available from well-formedness) transfers them to equalities
of valuations. -/
theorem Valuation.pair_first_split {Δ Δ₀ Δ₁ : Context}
    (hW : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁))
    (τ : Valuation ((Δ ++ Δ₀) ++ Δ₁)) :
    (Valuation.split (Γ := Δ) (Δ := Δ₀ ++ Δ₁)
        (List.append_assoc Δ Δ₀ Δ₁ ▸ τ)).1.append
      (Valuation.split (Γ := Δ₀) (Δ := Δ₁)
        (Valuation.split (Γ := Δ) (Δ := Δ₀ ++ Δ₁)
          (List.append_assoc Δ Δ₀ Δ₁ ▸ τ)).2).1
      = (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1 := by
  have hnd := Context.WellFormed.nodup hW
  have hndQ : List.Nodup (Δ ++ Δ₀) := List.Nodup.of_append_left hnd
  have hdisj₀ : List.Disjoint Δ Δ₀ := (List.nodup_append'.mp hndQ).2.2
  have hF : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ₀ → (x, S) ∉ Δ :=
    fun _ _ h₀ => List.disjoint_right.mp hdisj₀ h₀
  apply Valuation.ext hndQ
  intro x S hm
  rcases List.mem_append.mp hm with hΔ | hΔ₀
  · rw [Valuation.lookup_append_left _ _ hΔ,
      Valuation.lookup_split_left _ hΔ,
      Valuation.lookup_append_assoc,
      Valuation.lookup_split_left _ hm]
  · rw [Valuation.lookup_append_right _ _ hΔ₀ (hF hΔ₀),
      Valuation.lookup_split_left _ hΔ₀,
      Valuation.lookup_split_right _ (List.mem_append_left Δ₁ hΔ₀) (hF hΔ₀),
      Valuation.lookup_append_assoc,
      Valuation.lookup_split_left _ hm]

/-- The `d₁`-input of the `T-MixedPair` rule equals the cast-free
`(Δ ++ Δ₁)`-part of the valuation. -/
theorem Valuation.pair_second_split {Δ Δ₀ Δ₁ : Context}
    (hW : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁))
    (τ : Valuation ((Δ ++ Δ₀) ++ Δ₁)) :
    (Valuation.split (Γ := Δ) (Δ := Δ₀ ++ Δ₁)
        (List.append_assoc Δ Δ₀ Δ₁ ▸ τ)).1.append
      (Valuation.split (Γ := Δ₀) (Δ := Δ₁)
        (Valuation.split (Γ := Δ) (Δ := Δ₀ ++ Δ₁)
          (List.append_assoc Δ Δ₀ Δ₁ ▸ τ)).2).2
      = ((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
          (Γ := Δ) (Δ := Δ₀)).1.append
        (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2 := by
  have hnd := Context.WellFormed.nodup hW
  have hndΔ : List.Nodup Δ := (List.nodup_append'.mp (List.Nodup.of_append_left hnd)).1
  have hndΔ₁ : List.Nodup Δ₁ := (List.nodup_append'.mp hnd).2.1
  have hdisjQ₁ : List.Disjoint (Δ ++ Δ₀) Δ₁ := (List.nodup_append'.mp hnd).2.2
  have hdisjΔ₁ : List.Disjoint Δ Δ₁ :=
    fun _ h₁ => hdisjQ₁ (List.mem_append_left Δ₀ h₁)
  have hndR : List.Nodup (Δ ++ Δ₁) :=
    List.nodup_append'.mpr ⟨hndΔ, hndΔ₁, hdisjΔ₁⟩
  apply Valuation.ext hndR
  intro x S hm
  rcases List.mem_append.mp hm with hΔ | hΔ₁
  · rw [Valuation.lookup_append_left _ _ hΔ,
      Valuation.lookup_split_left _ hΔ,
      Valuation.lookup_append_assoc]
    rw [Valuation.lookup_append_left _ _ hΔ,
      Valuation.lookup_split_left _ hΔ,
      Valuation.lookup_split_left _ (List.mem_append_left Δ₀ hΔ)]
  · have hF : (x, S) ∉ Δ :=
      fun hmem => hdisjQ₁ (List.mem_append_left Δ₀ hmem) hΔ₁
    have hFQ : (x, S) ∉ Δ ++ Δ₀ := fun hmem => hdisjQ₁ hmem hΔ₁
    have hdisj₀ : List.Disjoint Δ Δ₀ :=
      (List.nodup_append'.mp (List.Nodup.of_append_left hnd)).2.2
    have hF₀ : (x, S) ∉ Δ₀ := by
      intro hmem
      rcases List.mem_append.mp hm with hΔ | hΔ₁
      · exact List.disjoint_right.mp hdisj₀ hmem hΔ
      · exact hdisjQ₁ (List.mem_append_right Δ hmem) hΔ₁
    calc
      Valuation.lookup ((Valuation.split (Γ := Δ) (Δ := Δ₀ ++ Δ₁)
          (List.append_assoc Δ Δ₀ Δ₁ ▸ τ)).1.append
        (Valuation.split (Γ := Δ₀) (Δ := Δ₁)
          (Valuation.split (Γ := Δ) (Δ := Δ₀ ++ Δ₁)
            (List.append_assoc Δ Δ₀ Δ₁ ▸ τ)).2).2) x S
          = Valuation.lookup (List.append_assoc Δ Δ₀ Δ₁ ▸ τ) x S :=
            Valuation.lookup_recombine_right _ hm hF₀
      _ = Valuation.lookup τ x S :=
            Valuation.lookup_append_assoc τ x S
      _ = Valuation.lookup (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
            (Γ := Δ) (Δ := Δ₀)).1.append
          (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2) x S := by
            rw [Valuation.lookup_append_right _ _ hΔ₁ hF,
              Valuation.lookup_split_right _ hΔ₁ hFQ]

/-! ## Reorder roundtrip -/

theorem Valuation.reorder_reorder {Γ Γ' : Context}
    (h : List.Perm Γ' Γ) (hnd : Γ.Nodup) (σ : Valuation Γ) :
    (σ.reorder h).reorder h.symm = σ := by
  apply Valuation.ext hnd
  intro x S hx
  rw [Valuation.lookup_reorder (h := h.symm) (σ := σ.reorder h)
    hx (h.mem_iff.mpr hx)]
  rw [Valuation.lookup_reorder (h := h) (σ := σ) (h.mem_iff.mpr hx) hx]

/-- Reordering valuations along a permutation is injective (on duplicate-free
contexts): this is what makes the `try` trace tests correspond across
permutation-related sides. -/
theorem Valuation.reorder_inj {Δ₁ Δ₂ : Context} (h : List.Perm Δ₁ Δ₂)
    (hnd₁ : Δ₁.Nodup) {σ σ' : Valuation Δ₁}
    (heq : σ.reorder h.symm = σ'.reorder h.symm) : σ = σ' := by
  have e₁ := Valuation.reorder_reorder (h := h.symm) hnd₁ σ
  have e₂ := Valuation.reorder_reorder (h := h.symm) hnd₁ σ'
  rw [heq] at e₁
  exact e₁.symm.trans e₂

/-! ## Enumeration is perm-stable -/

theorem Valuation.enum_map_reorder_perm {Δ₁ Δ₂ : Context}
    (h : List.Perm Δ₁ Δ₂) (hnd : Δ₂.Nodup) :
    List.Perm ((Valuation.enum Δ₁).map (fun τ => τ.reorder h.symm))
      (Valuation.enum Δ₂) := by
  have hsub : List.Subperm (Valuation.enum Δ₂)
      ((Valuation.enum Δ₁).map fun τ => τ.reorder h.symm) := by
    apply (Valuation.enum_nodup Δ₂).subperm
    intro τ₂ hτ₂
    exact List.mem_map.mpr
      ⟨τ₂.reorder h, Valuation.mem_enum _, Valuation.reorder_reorder h hnd τ₂⟩
  have hlen : ((Valuation.enum Δ₁).map fun τ => τ.reorder h.symm).length
      ≤ (Valuation.enum Δ₂).length := by
    rw [List.length_map, Valuation.enum_length_perm h]
  exact (hsub.perm_of_length_le hlen).symm

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

/-! ## Vanishing amplitudes -/

/-- A pure derivation has vanishing amplitude. -/
def PureVanishes {Γ Δ : Context} {e : Expression} {T : DataType}
    (d : PureDerivation Γ Δ e T) : Prop :=
  ∀ (σ : Valuation Γ) (τ : Valuation Δ) (v : Value T), pureAmplitude d σ τ v = 0

/-- A mixed derivation has vanishing amplitude. -/
def MixedVanishes {Δ : Context} {e : Expression} {T : DataType}
    (d : MixedDerivation Δ e T) : Prop :=
  ∀ (τ τ' : Valuation Δ) (v v' : Value T), mixedAmplitude d τ τ' v v' = 0

/-- A branch derivation has vanishing amplitude. -/
def BranchVanishes {Γ Γ' Δ Δ' : Context}
    {l : List ((Expression × Expression) × Context)} {T T' : DataType}
    (b : BranchDerivation Γ Γ' Δ Δ' l T T') : Prop :=
  ∀ (prob : Value T → ℂ) (σ : Valuation (Γ ++ Γ'))
    (τ : Valuation (Δ ++ Δ')) (v : Value T'), branchAmplitude b prob σ τ v = 0

theorem MixedVanishes.hasTypeMix {Δ : Context} {e : Expression} {T : DataType}
    (hW : Context.WellFormed Δ) (dp : PureDerivation [] Δ e T)
    (h : PureVanishes dp) :
    MixedVanishes (MixedDerivation.hasTypeMix hW dp) := by
  intro τ τ' v v'
  simp only [mixedAmplitude]
  rw [h]
  simp

theorem MixedVanishes.of_perm {Δ Δ' : Context} {e : Expression} {T : DataType}
    (hW : Context.WellFormed Δ') (d : MixedDerivation Δ e T)
    (hperm : List.Perm Δ Δ') (h : MixedVanishes d) :
    MixedVanishes (MixedDerivation.hasMixedTypePerm hW d hperm) := by
  intro τ τ' v v'
  simp only [mixedAmplitude]
  exact h _ _ _ _

theorem MixedVanishes.pair_left {Δ Δ₀ Δ₁ : Context} {e₀ e₁ : Expression}
    {T₀ T₁ : DataType} (hW : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁))
    (d₀ : MixedDerivation (Δ ++ Δ₀) e₀ T₀)
    (d₁ : MixedDerivation (Δ ++ Δ₁) e₁ T₁)
    (h : MixedVanishes d₀) :
    MixedVanishes (MixedDerivation.hasMixedTypePair hW d₀ d₁) := by
  intro τ τ' v v'
  simp only [mixedAmplitude]
  rw [h]
  simp

theorem MixedVanishes.pair_right {Δ Δ₀ Δ₁ : Context} {e₀ e₁ : Expression}
    {T₀ T₁ : DataType} (hW : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁))
    (d₀ : MixedDerivation (Δ ++ Δ₀) e₀ T₀)
    (d₁ : MixedDerivation (Δ ++ Δ₁) e₁ T₁)
    (h : MixedVanishes d₁) :
    MixedVanishes (MixedDerivation.hasMixedTypePair hW d₀ d₁) := by
  intro τ τ' v v'
  simp only [mixedAmplitude]
  rw [h]
  simp

theorem MixedVanishes.app {Δ : Context} {e : Expression} {f : Program}
    {T T' : DataType} (df : ProgramDerivation f (T ⇛ T'))
    (de : MixedDerivation Δ e T) (h : MixedVanishes de) :
    MixedVanishes (MixedDerivation.hasMixedTypeApp df de) := by
  intro τ τ' v v'
  simp only [mixedAmplitude]
  apply List.sum_eq_zero
  intro z hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  apply List.sum_eq_zero
  intro z' hz'
  rcases List.mem_map.mp hz' with ⟨w', hw', rfl⟩
  rw [h τ τ' w w']
  simp

theorem MixedVanishes.try_both {Δ₀ Δ₁ : Context} {e₀ e₁ : Expression}
    {T : DataType} (hW : Context.WellFormed (Δ₀ ++ Δ₁))
    (d₀ : MixedDerivation Δ₀ e₀ T) (d₁ : MixedDerivation Δ₁ e₁ T)
    (h₀ : MixedVanishes d₀) (h₁ : MixedVanishes d₁) :
    MixedVanishes (MixedDerivation.hasTypeTry hW d₀ d₁) := by
  intro τ τ' v v'
  simp only [mixedAmplitude]
  have htr : ((Value.enum T).map fun w =>
      mixedAmplitude d₀
        (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1
        (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1 w w).sum = 0 := by
    apply List.sum_eq_zero
    intro z hz
    rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact h₀ _ _ _ _
  rw [h₀ _ _ v v', h₁ _ _ v v', htr]
  simp

theorem PureVanishes.pair {Γ Δ Δ₀ Δ₁ : Context} {e₀ e₁ : Expression}
    {T₀ T₁ : DataType} (hΓ : Context.WellFormed Γ)
    (hΔ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁))
    (d₀ : PureDerivation Γ (Δ ++ Δ₀) e₀ T₀)
    (d₁ : PureDerivation Γ (Δ ++ Δ₁) e₁ T₁)
    (h : PureVanishes d₀) :
    PureVanishes (PureDerivation.hasTypePurePair hΓ hΔ d₀ d₁) := by
  intro σ τ v
  simp only [pureAmplitude]
  rw [h]
  simp

theorem PureVanishes.pair_right {Γ Δ Δ₀ Δ₁ : Context} {e₀ e₁ : Expression}
    {T₀ T₁ : DataType} (hΓ : Context.WellFormed Γ)
    (hΔ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁))
    (d₀ : PureDerivation Γ (Δ ++ Δ₀) e₀ T₀)
    (d₁ : PureDerivation Γ (Δ ++ Δ₁) e₁ T₁)
    (h : PureVanishes d₁) :
    PureVanishes (PureDerivation.hasTypePurePair hΓ hΔ d₀ d₁) := by
  intro σ τ v
  simp only [pureAmplitude]
  rw [h]
  simp

theorem PureVanishes.app {Γ Δ : Context} {e : Expression} {f : Program}
    {T T' : DataType} (df : ProgramDerivation f (T ⇝ T'))
    (de : PureDerivation Γ Δ e T) (h : PureVanishes de) :
    PureVanishes (PureDerivation.hasTypePureApp df de) := by
  intro σ τ v
  simp only [pureAmplitude]
  have hm : ((Value.enum T).map fun w =>
      programAmplitude df w v * pureAmplitude de σ τ w)
      = ((Value.enum T).map fun w => programAmplitude df w v * 0) := by
    apply List.map_congr_left
    intro w _
    rw [h]
  rw [hm]
  simp

theorem PureVanishes.of_perm {Γ Γ' Δ Δ' : Context} {e : Expression} {T : DataType}
    (hΓ : Context.WellFormed Γ') (hΔ : Context.WellFormed Δ')
    (d : PureDerivation Γ Δ e T) (hpΓ : List.Perm Γ Γ') (hpΔ : List.Perm Δ Δ')
    (h : PureVanishes d) :
    PureVanishes (PureDerivation.hasTypePurePerm hΓ hΔ d hpΓ hpΔ) := by
  intro σ τ v
  simp only [pureAmplitude]
  exact h _ _ _

theorem BranchVanishes.nil {Γ Γ' Δ Δ' : Context} {T T' : DataType} :
    BranchVanishes (BranchDerivation.nil Γ Γ' Δ Δ' T T') := by
  intro prob σ τ v
  simp only [branchAmplitude]

theorem BranchVanishes.cons {Γ Γ' Δ Δ' Γⱼ : Context}
    {eⱼ eⱼ' : Expression} {l : List ((Expression × Expression) × Context)}
    {T T' : DataType}
    (dPat : PureDerivation [] Γⱼ eⱼ T)
    (dBody : PureDerivation (Γ ++ Γ' ++ Γⱼ) (Δ ++ Δ') eⱼ' T')
    (b : BranchDerivation Γ Γ' Δ Δ' l T T')
    (hb : PureVanishes dBody) (ht : BranchVanishes b) :
    BranchVanishes (BranchDerivation.cons dPat dBody b) := by
  intro prob σ τ v
  simp only [branchAmplitude]
  rw [ht, add_zero]
  apply List.sum_eq_zero
  intro z hz
  rcases List.mem_map.mp hz with ⟨u, _, rfl⟩
  rw [show (((Valuation.enum Γⱼ).map fun σⱼ =>
      star (pureAmplitude dPat Valuation.nil σⱼ u) *
        pureAmplitude dBody (σ.append σⱼ) τ v).sum) = 0 from ?_]
  · simp
  · apply List.sum_eq_zero
    intro y hy
    rcases List.mem_map.mp hy with ⟨σⱼ, _, rfl⟩
    rw [hb]
    simp

theorem PureVanishes.ctrl {Γ Γ' Δ Δ' : Context}
    {l : List ((Expression × Expression) × Context)}
    {e : Expression} {T T' : DataType}
    (hW : Context.WellFormed (Γ ++ Γ' ++ Δ ++ Δ'))
    (dMix : MixedDerivation (Γ ++ Δ) e T)
    (hOrtho : Ortho T (l.map (Prod.fst ∘ Prod.fst)))
    (dB : BranchDerivation Γ Γ' Δ Δ' l T T')
    (hEr : ∀ x, x ∈ Context.dom Δ → Erases x T' (l.map (Prod.snd ∘ Prod.fst)))
    (h : BranchVanishes dB) :
    PureVanishes (PureDerivation.hasTypeCtrl Γ Γ' Δ Δ' l e T T'
      hW dMix hOrtho dB hEr) := by
  intro σ τ v
  simp only [pureAmplitude]
  exact h _ _ _ _

/-- A branch list vanishes when the head *pattern* derivation vanishes, provided
the tail vanishes: the head contribution is then a sum all of whose summands
carry the factor `star (pureAmplitude dPat …) = 0`. -/
theorem BranchVanishes.cons_of_pat {Γ Γ' Δ Δ' Γⱼ : Context}
    {eⱼ eⱼ' : Expression} {l : List ((Expression × Expression) × Context)}
    {T T' : DataType}
    (dPat : PureDerivation [] Γⱼ eⱼ T)
    (dBody : PureDerivation (Γ ++ Γ' ++ Γⱼ) (Δ ++ Δ') eⱼ' T')
    (b : BranchDerivation Γ Γ' Δ Δ' l T T')
    (hp : PureVanishes dPat) (ht : BranchVanishes b) :
    BranchVanishes (BranchDerivation.cons dPat dBody b) := by
  intro prob σ τ v
  simp only [branchAmplitude]
  rw [ht, add_zero]
  apply List.sum_eq_zero
  intro z hz
  rcases List.mem_map.mp hz with ⟨u, _, rfl⟩
  have hinner : ((Valuation.enum Γⱼ).map fun σⱼ =>
      star (pureAmplitude dPat .nil σⱼ u) *
        pureAmplitude dBody (σ.append σⱼ) τ v).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy
    rcases List.mem_map.mp hy with ⟨σⱼ, _, rfl⟩
    rw [hp, star_zero, zero_mul]
  rw [hinner, mul_zero]

/-- Implicit-argument variant of `PureVanishes.app` (the program derivation is
read off the goal). -/
theorem PureVanishes.appI {Γ Δ : Context} {e : Expression} {f : Program}
    {T T' : DataType} {df : ProgramDerivation f (T ⇝ T')}
    {de : PureDerivation Γ Δ e T} (h : PureVanishes de) :
    PureVanishes (PureDerivation.hasTypePureApp df de) :=
  PureVanishes.app df de h

/-- Implicit-argument variant of `PureVanishes.pair` (left factor). -/
theorem PureVanishes.pairI {Γ Δ Δ₀ Δ₁ : Context} {e₀ e₁ : Expression}
    {T₀ T₁ : DataType} {hΓ : Context.WellFormed Γ}
    {hΔ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
    {d₀ : PureDerivation Γ (Δ ++ Δ₀) e₀ T₀}
    {d₁ : PureDerivation Γ (Δ ++ Δ₁) e₁ T₁} (h : PureVanishes d₀) :
    PureVanishes (PureDerivation.hasTypePurePair hΓ hΔ d₀ d₁) :=
  PureVanishes.pair hΓ hΔ d₀ d₁ h

/-- Implicit-argument variant of `PureVanishes.pair` (right factor). -/
theorem PureVanishes.pairIr {Γ Δ Δ₀ Δ₁ : Context} {e₀ e₁ : Expression}
    {T₀ T₁ : DataType} {hΓ : Context.WellFormed Γ}
    {hΔ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
    {d₀ : PureDerivation Γ (Δ ++ Δ₀) e₀ T₀}
    {d₁ : PureDerivation Γ (Δ ++ Δ₁) e₁ T₁} (h : PureVanishes d₁) :
    PureVanishes (PureDerivation.hasTypePurePair hΓ hΔ d₀ d₁) :=
  PureVanishes.pair_right hΓ hΔ d₀ d₁ h

/-- Implicit-argument variant of `PureVanishes.of_perm`. -/
theorem PureVanishes.permI {Γ Γ' Δ Δ' : Context} {e : Expression} {T : DataType}
    {hΓ : Context.WellFormed Γ'} {hΔ : Context.WellFormed Δ'}
    {d : PureDerivation Γ Δ e T} {hpΓ : List.Perm Γ Γ'} {hpΔ : List.Perm Δ Δ'}
    (h : PureVanishes d) :
    PureVanishes (PureDerivation.hasTypePurePerm hΓ hΔ d hpΓ hpΔ) :=
  PureVanishes.of_perm hΓ hΔ d hpΓ hpΔ h

theorem PureDerivation.no_try {Γ Δ : Context} {e₀ e₁ : Expression} {T : DataType}
    (d : PureDerivation Γ Δ (.tryCatch e₀ e₁) T) : False := by
  cases d with
  | hasTypePurePerm _ _ d' _ _ => exact PureDerivation.no_try d'
termination_by d.depth
decreasing_by all_goals simp_all [PureDerivation.depth]

theorem PureDerivation.depth_cast_quantum {Γ Δ Δ' : Context}
    {e : Expression} {T : DataType} (h : Δ = Δ')
    (d : PureDerivation Γ Δ e T) :
    (h ▸ d).depth = d.depth := by
  cases h
  rfl


/-! ## Context determination

The remaining `prog`/`ctrl` comparisons need to know that two derivations of
the *same* expression and type live at quantum contexts that are
permutation-related, as soon as their classical contexts are permutation-
related (or empty) — unless their amplitudes vanish identically.  This
section proves exactly that, together with the mixed and pure-vs-mixed
analogues and the branch version needed by the `ctrl` case.

The statements are *disjunctive* because the typing rules genuinely
over-generate: context bindings can be moved between the shared and the
branch parts of a split, and the `ctrl` rule can choose an arbitrary quantum
branch context `Δ'` when the branch list is empty.  Derivations exploiting
that freedom have vanishing amplitude.

The classical-context hypothesis of `pure` and `branch` is *permutation*
(not equality): the branch case needs it because the per-branch pattern
contexts `Γⱼ` of two `ctrl` derivations are only permutation-related. -/

/-- The part of context determination needed for the amplitude induction:
pure derivations (and branch lists) at the same expression have permutation-
related contexts, unless both amplitudes vanish. -/
structure CtxDetPB (n : Nat) : Prop where
  /-- Two pure derivations whose classical contexts are permutation-related. -/
  pure : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : PureDerivation Γ₁ Δ₁ e T) (d₂ : PureDerivation Γ₂ Δ₂ e T),
    List.Perm Γ₁ Γ₂ → d₁.depth + d₂.depth ≤ n →
    List.Perm Δ₁ Δ₂ ∨ (PureVanishes d₁ ∧ PureVanishes d₂)
  /-- Two branch derivations over the same pattern-expression list, whose
  enclosing total classical contexts are permutation-related. -/
  branch : ∀ {Γa Γa' Δa Δa' Γb Γb' Δb Δb' : Context}
    {la lb : List ((Expression × Expression) × Context)} {T T' : DataType}
    (b₁ : BranchDerivation Γa Γa' Δa Δa' la T T')
    (b₂ : BranchDerivation Γb Γb' Δb Δb' lb T T'),
    la.map Prod.fst = lb.map Prod.fst →
    List.Perm (Γa ++ Γa') (Γb ++ Γb') → b₁.depth + b₂.depth ≤ n →
    List.Perm (Δa ++ Δa') (Δb ++ Δb') ∨ (BranchVanishes b₁ ∧ BranchVanishes b₂)

/-- Context determination facts at depth bound `n`. -/
structure CtxDet (n : Nat) : Prop where
  /-- Two pure derivations whose classical contexts are permutation-related. -/
  pure : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : PureDerivation Γ₁ Δ₁ e T) (d₂ : PureDerivation Γ₂ Δ₂ e T),
    List.Perm Γ₁ Γ₂ → d₁.depth + d₂.depth ≤ n →
    List.Perm Δ₁ Δ₂ ∨ (PureVanishes d₁ ∧ PureVanishes d₂)
  /-- Two mixed derivations. -/
  mixed : ∀ {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : MixedDerivation Δ₁ e T) (d₂ : MixedDerivation Δ₂ e T),
    d₁.depth + d₂.depth ≤ n →
    List.Perm Δ₁ Δ₂ ∨
      (MixedVanishes d₁ ∧ MixedVanishes d₂ ∧
        ∀ (τ₁ τ₁' : Valuation Δ₁) (τ₂ τ₂' : Valuation Δ₂),
          τ₁.Agreed τ₂ → τ₁'.Agreed τ₂' →
          ((τ₁ = τ₁') ↔ (τ₂ = τ₂')))
  /-- A pure derivation with empty classical context and a mixed derivation. -/
  pureMixed : ∀ {Γ₁ Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : PureDerivation Γ₁ Δ₁ e T) (d₂ : MixedDerivation Δ₂ e T),
    Γ₁ = [] → d₁.depth + d₂.depth ≤ n →
    List.Perm Δ₁ Δ₂ ∨ (PureVanishes d₁ ∧ MixedVanishes d₂)
  /-- Two branch derivations over the same pattern-expression list, whose
  enclosing total classical contexts are permutation-related. -/
  branch : ∀ {Γa Γa' Δa Δa' Γb Γb' Δb Δb' : Context}
    {la lb : List ((Expression × Expression) × Context)} {T T' : DataType}
    (b₁ : BranchDerivation Γa Γa' Δa Δa' la T T')
    (b₂ : BranchDerivation Γb Γb' Δb Δb' lb T T'),
    la.map Prod.fst = lb.map Prod.fst →
    List.Perm (Γa ++ Γa') (Γb ++ Γb') → b₁.depth + b₂.depth ≤ n →
    List.Perm (Δa ++ Δa') (Δb ++ Δb') ∨ (BranchVanishes b₁ ∧ BranchVanishes b₂)

/-- Context determination for pure/mixed comparisons. This fragment does not
depend on mixed/mixed context determination. -/
structure CtxDetPM (n : Nat) : Prop where
  pb : CtxDetPB n
  pureMixed : ∀ {Γ₁ Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : PureDerivation Γ₁ Δ₁ e T) (d₂ : MixedDerivation Δ₂ e T),
    Γ₁ = [] → d₁.depth + d₂.depth ≤ n →
    List.Perm Δ₁ Δ₂ ∨ (PureVanishes d₁ ∧ MixedVanishes d₂)

/-- Context determination for mixed derivations preserves the within-side
valuation equality tests used by `try`. In the permutation case this follows
from extensionality; in the vanishing case it is recorded explicitly. -/
theorem CtxDet.mixed_trace {n : Nat} (det : CtxDet n)
    {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : MixedDerivation Δ₁ e T) (d₂ : MixedDerivation Δ₂ e T)
    (hsum : d₁.depth + d₂.depth ≤ n)
    (τ₁ τ₁' : Valuation Δ₁) (τ₂ τ₂' : Valuation Δ₂)
    (hAg : τ₁.Agreed τ₂) (hAg' : τ₁'.Agreed τ₂') :
    (τ₁ = τ₁') ↔ (τ₂ = τ₂') := by
  rcases det.mixed d₁ d₂ hsum with hperm | ⟨_, _, htrace⟩
  · exact Valuation.Agreed.eq_iff_of_perm hperm
      (Context.WellFormed.nodup
        (HasMixedType.context_well_formed d₁.toProp))
      (Context.WellFormed.nodup
        (HasMixedType.context_well_formed d₂.toProp))
      τ₁ τ₁' τ₂ τ₂' hAg hAg'
  · exact @htrace τ₁ τ₁' τ₂ τ₂' hAg hAg'

/-- Base case of context determination: at depth zero every pure derivation
is `unit`, `cvar` or `qvar`, and two of them over the same expression agree on
their quantum context (up to permutation); mixed derivations have positive
depth and branch derivations of depth zero are `nil`. -/
theorem ctxDet_base : CtxDet 0 where
  pure := by
    intro Γ₁ Γ₂ Δ₁ Δ₂ e T d₁ d₂ hΓperm hsum
    have hz₁ : d₁.depth = 0 := by omega
    have hz₂ : d₂.depth = 0 := by omega
    rcases PureDerivation.eq_of_depth_zero d₁ hz₁ with
      ⟨he₁, -, hΔ₁, -⟩ | ⟨Ga, Gb, x, he₁, hΔ₁, hGeq₁, -⟩ |
      ⟨x, he₁, hΔ₁, -, hxdom₁, -⟩
    · rcases PureDerivation.eq_of_depth_zero d₂ hz₂ with
        ⟨he₂, -, hΔ₂, -⟩ | ⟨Ga, Gb, x, he₂, hΔ₂, hGeq₂, -⟩ |
        ⟨x, he₂, hΔ₂, -, -, -⟩
      · subst hΔ₁; subst hΔ₂; exact Or.inl (List.Perm.refl [])
      · exact absurd (he₁.symm.trans he₂) (by simp)
      · exact absurd (he₁.symm.trans he₂) (by simp)
    · -- `cvar` on the left
      rcases PureDerivation.eq_of_depth_zero d₂ hz₂ with
        ⟨he₂, -, hΔ₂, -⟩ | ⟨Ga', Gb', x', he₂, hΔ₂, hGeq₂, -⟩ |
        ⟨x', he₂, hΔ₂, -, hxdom₂, -⟩
      · exact absurd (he₁.symm.trans he₂) (by simp)
      · subst hΔ₁; subst hΔ₂; exact Or.inl (List.Perm.refl [])
      · have hxx : x = x' := by injection he₁.symm.trans he₂
        subst hxx
        subst hGeq₁
        have hxmem : (x, T) ∈ Γ₂ := hΓperm.mem_iff.mp
          (List.mem_append_left Gb
            (List.mem_append_right Ga (List.mem_singleton_self (x, T))))
        exact absurd hxmem (fun hm => hxdom₂ (by
          rw [Context.mem_dom_iff_in_context]
          exact List.mem_map_of_mem (f := Prod.fst) hm))
    · -- `qvar` on the left
      rcases PureDerivation.eq_of_depth_zero d₂ hz₂ with
        ⟨he₂, -, hΔ₂, -⟩ | ⟨Ga', Gb', x', he₂, hΔ₂, hGeq₂, -⟩ |
        ⟨x', he₂, hΔ₂, -, hxdom₂, -⟩
      · exact absurd (he₁.symm.trans he₂) (by simp)
      · have hxx : x = x' := by injection he₁.symm.trans he₂
        subst hxx
        subst hGeq₂
        have hxmem : (x, T) ∈ Γ₁ := hΓperm.mem_iff.mpr
          (List.mem_append_left Gb'
            (List.mem_append_right Ga' (List.mem_singleton_self (x, T))))
        exact absurd hxmem (fun hm => hxdom₁ (by
          rw [Context.mem_dom_iff_in_context]
          exact List.mem_map_of_mem (f := Prod.fst) hm))
      · have hxx : x = x' := by injection he₁.symm.trans he₂
        subst hxx; subst hΔ₁; subst hΔ₂
        exact Or.inl (List.Perm.refl _)
  mixed := by
    intro Δ₁ Δ₂ e T d₁ d₂ hsum
    cases d₁ <;> (simp only [MixedDerivation.depth] at hsum; omega)
  pureMixed := by
    intro Γ₁ Δ₁ Δ₂ e T d₁ d₂ hΓ₁ hsum
    cases d₂ <;> (simp only [MixedDerivation.depth] at hsum; omega)
  branch := by
    intro Γa Γa' Δa Δa' Γb Γb' Δb Δb' la lb T T' b₁ b₂ hmap hΓperm hsum
    have hz₁ : b₁.depth = 0 := by omega
    have hz₂ : b₂.depth = 0 := by omega
    cases b₁ with
    | nil =>
        cases b₂ with
        | nil => exact Or.inr ⟨BranchVanishes.nil, BranchVanishes.nil⟩
        | cons => simp [BranchDerivation.depth] at hz₂
    | cons => simp [BranchDerivation.depth] at hz₁

/-- Successor step for the `pure` field of context determination. -/
theorem ctxDet_pure_step {n : Nat} (ih : CtxDetPB n) :
    ∀ {Γ₁ Γ₂ Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
      (d₁ : PureDerivation Γ₁ Δ₁ e T) (d₂ : PureDerivation Γ₂ Δ₂ e T),
      List.Perm Γ₁ Γ₂ → d₁.depth + d₂.depth ≤ n + 1 →
      List.Perm Δ₁ Δ₂ ∨ (PureVanishes d₁ ∧ PureVanishes d₂) := by
  intro Γ₁ Γ₂ Δ₁ Δ₂ e T d₁ d₂ hΓperm hsum
  cases d₂ with
  | hasTypeUnit hW₂ =>
      cases d₁ with
      | hasTypeUnit hW₁ => exact Or.inl (List.Perm.refl _)
      | hasTypePurePerm hW₁ hWΔ₁ d₁' hp₁Γ hp₁Δ =>
          have hΓ₁' : List.Perm _ Γ₂ := hp₁Γ.trans hΓperm
          have hb : d₁'.depth + (PureDerivation.hasTypeUnit hW₂).depth ≤ n := by
            simp only [PureDerivation.depth] at hsum ⊢
            omega
          rcases ih.pure d₁' (PureDerivation.hasTypeUnit hW₂) hΓ₁' hb with
            hp | ⟨v₁, v₂⟩
          · exact Or.inl (hp₁Δ.symm.trans hp)
          · exact Or.inr ⟨PureVanishes.permI v₁, v₂⟩
  | hasTypeCVar hW₂ =>
      rename_i Ga₂ Gb₂ x
      cases d₁ with
      | hasTypeCVar hW₁ => exact Or.inl (List.Perm.refl [])
      | hasTypeQVar hW₁ hx₁ =>
          exfalso
          have hxmem : (x, T) ∈ Ga₂ ++ [(x, T)] ++ Gb₂ :=
            List.mem_append_left Gb₂
              (List.mem_append_right Ga₂ (List.mem_singleton_self (x, T)))
          have hin := hΓperm.mem_iff.mpr hxmem
          exact hx₁ ((Context.mem_dom_iff_in_context x _).mpr
            (List.mem_map_of_mem (f := Prod.fst) hin))
      | hasTypePurePerm hW₁ hWΔ₁ d₁' hp₁Γ hp₁Δ =>
          have hΓ₁' : List.Perm _ (Ga₂ ++ [(x, T)] ++ Gb₂) := hp₁Γ.trans hΓperm
          have hb : d₁'.depth + (PureDerivation.hasTypeCVar hW₂).depth ≤ n := by
            simp only [PureDerivation.depth] at hsum ⊢
            omega
          rcases ih.pure d₁' (PureDerivation.hasTypeCVar hW₂) hΓ₁' hb with
            hp | ⟨v₁, v₂⟩
          · exact Or.inl (hp₁Δ.symm.trans hp)
          · exact Or.inr ⟨PureVanishes.permI v₁, v₂⟩
  | hasTypeQVar hW₂ hx₂ =>
      rename_i x
      cases d₁ with
      | hasTypeCVar hW₁ =>
          rename_i Ga₁ Gb₁
          exfalso
          have hxmem : (x, T) ∈ Ga₁ ++ [(x, T)] ++ Gb₁ :=
            List.mem_append_left Gb₁
              (List.mem_append_right Ga₁ (List.mem_singleton_self (x, T)))
          have hin := hΓperm.mem_iff.mp hxmem
          exact hx₂ ((Context.mem_dom_iff_in_context x _).mpr
            (List.mem_map_of_mem (f := Prod.fst) hin))
      | hasTypeQVar hW₁ hx₁ => exact Or.inl (List.Perm.refl _)
      | hasTypePurePerm hW₁ hWΔ₁ d₁' hp₁Γ hp₁Δ =>
          have hΓ₁' : List.Perm _ Γ₂ := hp₁Γ.trans hΓperm
          have hb : d₁'.depth
              + (PureDerivation.hasTypeQVar (T := T) hW₂ hx₂).depth ≤ n := by
            simp only [PureDerivation.depth] at hsum ⊢
            omega
          rcases ih.pure d₁'
            (PureDerivation.hasTypeQVar (T := T) hW₂ hx₂) hΓ₁' hb with
            hp | ⟨v₁, v₂⟩
          · exact Or.inl (hp₁Δ.symm.trans hp)
          · exact Or.inr ⟨PureVanishes.permI v₁, v₂⟩
  | hasTypePurePair hG₂ hD₂ d₀₂ d₁₂ =>
      rename_i D₂ D0₂ D1₂
      cases d₁ with
      | hasTypePurePair hG₁ hD₁ d₀₁ d₁₁ =>
          rename_i D₁ D0₁ D1₁
          have hb0 : d₀₁.depth + d₀₂.depth ≤ n := by
            simp only [PureDerivation.depth] at hsum
            have m1 : d₀₁.depth ≤ Nat.max d₀₁.depth d₁₁.depth := Nat.le_max_left _ _
            have m2 : d₀₂.depth ≤ Nat.max d₀₂.depth d₁₂.depth := Nat.le_max_left _ _
            omega
          have hb1 : d₁₁.depth + d₁₂.depth ≤ n := by
            simp only [PureDerivation.depth] at hsum
            have m1 : d₁₁.depth ≤ Nat.max d₀₁.depth d₁₁.depth := Nat.le_max_right _ _
            have m2 : d₁₂.depth ≤ Nat.max d₀₂.depth d₁₂.depth := Nat.le_max_right _ _
            omega
          rcases ih.pure d₀₁ d₀₂ hΓperm hb0 with h0 | ⟨v01, v02⟩
          · rcases ih.pure d₁₁ d₁₂ hΓperm hb1 with h1 | ⟨v11, v12⟩
            · exact Or.inl (List.Perm.pair_combine hD₁.nodup hD₂.nodup h0 h1)
            · exact Or.inr ⟨PureVanishes.pairIr v11, PureVanishes.pairIr v12⟩
          · exact Or.inr ⟨PureVanishes.pairI v01, PureVanishes.pairI v02⟩
      | hasTypePurePerm hW₁ hWΔ₁ d₁' hp₁Γ hp₁Δ =>
          have hΓ₁' : List.Perm _ Γ₂ := hp₁Γ.trans hΓperm
          have hb : d₁'.depth
              + (PureDerivation.hasTypePurePair hG₂ hD₂ d₀₂ d₁₂).depth ≤ n := by
            simp only [PureDerivation.depth] at hsum ⊢
            omega
          rcases ih.pure d₁'
            (PureDerivation.hasTypePurePair hG₂ hD₂ d₀₂ d₁₂) hΓ₁' hb with
            hp | ⟨v₁, v₂⟩
          · exact Or.inl (hp₁Δ.symm.trans hp)
          · exact Or.inr ⟨PureVanishes.permI v₁, v₂⟩
  | hasTypePureApp df₂ de₂ =>
      cases d₁ with
      | hasTypePureApp df₁ de₁ =>
          cases df₂ <;> cases df₁
          all_goals
            have hb : de₁.depth + de₂.depth ≤ n := by
              simp only [PureDerivation.depth] at hsum
              omega
            rcases ih.pure de₁ de₂ hΓperm hb with h | ⟨v₁, v₂⟩
            · exact Or.inl h
            · exact Or.inr ⟨PureVanishes.appI v₁, PureVanishes.appI v₂⟩
      | hasTypePurePerm hW₁ hWΔ₁ d₁' hp₁Γ hp₁Δ =>
          have hΓ₁' : List.Perm _ Γ₂ := hp₁Γ.trans hΓperm
          have hb : d₁'.depth
              + (PureDerivation.hasTypePureApp df₂ de₂).depth ≤ n := by
            simp only [PureDerivation.depth] at hsum ⊢
            omega
          rcases ih.pure d₁'
            (PureDerivation.hasTypePureApp df₂ de₂) hΓ₁' hb with
            hp | ⟨v₁, v₂⟩
          · exact Or.inl (hp₁Δ.symm.trans hp)
          · exact Or.inr ⟨PureVanishes.permI v₁, v₂⟩
  | hasTypeCtrl Ga₂ Ga₂' Da₂ Da₂' l₂ e₀ Tc₂ Tr₂ hW₂ dMix₂ hOrtho₂ dB₂ hEr₂ =>
      obtain ⟨Ga₁, Ga₁', Da₁, Da₁', l₁, hW₁, dMix₁, hOrtho₁, dB₁, hEr₁,
        hPΓ₁, hPΔ₁, hLmap₁, hD1₁, hD2₁, hEq₁⟩ :=
        PureDerivation.ctrl_amplitude d₁ e₀ Tc₂ (l₂.map Prod.fst) rfl
      have hΓperm' : List.Perm (Ga₁ ++ Ga₁') (Ga₂ ++ Ga₂') := hPΓ₁.trans hΓperm
      have hdepth : dB₁.depth + dB₂.depth ≤ n := by
        simp only [PureDerivation.depth] at hsum
        have m2 : dB₂.depth ≤ Nat.max dMix₂.depth dB₂.depth := Nat.le_max_right _ _
        omega
      rcases ih.branch dB₁ dB₂ hLmap₁ hΓperm' hdepth with hperm | ⟨vB₁, vB₂⟩
      · exact Or.inl (hPΔ₁.symm.trans hperm)
      · refine Or.inr ⟨?_, PureVanishes.ctrl hW₂ dMix₂ hOrtho₂ dB₂ hEr₂ vB₂⟩
        intro σ τ v
        obtain ⟨ρσ, ρτ, -, -, hval⟩ := hEq₁ σ τ v
        rw [hval]
        exact vB₁ _ ρσ ρτ v
  | hasTypePurePerm hW₂ hWΔ₂ d₂' hp₂Γ hp₂Δ =>
      have hΓ₂' : List.Perm Γ₁ _ := hΓperm.trans hp₂Γ.symm
      have hb : d₁.depth + d₂'.depth ≤ n := by
        simp only [PureDerivation.depth] at hsum ⊢
        omega
      rcases ih.pure d₁ d₂' hΓ₂' hb with hp | ⟨v₁, v₂⟩
      · exact Or.inl (hp.trans hp₂Δ)
      · exact Or.inr ⟨v₁, PureVanishes.permI v₂⟩

/-- Successor step for the `branch` field of context determination. -/
theorem ctxDet_branch_step {n : Nat} (ih : CtxDetPB n) :
    ∀ {Γa Γa' Δa Δa' Γb Γb' Δb Δb' : Context}
      {la lb : List ((Expression × Expression) × Context)} {T T' : DataType}
      (b₁ : BranchDerivation Γa Γa' Δa Δa' la T T')
      (b₂ : BranchDerivation Γb Γb' Δb Δb' lb T T'),
      la.map Prod.fst = lb.map Prod.fst →
      List.Perm (Γa ++ Γa') (Γb ++ Γb') →
      b₁.depth + b₂.depth ≤ n + 1 →
      List.Perm (Δa ++ Δa') (Δb ++ Δb') ∨ (BranchVanishes b₁ ∧ BranchVanishes b₂) := by
  intro Γa Γa' Δa Δa' Γb Γb' Δb Δb' la lb T T' b₁ b₂ hmap hΓperm hsum
  revert hmap
  cases b₂ with
  | nil _ _ _ _ _ _ =>
      cases b₁ with
      | nil _ _ _ _ _ _ =>
          intro _
          exact Or.inr ⟨BranchVanishes.nil, BranchVanishes.nil⟩
      | cons _ _ _ =>
          intro hmap
          exact absurd hmap (by simp)
  | cons dPat₂ dBody₂ b₂' =>
      cases b₁ with
      | nil _ _ _ _ _ _ =>
          intro hmap
          exact absurd hmap (by simp)
      | cons dPat₁ dBody₁ b₁' =>
          intro hmap
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hmap
          obtain ⟨⟨he, he'⟩, htail⟩ := hmap
          subst he
          subst he'
          have hdepths : dPat₁.depth + dPat₂.depth ≤ n
              ∧ dBody₁.depth + dBody₂.depth ≤ n
              ∧ b₁'.depth + b₂'.depth ≤ n := by
            simp only [BranchDerivation.depth] at hsum
            have a1 : dPat₁.depth
                ≤ Nat.max dPat₁.depth dBody₁.depth := Nat.le_max_left _ _
            have a2 : dBody₁.depth
                ≤ Nat.max dPat₁.depth dBody₁.depth := Nat.le_max_right _ _
            have a3 : Nat.max dPat₁.depth dBody₁.depth
                ≤ Nat.max (Nat.max dPat₁.depth dBody₁.depth) b₁'.depth :=
              Nat.le_max_left _ _
            have b1 : dPat₂.depth
                ≤ Nat.max dPat₂.depth dBody₂.depth := Nat.le_max_left _ _
            have b2 : dBody₂.depth
                ≤ Nat.max dPat₂.depth dBody₂.depth := Nat.le_max_right _ _
            have b3 : Nat.max dPat₂.depth dBody₂.depth
                ≤ Nat.max (Nat.max dPat₂.depth dBody₂.depth) b₂'.depth :=
              Nat.le_max_left _ _
            omega
          obtain ⟨hpat, hbody, htaild⟩ := hdepths
          rcases ih.pure dPat₁ dPat₂ (List.Perm.refl []) hpat with
            hpatperm | ⟨vp₁, vp₂⟩
          · rcases ih.pure dBody₁ dBody₂ (hΓperm.append hpatperm) hbody with
              hbodyperm | ⟨vb₁, vb₂⟩
            · exact Or.inl hbodyperm
            · rcases ih.branch b₁' b₂' htail hΓperm htaild with
                htailperm | ⟨vt₁, vt₂⟩
              · exact Or.inl htailperm
              · exact Or.inr
                  ⟨BranchVanishes.cons dPat₁ dBody₁ b₁' vb₁ vt₁,
                   BranchVanishes.cons dPat₂ dBody₂ b₂' vb₂ vt₂⟩
          · rcases ih.branch b₁' b₂' htail hΓperm htaild with
              htailperm | ⟨vt₁, vt₂⟩
            · exact Or.inl htailperm
            · exact Or.inr
                ⟨BranchVanishes.cons_of_pat dPat₁ dBody₁ b₁' vp₁ vt₁,
                 BranchVanishes.cons_of_pat dPat₂ dBody₂ b₂' vp₂ vt₂⟩

/-- The source type of a program is fixed by its expression, whether it is
typed coherently or as a channel. -/
theorem ProgramDerivation.coherent_channel_input_eq {f : Program}
    {S₁ S₂ T₁ T₂ : DataType}
    (d₁ : ProgramDerivation f (S₁ ⇝ T₁))
    (d₂ : ProgramDerivation f (S₂ ⇛ T₂)) : S₁ = S₂ := by
  cases d₁ with
  | hasTypeGate => cases d₂ with | hasTypeChannel d => cases d; rfl
  | hasTypeLeft => cases d₂ with | hasTypeChannel d => cases d; rfl
  | hasTypeRight => cases d₂ with | hasTypeChannel d => cases d; rfl
  | hasCoherentTypeAbs dp dq =>
      cases d₂ with
      | hasTypeChannel d =>
          cases d with
          | hasCoherentTypeAbs _ _ => rfl
      | hasChannelTypeAbs dp' dm' => rfl
  | hasTypeRphase dp =>
      cases d₂ with
      | hasTypeChannel d =>
          cases d with
          | hasTypeRphase _ => rfl

/-- Successor context determination for a pure derivation at empty classical
context against a mixed derivation. -/
theorem ctxDet_pureMixed_step {n : Nat} (ih : CtxDetPM n) :
    ∀ {Γ₁ Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
      (d₁ : PureDerivation Γ₁ Δ₁ e T) (d₂ : MixedDerivation Δ₂ e T),
      Γ₁ = [] → d₁.depth + d₂.depth ≤ n + 1 →
      List.Perm Δ₁ Δ₂ ∨ (PureVanishes d₁ ∧ MixedVanishes d₂) := by
  intro Γ₁ Δ₁ Δ₂ e T d₁ d₂ hΓ hsum
  cases d₂ with
  | hasMixedTypePerm hW₂ d₂' hperm₂ =>
      have hb : d₁.depth + d₂'.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum
        omega
      rcases ih.pureMixed d₁ d₂' hΓ hb with hp | ⟨hpv, hmv⟩
      · exact Or.inl (hp.trans hperm₂)
      · exact Or.inr ⟨hpv, MixedVanishes.of_perm hW₂ d₂' hperm₂ hmv⟩
  | hasTypeMix hW₂ dp₂ =>
      have hb : d₁.depth + dp₂.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum
        omega
      rcases ih.pb.pure d₁ dp₂ (by simp [hΓ]) hb with hp | ⟨hpv, hpv₂⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hpv, MixedVanishes.hasTypeMix hW₂ dp₂ hpv₂⟩
  | hasMixedTypePair hW₂ d₀₂ d₁₂ =>
      cases d₁ with
      | hasTypePurePerm hWΓ hWΔ d₁' hΓ' hΔ' =>
          have hΓnil : List.Perm _ [] := hΓ ▸ hΓ'
          have hΓinner := List.Perm.eq_nil hΓnil
          cases hΓinner
          cases hΓ
          have hb : d₁'.depth
              + (MixedDerivation.hasMixedTypePair hW₂ d₀₂ d₁₂).depth ≤ n := by
            simp only [PureDerivation.depth, MixedDerivation.depth] at hsum ⊢
            omega
          rcases ih.pureMixed d₁' (MixedDerivation.hasMixedTypePair hW₂ d₀₂ d₁₂)
              rfl hb with hp | ⟨hpv, hmv⟩
          · exact Or.inl (hΔ'.symm.trans hp)
          · exact Or.inr ⟨PureVanishes.permI hpv, hmv⟩
      | hasTypePurePair hG₁ hD₁ d₀₁ d₁₁ =>
          cases hΓ
          have hdepths : d₀₁.depth + d₀₂.depth ≤ n
              ∧ d₁₁.depth + d₁₂.depth ≤ n := by
            simp only [PureDerivation.depth, MixedDerivation.depth] at hsum
            have m₁ := Nat.le_max_left d₀₁.depth d₁₁.depth
            have m₂ := Nat.le_max_right d₀₁.depth d₁₁.depth
            have m₃ := Nat.le_max_left d₀₂.depth d₁₂.depth
            have m₄ := Nat.le_max_right d₀₂.depth d₁₂.depth
            omega
          obtain ⟨hb₀, hb₁⟩ := hdepths
          rcases ih.pureMixed d₀₁ d₀₂ rfl hb₀ with h₀ | ⟨vp₀, vm₀⟩
          · rcases ih.pureMixed d₁₁ d₁₂ rfl hb₁ with h₁ | ⟨vp₁, vm₁⟩
            · exact Or.inl (List.Perm.pair_combine hD₁.nodup hW₂.nodup h₀ h₁)
            · exact Or.inr
                ⟨PureVanishes.pairIr vp₁, MixedVanishes.pair_right hW₂ d₀₂ d₁₂ vm₁⟩
          · exact Or.inr
              ⟨PureVanishes.pairI vp₀, MixedVanishes.pair_left hW₂ d₀₂ d₁₂ vm₀⟩
  | hasTypeTry hW₂ d₀₂ d₁₂ =>
      exact False.elim (PureDerivation.no_try d₁)
  | hasMixedTypeApp df₂ de₂ =>
      cases d₁ with
      | hasTypePurePerm hWΓ hWΔ d₁' hΓ' hΔ' =>
          have hΓnil : List.Perm _ [] := hΓ ▸ hΓ'
          have hΓinner := List.Perm.eq_nil hΓnil
          cases hΓinner
          cases hΓ
          have hb : d₁'.depth
              + (MixedDerivation.hasMixedTypeApp df₂ de₂).depth ≤ n := by
            simp only [PureDerivation.depth, MixedDerivation.depth] at hsum ⊢
            omega
          rcases ih.pureMixed d₁' (MixedDerivation.hasMixedTypeApp df₂ de₂)
              rfl hb with hp | ⟨hpv, hmv⟩
          · exact Or.inl (hΔ'.symm.trans hp)
          · exact Or.inr ⟨PureVanishes.permI hpv, hmv⟩
      | hasTypePureApp df₁ de₁ =>
          cases hΓ
          have hS := ProgramDerivation.coherent_channel_input_eq df₁ df₂
          cases hS
          have hb : de₁.depth + de₂.depth ≤ n := by
            simp only [PureDerivation.depth, MixedDerivation.depth] at hsum
            omega
          rcases ih.pureMixed de₁ de₂ rfl hb with hΔ | ⟨hpv, hmv⟩
          · exact Or.inl hΔ
          · exact Or.inr
              ⟨PureVanishes.appI hpv, MixedVanishes.app df₂ de₂ hmv⟩

/-- Base case for `CtxDetPB`, extracted from `ctxDet_base`. -/
theorem ctxDetPB_base : CtxDetPB 0 where
  pure := ctxDet_base.pure
  branch := ctxDet_base.branch

/-- Context determination for pure/`branch`, at every depth. -/
theorem ctxDetPB_all (n : Nat) : CtxDetPB n := by
  induction n with
  | zero => exact ctxDetPB_base
  | succ n ih => exact ⟨ctxDet_pure_step ih, ctxDet_branch_step ih⟩

theorem ctxDetPM_base : CtxDetPM 0 where
  pb := ctxDetPB_base
  pureMixed := ctxDet_base.pureMixed

theorem ctxDetPM_all (n : Nat) : CtxDetPM n := by
  induction n with
  | zero => exact ctxDetPM_base
  | succ n ih =>
      exact ⟨ctxDetPB_all (n + 1), ctxDet_pureMixed_step ih⟩

/-! ## The refined equivalence family

Appendix G of the paper compares *equivalent proofs* (Definition G.2): two
proofs of the same judgment in which every context decomposition chosen by a
rule is recorded, so that equivalent proofs use corresponding decompositions,
up to permutation of each component.  This matters for `try` (its trace
tests are taken along each side's own decomposition) and equally for
`purePair` and `ctrl`, whose decompositions are free rule data.

The three judgments are mutually recursive, so the relations are too: the
`mix` rule of the mixed judgment records a *pure* equivalence between its
two pure sub-proofs; the `ctrl` rule of the pure judgment records a *mixed*
equivalence between its control sub-proofs together with a *branch*
equivalence between its branch lists; each branch records pure equivalences
for its pattern and body.  The relations are proof-relevant (in `Type`) so
that they can carry the componentwise permutations that the transports below
use to map valuations between the two sides.

`PureEqv` relates derivations of possibly different expressions only through
its constructors, which pin the correspondence themselves.  The one place
where the judgment does not pin the expression index is `ctrl`, whose
expression determines only `l.map Prod.fst`, so the `ctrl` constructor
carries that equality as a premise. -/

mutual

/-- Equivalent pure proofs: the rule-chosen decompositions (`purePair`'s
context split, `ctrl`'s four-way split) correspond componentwise up to
permutation, and every sub-derivation carries its own equivalence witness. -/
inductive PureEqv : {Γ₁ Δ₁ Γ₂ Δ₂ : Context} → {e₁ e₂ : Expression} →
    {T : DataType} → PureDerivation Γ₁ Δ₁ e₁ T → PureDerivation Γ₂ Δ₂ e₂ T →
    Type where
  | unit {Γ₁ Γ₂ : Context} {hW₁ : Context.WellFormed Γ₁}
      {hW₂ : Context.WellFormed Γ₂} (hΓ : List.Perm Γ₁ Γ₂) :
      PureEqv (.hasTypeUnit hW₁) (.hasTypeUnit hW₂)
  | cvar {Γa₁ Γb₁ Γa₂ Γb₂ : Context} {x : Variable} {T : DataType}
      {hW₁ : Context.WellFormed (Γa₁ ++ [(x, T)] ++ Γb₁)}
      {hW₂ : Context.WellFormed (Γa₂ ++ [(x, T)] ++ Γb₂)}
      (hΓ : List.Perm (Γa₁ ++ [(x, T)] ++ Γb₁) (Γa₂ ++ [(x, T)] ++ Γb₂)) :
      PureEqv (.hasTypeCVar hW₁) (.hasTypeCVar hW₂)
  | qvar {Γ₁ Γ₂ : Context} {x : Variable} {T : DataType}
      {hW₁ : Context.WellFormed Γ₁} {hW₂ : Context.WellFormed Γ₂}
      {hx₁ : x ∉ Context.dom Γ₁} {hx₂ : x ∉ Context.dom Γ₂}
      (hΓ : List.Perm Γ₁ Γ₂) :
      PureEqv (.hasTypeQVar (x := x) (T := T) hW₁ hx₁)
          (.hasTypeQVar (x := x) (T := T) hW₂ hx₂)
  | purePair {Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' : Context} {e₀ e₁ : Expression}
      {T₀ T₁ : DataType}
      {hWΓ₁ : Context.WellFormed Γ₁} {hWΓ₂ : Context.WellFormed Γ₂}
      {hWΔ₁ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
      {hWΔ₂ : Context.WellFormed (Δ' ++ Δ₀' ++ Δ₁')}
      (hΓ : List.Perm Γ₁ Γ₂) (hΔ : List.Perm Δ Δ')
      (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
      {d₀ : PureDerivation Γ₁ (Δ ++ Δ₀) e₀ T₀}
      {d₁ : PureDerivation Γ₁ (Δ ++ Δ₁) e₁ T₁}
      {d₀' : PureDerivation Γ₂ (Δ' ++ Δ₀') e₀ T₀}
      {d₁' : PureDerivation Γ₂ (Δ' ++ Δ₁') e₁ T₁}
      (r₀ : PureEqv d₀ d₀') (r₁ : PureEqv d₁ d₁') :
      PureEqv (.hasTypePurePair hWΓ₁ hWΔ₁ d₀ d₁)
          (.hasTypePurePair hWΓ₂ hWΔ₂ d₀' d₁')
  | ctrl {Γ₁ Γ₁' Δ₁ Δ₁' G₂ G₂' D₂ D₂' : Context} {e : Expression}
      {T T' : DataType} {l₁ l₂ : List ((Expression × Expression) × Context)}
      {hW₁ : Context.WellFormed (Γ₁ ++ Γ₁' ++ Δ₁ ++ Δ₁')}
      {hW₂ : Context.WellFormed (G₂ ++ G₂' ++ D₂ ++ D₂')}
      (hl : l₁.map Prod.fst = l₂.map Prod.fst)
      (hΓ : List.Perm Γ₁ G₂) (hΓ' : List.Perm Γ₁' G₂')
      (hΔ : List.Perm Δ₁ D₂) (hΔ' : List.Perm Δ₁' D₂')
      {dMix₁ : MixedDerivation (Γ₁ ++ Δ₁) e T}
      {dMix₂ : MixedDerivation (G₂ ++ D₂) e T}
      (r : MixedEqv dMix₁ dMix₂)
      {hO₁ : Ortho T (l₁.map (Prod.fst ∘ Prod.fst))}
      {hO₂ : Ortho T (l₂.map (Prod.fst ∘ Prod.fst))}
      {hE₁ : ∀ x, x ∈ Context.dom Δ₁ →
          Erases x T' (l₁.map (Prod.snd ∘ Prod.fst))}
      {hE₂ : ∀ x, x ∈ Context.dom D₂ →
          Erases x T' (l₂.map (Prod.snd ∘ Prod.fst))}
      {dB₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
      {dB₂ : BranchDerivation G₂ G₂' D₂ D₂' l₂ T T'}
      (rb : BranchEqv hΓ hΓ' hΔ hΔ' dB₁ dB₂) :
      PureEqv (.hasTypeCtrl Γ₁ Γ₁' Δ₁ Δ₁' l₁ e T T' hW₁ dMix₁ hO₁ dB₁ hE₁)
          (.hasTypeCtrl G₂ G₂' D₂ D₂' l₂ e T T' hW₂ dMix₂ hO₂ dB₂ hE₂)
  | pureApp {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e : Expression} {f : Program}
      {T T' : DataType}
      {df₁ df₂ : ProgramDerivation f (T ⇝ T')}
      {de₁ : PureDerivation Γ₁ Δ₁ e T} {de₂ : PureDerivation Γ₂ Δ₂ e T}
      (hΓ : List.Perm Γ₁ Γ₂) (hΔ : List.Perm Δ₁ Δ₂)
      (hprog : programAmplitude df₁ = programAmplitude df₂)
      (r : PureEqv de₁ de₂) :
      PureEqv (.hasTypePureApp df₁ de₁) (.hasTypePureApp df₂ de₂)
  | permL {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Δ₂ : Context} {e : Expression} {T : DataType}
      {hWΓ : Context.WellFormed Γ₁'} {hWΔ : Context.WellFormed Δ₁'}
      {d₁ : PureDerivation Γ₁ Δ₁ e T} {d₂ : PureDerivation Γ₂ Δ₂ e T}
      (hΓ : List.Perm Γ₁ Γ₁') (hΔ : List.Perm Δ₁ Δ₁')
      (r : PureEqv d₁ d₂) :
      PureEqv (.hasTypePurePerm hWΓ hWΔ d₁ hΓ hΔ) d₂
  | permR {Γ₁ Δ₁ Γ₂ Γ₂' Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
      {hWΓ : Context.WellFormed Γ₂'} {hWΔ : Context.WellFormed Δ₂'}
      {d₁ : PureDerivation Γ₁ Δ₁ e T} {d₂ : PureDerivation Γ₂ Δ₂ e T}
      (r : PureEqv d₁ d₂)
      (hΓ : List.Perm Γ₂ Γ₂') (hΔ : List.Perm Δ₂ Δ₂') :
      PureEqv d₁ (.hasTypePurePerm hWΓ hWΔ d₂ hΓ hΔ)

/-- Equivalent mixed proofs: same expression and type, with rule-chosen
context decompositions corresponding componentwise up to permutation.  The
`mix` constructor additionally records a pure equivalence between the two
pure sub-proofs. -/
inductive MixedEqv : {Δ₁ Δ₂ : Context} → {e : Expression} → {T : DataType} →
    MixedDerivation Δ₁ e T → MixedDerivation Δ₂ e T → Type where
  | mix {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
      {hW₁ : Context.WellFormed Δ₁} {hW₂ : Context.WellFormed Δ₂}
      (h : List.Perm Δ₁ Δ₂)
      (dp₁ : PureDerivation [] Δ₁ e T) (dp₂ : PureDerivation [] Δ₂ e T)
      (pq : PureEqv dp₁ dp₂) :
      MixedEqv (.hasTypeMix hW₁ dp₁) (.hasTypeMix hW₂ dp₂)
  | permL {Δ₁ Δ₁' Δ₂ : Context} {e : Expression} {T : DataType}
      {hW : Context.WellFormed Δ₁'}
      {d₁ : MixedDerivation Δ₁ e T} {d₂ : MixedDerivation Δ₂ e T}
      (h' : List.Perm Δ₁ Δ₁') (r : MixedEqv d₁ d₂) :
      MixedEqv (.hasMixedTypePerm hW d₁ h') d₂
  | permR {Δ₁ Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
      {hW : Context.WellFormed Δ₂'}
      {d₁ : MixedDerivation Δ₁ e T} {d₂ : MixedDerivation Δ₂ e T}
      (r : MixedEqv d₁ d₂) (h' : List.Perm Δ₂ Δ₂') :
      MixedEqv d₁ (.hasMixedTypePerm hW d₂ h')
  | pair {Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' : Context} {e₀ e₁ : Expression} {T₀ T₁ : DataType}
      {hW₁ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
      {hW₂ : Context.WellFormed (Δ' ++ Δ₀' ++ Δ₁')}
      (hΔ : List.Perm Δ Δ') (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
      {d₀ : MixedDerivation (Δ ++ Δ₀) e₀ T₀} {d₁ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
      {d₀' : MixedDerivation (Δ' ++ Δ₀') e₀ T₀} {d₁' : MixedDerivation (Δ' ++ Δ₁') e₁ T₁}
      (r₀ : MixedEqv d₀ d₀') (r₁ : MixedEqv d₁ d₁') :
      MixedEqv (.hasMixedTypePair hW₁ d₀ d₁) (.hasMixedTypePair hW₂ d₀' d₁')
  | mtry {Δ₀ Δ₁ Δ₀' Δ₁' : Context} {e₀ e₁ : Expression} {T : DataType}
      {hW₁ : Context.WellFormed (Δ₀ ++ Δ₁)}
      {hW₂ : Context.WellFormed (Δ₀' ++ Δ₁')}
      (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
      {d₀ : MixedDerivation Δ₀ e₀ T} {d₁ : MixedDerivation Δ₁ e₁ T}
      {d₀' : MixedDerivation Δ₀' e₀ T} {d₁' : MixedDerivation Δ₁' e₁ T}
      (r₀ : MixedEqv d₀ d₀') (r₁ : MixedEqv d₁ d₁') :
      MixedEqv (.hasTypeTry hW₁ d₀ d₁) (.hasTypeTry hW₂ d₀' d₁')
  | app {Δ Δ' : Context} {e : Expression} {f : Program} {T T' : DataType}
      {df₁ df₂ : ProgramDerivation f (T ⇛ T')}
      {de₁ : MixedDerivation Δ e T} {de₂ : MixedDerivation Δ' e T}
      (hprog : programAmplitude df₁ = programAmplitude df₂)
      (r : MixedEqv de₁ de₂) :
      MixedEqv (.hasMixedTypeApp df₁ de₁) (.hasMixedTypeApp df₂ de₂)
  /-- The cross case `T-Mix`/`T-MixedPair`: a mixed proof obtained by mixing a
  *literal* pure pair proof is equivalent to a mixed pair proof of the same
  expression, provided each pair component's mixed proof is equivalent to the
  mixture of the corresponding pure component.  The two decompositions are
  related by the recorded permutations `hΔ`, `h₀`, `h₁` (the paper's
  `𝜋₂`, `𝜋₂⁰`, `𝜋₂¹`).  The pure components are written at the literal
  pair's split, matching the `T-Pair` normal form of a pure pair proof. -/
  | mixPair {Δ Δ₀ Δ₁ Δs Δ₀s Δ₁s : Context} {e₀ e₁ : Expression}
      {T₀ T₁ : DataType}
      {hWs : Context.WellFormed ((Δs ++ Δ₀s) ++ Δ₁s)}
      {hW : Context.WellFormed ((Δ ++ Δ₀) ++ Δ₁)}
      {hW₀s : Context.WellFormed (Δs ++ Δ₀s)}
      {hW₁s : Context.WellFormed (Δs ++ Δ₁s)}
      {dp₀ : PureDerivation [] (Δs ++ Δ₀s) e₀ T₀}
      {dp₁ : PureDerivation [] (Δs ++ Δ₁s) e₁ T₁}
      (hΔ : List.Perm Δs Δ) (h₀ : List.Perm Δ₀s Δ₀) (h₁ : List.Perm Δ₁s Δ₁)
      {d₀ : MixedDerivation (Δ ++ Δ₀) e₀ T₀}
      {d₁ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
      (r₀ : MixedEqv (.hasTypeMix hW₀s dp₀) d₀)
      (r₁ : MixedEqv (.hasTypeMix hW₁s dp₁) d₁) :
      MixedEqv (.hasTypeMix hWs (.hasTypePurePair Context.WellFormed.nil hWs dp₀ dp₁))
          (.hasMixedTypePair hW d₀ d₁)
  /-- The cross case `T-Mix`/`T-MixedApp`: a mixed proof obtained by mixing a
  *literal* pure application proof is equivalent to a mixed application proof
  whose program is the channel (pure) form of the same program, provided the
  mixed argument proof is equivalent to the mixture of the pure argument. -/
  | mixApp {Δd Δ : Context} {e : Expression} {f : Program} {T T' : DataType}
      {hWd : Context.WellFormed Δd}
      {dp₀ : PureDerivation [] Δd e T}
      {df : ProgramDerivation f (T ⇝ T')}
      {de : MixedDerivation Δ e T}
      (r : MixedEqv (.hasTypeMix hWd dp₀) de) :
      MixedEqv (.hasTypeMix hWd (.hasTypePureApp df dp₀))
          (.hasMixedTypeApp (.hasTypeChannel df) de)

/-- Equivalent branch lists at corresponding (permutation-related) ctrl
decompositions.  The frame permutations are parameters: one equivalence
witness fixes the ctrl decomposition correspondence once, and every branch
shares it.  Per-branch classical contexts `Γⱼ` are free rule data, so each
`cons` carries pure equivalences for the pattern and the body at their own
contexts. -/
inductive BranchEqv :
    {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context} →
    (hΓ : List.Perm Γ₁ Γ₂) → (hΓ' : List.Perm Γ₁' Γ₂') →
    (hΔ : List.Perm Δ₁ Δ₂) → (hΔ' : List.Perm Δ₁' Δ₂') →
    {l₁ l₂ : List ((Expression × Expression) × Context)} →
    {T T' : DataType} →
    BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T' →
    BranchDerivation Γ₂ Γ₂' Δ₂ Δ₂' l₂ T T' → Type where
  | nil {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context} {T T' : DataType}
      {hΓ : List.Perm Γ₁ Γ₂} {hΓ' : List.Perm Γ₁' Γ₂'}
      {hΔ : List.Perm Δ₁ Δ₂} {hΔ' : List.Perm Δ₁' Δ₂'} :
      BranchEqv hΓ hΓ' hΔ hΔ'
        (BranchDerivation.nil Γ₁ Γ₁' Δ₁ Δ₁' T T')
        (BranchDerivation.nil Γ₂ Γ₂' Δ₂ Δ₂' T T')
  | cons {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context}
      {hΓ : List.Perm Γ₁ Γ₂} {hΓ' : List.Perm Γ₁' Γ₂'}
      {hΔ : List.Perm Δ₁ Δ₂} {hΔ' : List.Perm Δ₁' Δ₂'}
      {T T' : DataType} {Γⱼ₁ Γⱼ₂ : Context} {eⱼ eⱼ' : Expression}
      {l₁ l₂ : List ((Expression × Expression) × Context)}
      {dPat₁ : PureDerivation [] Γⱼ₁ eⱼ T}
      {dPat₂ : PureDerivation [] Γⱼ₂ eⱼ T}
      {dBody₁ : PureDerivation (Γ₁ ++ Γ₁' ++ Γⱼ₁) (Δ₁ ++ Δ₁') eⱼ' T'}
      {dBody₂ : PureDerivation (Γ₂ ++ Γ₂' ++ Γⱼ₂) (Δ₂ ++ Δ₂') eⱼ' T'}
      {b₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
      {b₂ : BranchDerivation Γ₂ Γ₂' Δ₂ Δ₂' l₂ T T'}
      (hp : PureEqv dPat₁ dPat₂) (hb : PureEqv dBody₁ dBody₂)
      (rt : BranchEqv hΓ hΓ' hΔ hΔ' b₁ b₂) :
      BranchEqv hΓ hΓ' hΔ hΔ' (BranchDerivation.cons dPat₁ dBody₁ b₁)
          (BranchDerivation.cons dPat₂ dBody₂ b₂)

end

/-- Single-motive induction principle over mixed equivalences.  The pure and
branch cases of the combined mutual recursor are discharged here once and
for all, so proofs by `induction r using MixedEqv.induct` see only the six
mixed cases, with the constructor binder shapes. -/
def MixedEqv.induct
    {motive : ∀ {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType},
      (d₁ : MixedDerivation Δ₁ e T) → (d₂ : MixedDerivation Δ₂ e T) →
      MixedEqv d₁ d₂ → Sort u}
    (hmix : ∀ {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
      {hW₁ : Context.WellFormed Δ₁} {hW₂ : Context.WellFormed Δ₂}
      (h : List.Perm Δ₁ Δ₂)
      (dp₁ : PureDerivation [] Δ₁ e T) (dp₂ : PureDerivation [] Δ₂ e T)
      (pq : PureEqv dp₁ dp₂),
      motive (.hasTypeMix hW₁ dp₁) (.hasTypeMix hW₂ dp₂) (.mix h dp₁ dp₂ pq))
    (hpermL : ∀ {Δ₁ Δ₁' Δ₂ : Context} {e : Expression} {T : DataType}
      {hW : Context.WellFormed Δ₁'}
      {d₁ : MixedDerivation Δ₁ e T} {d₂ : MixedDerivation Δ₂ e T}
      (h' : List.Perm Δ₁ Δ₁') (r : MixedEqv d₁ d₂),
      motive d₁ d₂ r →
      motive (.hasMixedTypePerm hW d₁ h') d₂ (.permL h' r))
    (hpermR : ∀ {Δ₁ Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
      {hW : Context.WellFormed Δ₂'}
      {d₁ : MixedDerivation Δ₁ e T} {d₂ : MixedDerivation Δ₂ e T}
      (r : MixedEqv d₁ d₂) (h' : List.Perm Δ₂ Δ₂'),
      motive d₁ d₂ r →
      motive d₁ (.hasMixedTypePerm hW d₂ h') (.permR r h'))
    (hpair : ∀ {Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' : Context} {e₀ e₁ : Expression}
      {T₀ T₁ : DataType}
      {hW₁ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
      {hW₂ : Context.WellFormed (Δ' ++ Δ₀' ++ Δ₁')}
      (hΔ : List.Perm Δ Δ') (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
      {d₀ : MixedDerivation (Δ ++ Δ₀) e₀ T₀} {d₁ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
      {d₀' : MixedDerivation (Δ' ++ Δ₀') e₀ T₀} {d₁' : MixedDerivation (Δ' ++ Δ₁') e₁ T₁}
      (r₀ : MixedEqv d₀ d₀') (r₁ : MixedEqv d₁ d₁'),
      motive d₀ d₀' r₀ → motive d₁ d₁' r₁ →
      motive (.hasMixedTypePair hW₁ d₀ d₁) (.hasMixedTypePair hW₂ d₀' d₁')
        (.pair hΔ h₀ h₁ r₀ r₁))
    (hmtry : ∀ {Δ₀ Δ₁ Δ₀' Δ₁' : Context} {e₀ e₁ : Expression} {T : DataType}
      {hW₁ : Context.WellFormed (Δ₀ ++ Δ₁)} {hW₂ : Context.WellFormed (Δ₀' ++ Δ₁')}
      (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
      {d₀ : MixedDerivation Δ₀ e₀ T} {d₁ : MixedDerivation Δ₁ e₁ T}
      {d₀' : MixedDerivation Δ₀' e₀ T} {d₁' : MixedDerivation Δ₁' e₁ T}
      (r₀ : MixedEqv d₀ d₀') (r₁ : MixedEqv d₁ d₁'),
      motive d₀ d₀' r₀ → motive d₁ d₁' r₁ →
      motive (.hasTypeTry hW₁ d₀ d₁) (.hasTypeTry hW₂ d₀' d₁')
        (.mtry h₀ h₁ r₀ r₁))
    (happ : ∀ {Δ Δ' : Context} {e : Expression} {f : Program} {T T' : DataType}
      {df₁ df₂ : ProgramDerivation f (T ⇛ T')}
      {de₁ : MixedDerivation Δ e T} {de₂ : MixedDerivation Δ' e T}
      (hprog : programAmplitude df₁ = programAmplitude df₂) (r : MixedEqv de₁ de₂),
      motive de₁ de₂ r →
      motive (.hasMixedTypeApp df₁ de₁) (.hasMixedTypeApp df₂ de₂) (.app hprog r))
    (hmixPair : ∀ {Δ Δ₀ Δ₁ Δs Δ₀s Δ₁s : Context} {e₀ e₁ : Expression}
      {T₀ T₁ : DataType}
      {hWs : Context.WellFormed ((Δs ++ Δ₀s) ++ Δ₁s)}
      {hW : Context.WellFormed ((Δ ++ Δ₀) ++ Δ₁)}
      {hW₀s : Context.WellFormed (Δs ++ Δ₀s)}
      {hW₁s : Context.WellFormed (Δs ++ Δ₁s)}
      {dp₀ : PureDerivation [] (Δs ++ Δ₀s) e₀ T₀}
      {dp₁ : PureDerivation [] (Δs ++ Δ₁s) e₁ T₁}
      (hΔ : List.Perm Δs Δ) (h₀ : List.Perm Δ₀s Δ₀) (h₁ : List.Perm Δ₁s Δ₁)
      {d₀ : MixedDerivation (Δ ++ Δ₀) e₀ T₀}
      {d₁ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
      (r₀ : MixedEqv (.hasTypeMix hW₀s dp₀) d₀)
      (r₁ : MixedEqv (.hasTypeMix hW₁s dp₁) d₁),
      motive (.hasTypeMix hW₀s dp₀) d₀ r₀ →
      motive (.hasTypeMix hW₁s dp₁) d₁ r₁ →
      motive (.hasTypeMix hWs
          (.hasTypePurePair Context.WellFormed.nil hWs dp₀ dp₁))
        (.hasMixedTypePair hW d₀ d₁) (.mixPair hΔ h₀ h₁ r₀ r₁))
    (hmixApp : ∀ {Δd Δ : Context} {e : Expression} {f : Program} {T T' : DataType}
      {hWd : Context.WellFormed Δd}
      {dp₀ : PureDerivation [] Δd e T}
      {df : ProgramDerivation f (T ⇝ T')}
      {de : MixedDerivation Δ e T}
      (r : MixedEqv (.hasTypeMix hWd dp₀) de),
      motive (.hasTypeMix hWd dp₀) de r →
      motive (.hasTypeMix hWd (.hasTypePureApp df dp₀))
        (.hasMixedTypeApp (.hasTypeChannel df) de) (.mixApp r)) :
    ∀ {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
      {d₁ : MixedDerivation Δ₁ e T} {d₂ : MixedDerivation Δ₂ e T}
      (r : MixedEqv d₁ d₂), motive d₁ d₂ r :=
  fun r =>
    match r with
    | .mix h dp₁ dp₂ pq => hmix h dp₁ dp₂ pq
    | .permL h' r' =>
        hpermL h' r'
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r')
    | .permR r' h' =>
        hpermR r' h'
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r')
    | .pair hΔ h₀ h₁ r₀ r₁ =>
        hpair hΔ h₀ h₁ r₀ r₁
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r₀)
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r₁)
    | .mtry h₀ h₁ r₀ r₁ =>
        hmtry h₀ h₁ r₀ r₁
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r₀)
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r₁)
    | .app hprog r' =>
        happ hprog r'
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r')
    | .mixPair hΔ h₀ h₁ r₀ r₁ =>
        hmixPair hΔ h₀ h₁ r₀ r₁
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r₀)
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r₁)
    | .mixApp r' =>
        hmixApp r'
          (MixedEqv.induct hmix hpermL hpermR hpair hmtry happ hmixPair
            hmixApp r')

/-- Single-motive induction principle over pure equivalences, analogous to
`MixedEqv.induct`: the mixed and branch cases of the combined mutual
recursor never arise when eliminating a pure witness, so proofs by
`induction r using PureEqv.induct` see only the eight pure cases with the
constructor binder shapes. -/
def PureEqv.induct
    {motive : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression} {T : DataType},
      (d₁ : PureDerivation Γ₁ Δ₁ e₁ T) → (d₂ : PureDerivation Γ₂ Δ₂ e₂ T) →
      PureEqv d₁ d₂ → Sort u}
    (hunit : ∀ {Γ₁ Γ₂ : Context} {hW₁ : Context.WellFormed Γ₁}
      {hW₂ : Context.WellFormed Γ₂} (hΓ : List.Perm Γ₁ Γ₂),
      motive (.hasTypeUnit hW₁) (.hasTypeUnit hW₂) (.unit hΓ))
    (hcvar : ∀ {Γa₁ Γb₁ Γa₂ Γb₂ : Context} {x : Variable} {T : DataType}
      {hW₁ : Context.WellFormed (Γa₁ ++ [(x, T)] ++ Γb₁)}
      {hW₂ : Context.WellFormed (Γa₂ ++ [(x, T)] ++ Γb₂)}
      (hΓ : List.Perm (Γa₁ ++ [(x, T)] ++ Γb₁) (Γa₂ ++ [(x, T)] ++ Γb₂)),
      motive (.hasTypeCVar hW₁) (.hasTypeCVar hW₂) (.cvar hΓ))
    (hqvar : ∀ {Γ₁ Γ₂ : Context} {x : Variable} {T : DataType}
      {hW₁ : Context.WellFormed Γ₁} {hW₂ : Context.WellFormed Γ₂}
      {hx₁ : x ∉ Context.dom Γ₁} {hx₂ : x ∉ Context.dom Γ₂}
      (hΓ : List.Perm Γ₁ Γ₂),
      motive (.hasTypeQVar (x := x) (T := T) hW₁ hx₁)
          (.hasTypeQVar (x := x) (T := T) hW₂ hx₂) (.qvar hΓ))
    (hpurePair : ∀ {Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' : Context} {e₀ e₁ : Expression}
      {T₀ T₁ : DataType}
      {hWΓ₁ : Context.WellFormed Γ₁} {hWΓ₂ : Context.WellFormed Γ₂}
      {hWΔ₁ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
      {hWΔ₂ : Context.WellFormed (Δ' ++ Δ₀' ++ Δ₁')}
      (hΓ : List.Perm Γ₁ Γ₂) (hΔ : List.Perm Δ Δ')
      (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
      {d₀ : PureDerivation Γ₁ (Δ ++ Δ₀) e₀ T₀}
      {d₁ : PureDerivation Γ₁ (Δ ++ Δ₁) e₁ T₁}
      {d₀' : PureDerivation Γ₂ (Δ' ++ Δ₀') e₀ T₀}
      {d₁' : PureDerivation Γ₂ (Δ' ++ Δ₁') e₁ T₁}
      (r₀ : PureEqv d₀ d₀') (r₁ : PureEqv d₁ d₁'),
      motive d₀ d₀' r₀ → motive d₁ d₁' r₁ →
      motive (.hasTypePurePair hWΓ₁ hWΔ₁ d₀ d₁)
          (.hasTypePurePair hWΓ₂ hWΔ₂ d₀' d₁')
        (.purePair hΓ hΔ h₀ h₁ r₀ r₁))
    (hctrl : ∀ {Γ₁ Γ₁' Δ₁ Δ₁' G₂ G₂' D₂ D₂' : Context} {e : Expression}
      {T T' : DataType} {l₁ l₂ : List ((Expression × Expression) × Context)}
      {hW₁ : Context.WellFormed (Γ₁ ++ Γ₁' ++ Δ₁ ++ Δ₁')}
      {hW₂ : Context.WellFormed (G₂ ++ G₂' ++ D₂ ++ D₂')}
      (hl : l₁.map Prod.fst = l₂.map Prod.fst)
      (hΓ : List.Perm Γ₁ G₂) (hΓ' : List.Perm Γ₁' G₂')
      (hΔ : List.Perm Δ₁ D₂) (hΔ' : List.Perm Δ₁' D₂')
      {dMix₁ : MixedDerivation (Γ₁ ++ Δ₁) e T}
      {dMix₂ : MixedDerivation (G₂ ++ D₂) e T}
      (r : MixedEqv dMix₁ dMix₂)
      {hO₁ : Ortho T (l₁.map (Prod.fst ∘ Prod.fst))}
      {hO₂ : Ortho T (l₂.map (Prod.fst ∘ Prod.fst))}
      {hE₁ : ∀ x, x ∈ Context.dom Δ₁ →
          Erases x T' (l₁.map (Prod.snd ∘ Prod.fst))}
      {hE₂ : ∀ x, x ∈ Context.dom D₂ →
          Erases x T' (l₂.map (Prod.snd ∘ Prod.fst))}
      {dB₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
      {dB₂ : BranchDerivation G₂ G₂' D₂ D₂' l₂ T T'}
      (rb : BranchEqv hΓ hΓ' hΔ hΔ' dB₁ dB₂),
      motive (.hasTypeCtrl Γ₁ Γ₁' Δ₁ Δ₁' l₁ e T T' hW₁ dMix₁ hO₁ dB₁ hE₁)
          (.hasTypeCtrl G₂ G₂' D₂ D₂' l₂ e T T' hW₂ dMix₂ hO₂ dB₂ hE₂)
        (.ctrl hl hΓ hΓ' hΔ hΔ' r rb))
    (hpureApp : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e : Expression} {f : Program}
      {T T' : DataType}
      {df₁ df₂ : ProgramDerivation f (T ⇝ T')}
      {de₁ : PureDerivation Γ₁ Δ₁ e T} {de₂ : PureDerivation Γ₂ Δ₂ e T}
      (hΓ : List.Perm Γ₁ Γ₂) (hΔ : List.Perm Δ₁ Δ₂)
      (hprog : programAmplitude df₁ = programAmplitude df₂)
      (r : PureEqv de₁ de₂), motive de₁ de₂ r →
      motive (.hasTypePureApp df₁ de₁) (.hasTypePureApp df₂ de₂)
        (.pureApp hΓ hΔ hprog r))
    (hpermL : ∀ {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Δ₂ : Context} {e : Expression}
      {T : DataType}
      {hWΓ : Context.WellFormed Γ₁'} {hWΔ : Context.WellFormed Δ₁'}
      {d₁ : PureDerivation Γ₁ Δ₁ e T} {d₂ : PureDerivation Γ₂ Δ₂ e T}
      (hΓ : List.Perm Γ₁ Γ₁') (hΔ : List.Perm Δ₁ Δ₁') (r : PureEqv d₁ d₂),
      motive d₁ d₂ r →
      motive (.hasTypePurePerm hWΓ hWΔ d₁ hΓ hΔ) d₂ (.permL hΓ hΔ r))
    (hpermR : ∀ {Γ₁ Δ₁ Γ₂ Γ₂' Δ₂ Δ₂' : Context} {e : Expression}
      {T : DataType}
      {hWΓ : Context.WellFormed Γ₂'} {hWΔ : Context.WellFormed Δ₂'}
      {d₁ : PureDerivation Γ₁ Δ₁ e T} {d₂ : PureDerivation Γ₂ Δ₂ e T}
      (r : PureEqv d₁ d₂) (hΓ : List.Perm Γ₂ Γ₂') (hΔ : List.Perm Δ₂ Δ₂'),
      motive d₁ d₂ r →
      motive d₁ (.hasTypePurePerm hWΓ hWΔ d₂ hΓ hΔ) (.permR r hΓ hΔ)) :
    ∀ {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression} {T : DataType}
      {d₁ : PureDerivation Γ₁ Δ₁ e₁ T} {d₂ : PureDerivation Γ₂ Δ₂ e₂ T}
      (r : PureEqv d₁ d₂), motive d₁ d₂ r :=
  fun r =>
    match r with
    | .unit hΓ => hunit hΓ
    | .cvar hΓ => hcvar hΓ
    | .qvar hΓ => hqvar hΓ
    | .purePair hΓ hΔ h₀ h₁ r₀ r₁ =>
        hpurePair hΓ hΔ h₀ h₁ r₀ r₁
          (PureEqv.induct hunit hcvar hqvar hpurePair hctrl hpureApp hpermL
            hpermR r₀)
          (PureEqv.induct hunit hcvar hqvar hpurePair hctrl hpureApp hpermL
            hpermR r₁)
    | .ctrl hl hΓ hΓ' hΔ hΔ' r rb => hctrl hl hΓ hΓ' hΔ hΔ' r rb
    | .pureApp hΓ hΔ hprog r =>
        hpureApp hΓ hΔ hprog r
          (PureEqv.induct hunit hcvar hqvar hpurePair hctrl hpureApp hpermL
            hpermR r)
    | .permL hΓ hΔ r =>
        hpermL hΓ hΔ r
          (PureEqv.induct hunit hcvar hqvar hpurePair hctrl hpureApp hpermL
            hpermR r)
    | .permR r hΓ hΔ =>
        hpermR r hΓ hΔ
          (PureEqv.induct hunit hcvar hqvar hpurePair hctrl hpureApp hpermL
            hpermR r)

/-- Single-motive induction principle over branch equivalences. -/
lemma BranchEqv.induct
    {motive : ∀ {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context},
      (hΓ : List.Perm Γ₁ Γ₂) → (hΓ' : List.Perm Γ₁' Γ₂') →
      (hΔ : List.Perm Δ₁ Δ₂) → (hΔ' : List.Perm Δ₁' Δ₂') →
      {l₁ l₂ : List ((Expression × Expression) × Context)} →
      {T T' : DataType} →
      (b₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T') →
      (b₂ : BranchDerivation Γ₂ Γ₂' Δ₂ Δ₂' l₂ T T') →
      BranchEqv hΓ hΓ' hΔ hΔ' b₁ b₂ → Prop}
    (hnil : ∀ {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context} {T T' : DataType}
      {hΓ : List.Perm Γ₁ Γ₂} {hΓ' : List.Perm Γ₁' Γ₂'}
      {hΔ : List.Perm Δ₁ Δ₂} {hΔ' : List.Perm Δ₁' Δ₂'},
      motive hΓ hΓ' hΔ hΔ' (BranchDerivation.nil Γ₁ Γ₁' Δ₁ Δ₁' T T')
          (BranchDerivation.nil Γ₂ Γ₂' Δ₂ Δ₂' T T') BranchEqv.nil)
    (hcons : ∀ {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context}
      {hΓ : List.Perm Γ₁ Γ₂} {hΓ' : List.Perm Γ₁' Γ₂'}
      {hΔ : List.Perm Δ₁ Δ₂} {hΔ' : List.Perm Δ₁' Δ₂'}
      {T T' : DataType} {Γⱼ₁ Γⱼ₂ : Context} {eⱼ eⱼ' : Expression}
      {l₁ l₂ : List ((Expression × Expression) × Context)}
      {dPat₁ : PureDerivation [] Γⱼ₁ eⱼ T} {dPat₂ : PureDerivation [] Γⱼ₂ eⱼ T}
      {dBody₁ : PureDerivation (Γ₁ ++ Γ₁' ++ Γⱼ₁) (Δ₁ ++ Δ₁') eⱼ' T'}
      {dBody₂ : PureDerivation (Γ₂ ++ Γ₂' ++ Γⱼ₂) (Δ₂ ++ Δ₂') eⱼ' T'}
      {b₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
      {b₂ : BranchDerivation Γ₂ Γ₂' Δ₂ Δ₂' l₂ T T'}
      (hp : PureEqv dPat₁ dPat₂) (hb : PureEqv dBody₁ dBody₂)
      (rt : BranchEqv hΓ hΓ' hΔ hΔ' b₁ b₂),
      motive hΓ hΓ' hΔ hΔ' b₁ b₂ rt →
      motive hΓ hΓ' hΔ hΔ'
          (BranchDerivation.cons dPat₁ dBody₁ b₁)
          (BranchDerivation.cons dPat₂ dBody₂ b₂) (.cons hp hb rt)) :
    ∀ {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context}
      {hΓ : List.Perm Γ₁ Γ₂} {hΓ' : List.Perm Γ₁' Γ₂'}
      {hΔ : List.Perm Δ₁ Δ₂} {hΔ' : List.Perm Δ₁' Δ₂'}
      {l₁ l₂ : List ((Expression × Expression) × Context)} {T T' : DataType}
      {b₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
      {b₂ : BranchDerivation Γ₂ Γ₂' Δ₂ Δ₂' l₂ T T'}
      (rb : BranchEqv hΓ hΓ' hΔ hΔ' b₁ b₂),
      motive hΓ hΓ' hΔ hΔ' b₁ b₂ rb :=
  fun rb =>
    match rb with
    | .nil .. => hnil
    | .cons hp hb rt =>
        hcons hp hb rt (BranchEqv.induct hnil hcons rt)

/-- Transport a valuation from the first proof's context to the second's,
along the componentwise permutations carried by the equivalence. -/
def MixedEqv.transport {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    {d₁ : MixedDerivation Δ₁ e T} {d₂ : MixedDerivation Δ₂ e T}
    (r : MixedEqv d₁ d₂) : Valuation Δ₁ → Valuation Δ₂ :=
  match r with
  | .mix h _ _ _ => fun τ => τ.reorder h.symm
  | .permL h' r' => fun τ => r'.transport (τ.reorder h')
  | .permR r' h' => fun τ => (r'.transport τ).reorder h'.symm
  | .pair hΔ h₀ h₁ _ _ => fun τ =>
      (((Valuation.split (Γ := _) (Δ := _)
          (Valuation.split (Γ := _) (Δ := _) τ).1).1.reorder hΔ.symm).append
        ((Valuation.split (Γ := _) (Δ := _)
            (Valuation.split (Γ := _) (Δ := _) τ).1).2.reorder h₀.symm)).append
          ((Valuation.split (Γ := _) (Δ := _) τ).2.reorder h₁.symm)
  | .mtry _ _ r₀' r₁' => fun τ =>
      (r₀'.transport (Valuation.split (Γ := _) (Δ := _) τ).1).append
        (r₁'.transport (Valuation.split (Γ := _) (Δ := _) τ).2)
  | .app _ r' => fun τ => r'.transport τ
  | .mixPair hΔ h₀ h₁ _ _ => fun τ =>
      (((Valuation.split (Γ := _) (Δ := _)
          (Valuation.split (Γ := _) (Δ := _) τ).1).1.reorder hΔ.symm).append
        ((Valuation.split (Γ := _) (Δ := _)
            (Valuation.split (Γ := _) (Δ := _) τ).1).2.reorder h₀.symm)).append
          ((Valuation.split (Γ := _) (Δ := _) τ).2.reorder h₁.symm)
  | .mixApp r' => fun τ => r'.transport τ

/-- Transport along a `try` equivalence is assembled from the sub-relations'
own transports, so the sub-amplitude agreements apply componentwise, and the
reassembled valuation splits back into the transported components. -/
theorem MixedEqv.transport_mtry_split
    {Δ₀ Δ₁ Δ₀' Δ₁' : Context} {e₀ e₁ : Expression} {T : DataType}
    {hW₁ : Context.WellFormed (Δ₀ ++ Δ₁)} {hW₂ : Context.WellFormed (Δ₀' ++ Δ₁')}
    (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
    {d₀ : MixedDerivation Δ₀ e₀ T} {d₁ : MixedDerivation Δ₁ e₁ T}
    {d₀' : MixedDerivation Δ₀' e₀ T} {d₁' : MixedDerivation Δ₁' e₁ T}
    (r₀ : MixedEqv d₀ d₀') (r₁ : MixedEqv d₁ d₁')
    (τ : Valuation (Δ₀ ++ Δ₁)) :
    (MixedEqv.transport
        (((.mtry h₀ h₁ r₀ r₁) :
          MixedEqv (.hasTypeTry hW₁ d₀ d₁) (.hasTypeTry hW₂ d₀' d₁'))) τ).split
      = (r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1,
         r₁.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).2) := by
  have h : MixedEqv.transport
      (((.mtry h₀ h₁ r₀ r₁) :
        MixedEqv (.hasTypeTry hW₁ d₀ d₁) (.hasTypeTry hW₂ d₀' d₁'))) τ
      = (r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1).append
        (r₁.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).2) := rfl
  rw [h, Valuation.split_append]

/-- Transport along an equivalence is injective (on duplicate-free contexts):
this is what makes each side's `try` trace tests correspond. -/
theorem MixedEqv.transport_inj {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    {d₁ : MixedDerivation Δ₁ e T} {d₂ : MixedDerivation Δ₂ e T}
    (r : MixedEqv d₁ d₂) :
    ∀ (_ : Δ₁.Nodup) (_ : Δ₂.Nodup) ⦃σ σ' : Valuation Δ₁⦄,
      r.transport σ = r.transport σ' → σ = σ' := by
  induction r using MixedEqv.induct with
  | hmix h _ _ _ =>
      intro hnd₁ _ σ σ' heq
      exact Valuation.reorder_inj h hnd₁ heq
  | @hpermL Δᵢ Δ₁' Δ₂ ei Ti hW dᵢ d₂ᵢ h' r' ih =>
      intro hnd₁ hnd₂ σ σ' heq
      have hndᵢ : List.Nodup Δᵢ := h'.nodup_iff.mpr hnd₁
      exact Valuation.reorder_inj h'.symm hnd₁ (ih hndᵢ hnd₂ heq)
  | @hpermR Δᵢ Δ₂ᵢ Δ₂' ei Ti hW dᵢ d₂ᵢ r' h' ih =>
      intro hnd₁ hnd₂ σ σ' heq
      have hndᵢ : List.Nodup Δ₂ᵢ := h'.nodup_iff.mpr hnd₂
      simp only [MixedEqv.transport] at heq
      exact ih hnd₁ hndᵢ (Valuation.reorder_inj h' hndᵢ heq)
  | @hpair Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' e₀ e₁ T₀ T₁ hW₁ hW₂ hΔ h₀ h₁ d₀ d₁ d₀' d₁' r₀ r₁ _ _ =>
      intro hnd₁ hnd₂ σ σ' heq
      have hndΔ : List.Nodup Δ :=
        List.Nodup.of_append_left (List.Nodup.of_append_left hnd₁)
      have hndΔ₀ : List.Nodup Δ₀ :=
        List.Nodup.of_append_right (List.Nodup.of_append_left hnd₁)
      have hndΔ₁ : List.Nodup Δ₁ := List.Nodup.of_append_right hnd₁
      have ho := congrArg (Valuation.split (Γ := Δ' ++ Δ₀') (Δ := Δ₁')) heq
      simp only [MixedEqv.transport] at ho
      rw [Valuation.split_append, Valuation.split_append] at ho
      have h1 := congrArg Prod.fst ho
      have h2 := congrArg Prod.snd ho
      have h1' := congrArg (Valuation.split (Γ := Δ') (Δ := Δ₀')) h1
      rw [Valuation.split_append, Valuation.split_append] at h1'
      have hΔeq := Valuation.reorder_inj hΔ hndΔ (congrArg Prod.fst h1')
      have hΔ₀eq := Valuation.reorder_inj h₀ hndΔ₀ (congrArg Prod.snd h1')
      have hΔ₁eq := Valuation.reorder_inj h₁ hndΔ₁ h2
      rw [Valuation.split_append_inv (Δ ++ Δ₀) Δ₁ σ,
        Valuation.split_append_inv (Δ ++ Δ₀) Δ₁ σ',
        Valuation.split_append_inv Δ Δ₀
          (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) σ).1,
        Valuation.split_append_inv Δ Δ₀
          (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) σ').1,
        hΔeq, hΔ₀eq, hΔ₁eq]
  | @hmtry Δ₀ Δ₁ Δ₀' Δ₁' e₀ e₁ Ti hW₁ hW₂ h₀ h₁ d₀ d₁ d₀' d₁' r₀ r₁ ih₀ ih₁ =>
      intro hnd₁ hnd₂ σ σ' heq
      have h := congrArg (Valuation.split (Γ := Δ₀') (Δ := Δ₁')) heq
      simp only [MixedEqv.transport] at h
      rw [Valuation.split_append, Valuation.split_append] at h
      have e₀ := ih₀ (List.Nodup.of_append_left hnd₁)
        (List.Nodup.of_append_left hnd₂) (congrArg Prod.fst h)
      have e₁ := ih₁ (List.Nodup.of_append_right hnd₁)
        (List.Nodup.of_append_right hnd₂) (congrArg Prod.snd h)
      rw [Valuation.split_append_inv Δ₀ Δ₁ σ,
        Valuation.split_append_inv Δ₀ Δ₁ σ', e₀, e₁]
  | happ _ r' ih =>
      intro hnd₁ hnd₂ σ σ' heq
      exact ih hnd₁ hnd₂ heq
  | @hmixPair Δ Δ₀ Δ₁ Δs Δ₀s Δ₁s e₀ e₁ T₀ T₁ hWs hW hW₀s hW₁s dp₀ dp₁
      hΔ h₀ h₁ d₀ d₁ r₀ r₁ _ _ =>
      intro hnd₁ hnd₂ σ σ' heq
      have hndΔs : List.Nodup Δs :=
        List.Nodup.of_append_left (List.Nodup.of_append_left hnd₁)
      have hndΔ₀s : List.Nodup Δ₀s :=
        List.Nodup.of_append_right (List.Nodup.of_append_left hnd₁)
      have hndΔ₁s : List.Nodup Δ₁s := List.Nodup.of_append_right hnd₁
      have ho := congrArg (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁)) heq
      simp only [MixedEqv.transport] at ho
      rw [Valuation.split_append, Valuation.split_append] at ho
      have h1 := congrArg Prod.fst ho
      have h2 := congrArg Prod.snd ho
      have h1' := congrArg (Valuation.split (Γ := Δ) (Δ := Δ₀)) h1
      rw [Valuation.split_append, Valuation.split_append] at h1'
      have hΔeq := Valuation.reorder_inj hΔ hndΔs (congrArg Prod.fst h1')
      have h₀eq := Valuation.reorder_inj h₀ hndΔ₀s (congrArg Prod.snd h1')
      have h₁eq := Valuation.reorder_inj h₁ hndΔ₁s h2
      rw [Valuation.split_append_inv (Δs ++ Δ₀s) Δ₁s σ,
        Valuation.split_append_inv (Δs ++ Δ₀s) Δ₁s σ',
        Valuation.split_append_inv Δs Δ₀s
          (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) σ).1,
        Valuation.split_append_inv Δs Δ₀s
          (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) σ').1,
        hΔeq, h₀eq, h₁eq]
  | @hmixApp Δd Δ e f T T' hWd dp₀ df de r ih =>
      intro hnd₁ hnd₂ σ σ' heq
      exact ih hnd₁ hnd₂ heq

def PureEqv.transport {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression}
    {T : DataType}
    {d₁ : PureDerivation Γ₁ Δ₁ e₁ T} {d₂ : PureDerivation Γ₂ Δ₂ e₂ T}
    (r : PureEqv d₁ d₂) :
    Valuation Γ₁ → Valuation Δ₁ → Valuation Γ₂ × Valuation Δ₂ :=
  match r with
  | .unit hΓ => fun σ τ => (σ.reorder hΓ.symm, τ)
  | .cvar hΓ => fun σ τ => (σ.reorder hΓ.symm, τ)
  | .qvar hΓ => fun σ τ => (σ.reorder hΓ.symm, τ)
  | @purePair _ _ Δ Δ₀ Δ₁ _ _ _ _ _ _ _ _ _ _ _ hΓ hΔ h₀ h₁ _ _ _ _ _ _ =>
      fun σ τ =>
        let p := Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ
        let q := p.1.split (Γ := Δ) (Δ := Δ₀)
        (σ.reorder hΓ.symm,
          (q.1.reorder hΔ.symm).append (q.2.reorder h₀.symm) |>.append
            (p.2.reorder h₁.symm))
  | .ctrl _ hΓ hΓ' hΔ hΔ' _ _ =>
      fun σ τ =>
        (σ.reorder (hΓ.append hΓ').symm, τ.reorder (hΔ.append hΔ').symm)
  | .pureApp hΓ hΔ _ _ => fun σ τ => (σ.reorder hΓ.symm, τ.reorder hΔ.symm)
  | .permL hΓ hΔ r => fun σ τ => r.transport (σ.reorder hΓ) (τ.reorder hΔ)
  | .permR r hΓ hΔ =>
      fun σ τ =>
        ((r.transport σ τ).1.reorder hΓ.symm,
          (r.transport σ τ).2.reorder hΔ.symm)

/-- The classical-frame permutation recorded by a pure equivalence. -/
lemma PureEqv.σPerm {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression}
    {T : DataType}
    {d₁ : PureDerivation Γ₁ Δ₁ e₁ T} {d₂ : PureDerivation Γ₂ Δ₂ e₂ T}
    (r : PureEqv d₁ d₂) : List.Perm Γ₁ Γ₂ :=
  match r with
  | .unit hΓ => hΓ
  | .cvar hΓ => hΓ
  | .qvar hΓ => hΓ
  | @purePair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΓ _ _ _ _ _ _ _ _ _ => hΓ
  | .ctrl _ hΓ hΓ' _ _ _ _ => hΓ.append hΓ'
  | .pureApp hΓ _ _ _ => hΓ
  | .permL hΓ hΔ r => hΓ.symm.trans (PureEqv.σPerm r)
  | .permR r hΓ hΔ => (PureEqv.σPerm r).trans hΓ

/-- The quantum-frame permutation recorded by a pure equivalence. -/
lemma PureEqv.τPerm {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression}
    {T : DataType}
    {d₁ : PureDerivation Γ₁ Δ₁ e₁ T} {d₂ : PureDerivation Γ₂ Δ₂ e₂ T}
    (r : PureEqv d₁ d₂) : List.Perm Δ₁ Δ₂ :=
  match r with
  | .unit .. => List.Perm.refl _
  | .cvar .. => List.Perm.refl _
  | .qvar .. => List.Perm.refl _
  | @purePair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΔ h₀ h₁ _ _ _ _ _ _ =>
      (hΔ.append h₀).append h₁
  | .ctrl _ _ _ hΔ hΔ' _ _ => hΔ.append hΔ'
  | .pureApp _ hΔ _ _ => hΔ
  | .permL hΓ hΔ r => hΔ.symm.trans (PureEqv.τPerm r)
  | .permR r hΓ hΔ => (PureEqv.τPerm r).trans hΔ

/-- Transport valuations along a branch equivalence: both frames are
reordered along the recorded permutations.  The transport only depends on
the frames, so no recursion on the witness is needed. -/
def BranchEqv.transport {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context}
    (hΓ : List.Perm Γ₁ Γ₂) (hΓ' : List.Perm Γ₁' Γ₂')
    (hΔ : List.Perm Δ₁ Δ₂) (hΔ' : List.Perm Δ₁' Δ₂')
    : Valuation (Γ₁ ++ Γ₁') → Valuation (Δ₁ ++ Δ₁') →
    Valuation (Γ₂ ++ Γ₂') × Valuation (Δ₂ ++ Δ₂') :=
  fun σ τ => (σ.reorder (hΓ.append hΓ').symm, τ.reorder (hΔ.append hΔ').symm)

/-! ## Paper-faithful mixed uniqueness

Definition G.2 of the paper compares *equivalent proofs*: two proofs of the
same mixed judgment in which every context decomposition chosen by a rule is
recorded, so that the two proofs use corresponding decompositions up to
permutation.  `MixedEqv` is that relation; `MixedEqv.Shared` carries the pair
rule's compatibility condition (its two sub-relations must transport the
*shared* part of the decomposition identically — the analogue of the paper
recording the decomposition in the judgment); `MixedUnique` is the
uniqueness statement itself, and `mixedUnique_step` its successor step. -/

/-- Reordering along the reflexivity permutation is the identity (on
duplicate-free contexts). -/
theorem Valuation.reorder_refl {Γ : Context} (hnd : Γ.Nodup) :
    ∀ (τ : Valuation Γ), τ.reorder (List.Perm.refl Γ).symm = τ := by
  intro τ
  apply Valuation.ext hnd
  intro x S hx
  rw [Valuation.lookup_reorder (h := (List.Perm.refl Γ).symm) (σ := τ) hx hx]

/-- Reassembling the reordered split parts equals the whole-frame reorder:
the commutation between `Valuation.split` and `Valuation.reorder` that the
pure transport needs for its `purePair` case. -/
theorem Valuation.split_reorder_append {Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' : Context}
    (hΔ : List.Perm Δ Δ') (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
    (hW : Context.WellFormed ((Δ ++ Δ₀) ++ Δ₁)) :
    ∀ τ : Valuation ((Δ ++ Δ₀) ++ Δ₁),
      ((((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split (Γ := Δ) (Δ := Δ₀)).1.reorder hΔ.symm).append (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split (Γ := Δ) (Δ := Δ₀)).2.reorder h₀.symm)).append ((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2.reorder h₁.symm)
      = τ.reorder ((hΔ.append h₀).append h₁).symm := by
  intro τ
  have hnd := hW.nodup
  have hndΔ : Δ.Nodup := List.Nodup.of_append_left (List.Nodup.of_append_left hnd)
  have hndΔ₀ : Δ₀.Nodup :=
    List.Nodup.of_append_right (List.Nodup.of_append_left hnd)
  have hndΔ₁ : Δ₁.Nodup := List.Nodup.of_append_right hnd
  have hndΔ' : Δ'.Nodup := hΔ.nodup_iff.mp hndΔ
  have hndΔ₀' : Δ₀'.Nodup := h₀.nodup_iff.mp hndΔ₀
  have hndΔ₁' : Δ₁'.Nodup := h₁.nodup_iff.mp hndΔ₁
  have hdisjΔΔ₀ : List.Disjoint Δ Δ₀ :=
    (List.nodup_append'.mp (List.Nodup.of_append_left hnd)).2.2
  have hdisjFull : List.Disjoint (Δ ++ Δ₀) Δ₁ :=
    (List.nodup_append'.mp hnd).2.2
  have hdisjΔ'Δ₀' : List.Disjoint Δ' Δ₀' := by
    intro _ hmem' hmem₀'
    exact hdisjΔΔ₀ (hΔ.mem_iff.mpr hmem') (h₀.mem_iff.mpr hmem₀')
  have hdisjQ : List.Disjoint (Δ' ++ Δ₀') Δ₁' := by
    intro _ hmem hmem₁'
    refine hdisjFull ?_ (h₁.mem_iff.mpr hmem₁')
    rcases List.mem_append.mp hmem with hΔ' | h₀'
    · exact List.mem_append_left _ (hΔ.mem_iff.mpr hΔ')
    · exact List.mem_append_right _ (h₀.mem_iff.mpr h₀')
  have hndQ : (Δ' ++ Δ₀').Nodup :=
    List.nodup_append'.mpr ⟨hndΔ', hndΔ₀', hdisjΔ'Δ₀'⟩
  have hndT : ((Δ' ++ Δ₀') ++ Δ₁').Nodup :=
    List.nodup_append'.mpr ⟨hndQ, hndΔ₁', hdisjQ⟩
  apply Valuation.ext hndT
  intro x S hx
  rcases List.mem_append.mp hx with hL | hC
  · rcases List.mem_append.mp hL with hΔ' | h₀'
    · rw [Valuation.lookup_append_left _ _
          (List.mem_append_left Δ₀' hΔ'),
        Valuation.lookup_append_left _ _ hΔ',
        Valuation.lookup_reorder (h := hΔ.symm) _ hΔ'
          (hΔ.mem_iff.mpr hΔ'),
        Valuation.lookup_split_left _ (hΔ.mem_iff.mpr hΔ'),
        Valuation.lookup_split_left _
          (List.mem_append_left Δ₀ (hΔ.mem_iff.mpr hΔ')),
        Valuation.lookup_reorder (h := ((hΔ.append h₀).append h₁).symm) _ hx
          (((hΔ.append h₀).append h₁).symm.mem_iff.mp hx)]
    · rw [Valuation.lookup_append_left _ _
          (List.mem_append_right Δ' h₀'),
        Valuation.lookup_append_right _ _ h₀'
          (List.Disjoint.symm hdisjΔ'Δ₀' h₀'),
        Valuation.lookup_reorder (h := h₀.symm) _ h₀'
          (h₀.mem_iff.mpr h₀'),
        Valuation.lookup_split_right _ (h₀.mem_iff.mpr h₀')
          (fun hmem => hdisjΔΔ₀ hmem (h₀.mem_iff.mpr h₀')),
        Valuation.lookup_split_left _
          (List.mem_append_right Δ (h₀.mem_iff.mpr h₀')),
        Valuation.lookup_reorder (h := ((hΔ.append h₀).append h₁).symm) _ hx
          (((hΔ.append h₀).append h₁).symm.mem_iff.mp hx)]
  · rw [Valuation.lookup_append_right _ _ hC
        (fun hmem => hdisjQ hmem hC),
      Valuation.lookup_reorder (h := h₁.symm) _ hC
        (h₁.mem_iff.mpr hC),
      Valuation.lookup_split_right _ (h₁.mem_iff.mpr hC)
        (fun hmem => hdisjFull hmem (h₁.mem_iff.mpr hC)),
      Valuation.lookup_reorder (h := ((hΔ.append h₀).append h₁).symm) _ hx
        (((hΔ.append h₀).append h₁).symm.mem_iff.mp hx)]

/-- The pure transport is exactly the frame reorder recorded by the
accessors.  This is what lets the branch uniqueness step reindex its
per-branch classical-context sums along `hp.τPerm`. -/
theorem PureEqv.transport_eq {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression}
    {T : DataType}
    {d₁ : PureDerivation Γ₁ Δ₁ e₁ T} {d₂ : PureDerivation Γ₂ Δ₂ e₂ T}
    (r : PureEqv d₁ d₂) :
    ∀ (σ : Valuation Γ₁) (τ : Valuation Δ₁),
      r.transport σ τ = (σ.reorder (r.σPerm).symm, τ.reorder (r.τPerm).symm) := by
  induction r using PureEqv.induct with
  | @hunit Γ₁ Γ₂ hW₁ hW₂ hΓ =>
      intro σ τ
      have hτ : τ.reorder (List.Perm.refl _).symm = τ :=
        Valuation.reorder_refl (by simp) τ
      simp only [PureEqv.transport]
      rw [hτ]
  | @hcvar Γa₁ Γb₁ Γa₂ Γb₂ x T hW₁ hW₂ hΓ =>
      intro σ τ
      have hτ : τ.reorder (List.Perm.refl _).symm = τ :=
        Valuation.reorder_refl (by simp) τ
      simp only [PureEqv.transport]
      rw [hτ]
  | @hqvar Γ₁ Γ₂ x T hW₁ hW₂ hx₁ hx₂ hΓ =>
      intro σ τ
      have hτ : τ.reorder (List.Perm.refl _).symm = τ :=
        Valuation.reorder_refl (by simp) τ
      simp only [PureEqv.transport]
      rw [hτ]
  | @hpurePair Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' e₀ e₁ T₀ T₁ hWΓ₁ hWΓ₂ hWΔ₁ hWΔ₂ hΓ hΔ
      h₀ h₁ d₀ d₁ d₀' d₁' r₀ r₁ ih₀ ih₁ =>
      intro σ τ
      have hndT : ((Δ' ++ Δ₀') ++ Δ₁').Nodup := hWΔ₂.nodup
      -- the reassembled parts equal the whole-frame reorder
      have key := Valuation.split_reorder_append hΔ h₀ h₁ hWΔ₁ τ
      simp only [PureEqv.transport]
      rw [key]
  | @hctrl Γ₁ Γ₁' Δ₁ Δ₁' G₂ G₂' D₂ D₂' e T T' l₁ l₂ hW₁ hW₂ hl hΓ hΓ' hΔ hΔ'
      dMix₁ dMix₂ r hO₁ hO₂ hE₁ hE₂ dB₁ dB₂ rb =>
      intro σ τ
      simp only [PureEqv.transport]
  | @hpureApp Γ₁ Δ₁ Γ₂ Δ₂ e f T T' df₁ df₂ de₁ de₂ hΓ hΔ hprog r ih =>
      intro σ τ
      simp only [PureEqv.transport]
  | @hpermL Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Δ₂ e T hWΓ hWΔ d₁ d₂ hΓ hΔ r ih =>
      intro σ τ
      have hndΓ₂ : Γ₂.Nodup :=
        List.Nodup.of_append_left
          (HasPureType.context_well_formed d₂.toProp).nodup
      have hndΔ₂ : Δ₂.Nodup :=
        List.Nodup.of_append_right
          (HasPureType.context_well_formed d₂.toProp).nodup
      have hxΓ : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γ₂ →
          (x, S) ∈ Γ₁ := fun _ _ hx => (PureEqv.σPerm r).mem_iff.mpr hx
      have hxΔ : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ₂ →
          (x, S) ∈ Δ₁ := fun _ _ hx => (PureEqv.τPerm r).mem_iff.mpr hx
      simp only [PureEqv.transport]
      rw [ih (σ.reorder hΓ) (τ.reorder hΔ)]
      have hσ : (σ.reorder hΓ).reorder (PureEqv.σPerm r).symm
          = σ.reorder (hΓ.symm.trans (PureEqv.σPerm r)).symm := by
        apply Valuation.ext hndΓ₂
        intro x S hx
        rw [Valuation.lookup_reorder (h := (PureEqv.σPerm r).symm)
          (σ := σ.reorder hΓ) hx (hxΓ hx),
          Valuation.lookup_reorder (h := hΓ) (σ := σ)
            (hxΓ hx) (hΓ.mem_iff.mp (hxΓ hx)),
          Valuation.lookup_reorder (h := (hΓ.symm.trans
              (PureEqv.σPerm r)).symm) (σ := σ) hx
            ((hΓ.symm.trans (PureEqv.σPerm r)).symm.mem_iff.mp hx)]
      have hτ : (τ.reorder hΔ).reorder (PureEqv.τPerm r).symm
          = τ.reorder (hΔ.symm.trans (PureEqv.τPerm r)).symm := by
        apply Valuation.ext hndΔ₂
        intro x S hx
        rw [Valuation.lookup_reorder (h := (PureEqv.τPerm r).symm)
          (σ := τ.reorder hΔ) hx (hxΔ hx),
          Valuation.lookup_reorder (h := hΔ) (σ := τ)
            (hxΔ hx) (hΔ.mem_iff.mp (hxΔ hx)),
          Valuation.lookup_reorder (h := (hΔ.symm.trans
              (PureEqv.τPerm r)).symm) (σ := τ) hx
            ((hΔ.symm.trans (PureEqv.τPerm r)).symm.mem_iff.mp hx)]
      rw [hσ, hτ]
  | @hpermR Γ₁ Δ₁ Γ₂ Γ₂' Δ₂ Δ₂' e T hWΓ hWΔ d₁ d₂ r hΓ hΔ ih =>
      intro σ τ
      have hndΓ' : Γ₂'.Nodup := hWΓ.nodup
      have hndΔ' : Δ₂'.Nodup := hWΔ.nodup
      have hxΓ : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Γ₂ →
          (x, S) ∈ Γ₁ := fun _ _ hx => (PureEqv.σPerm r).mem_iff.mpr hx
      have hxΔ : ∀ ⦃x : Variable⦄ ⦃S : DataType⦄, (x, S) ∈ Δ₂ →
          (x, S) ∈ Δ₁ := fun _ _ hx => (PureEqv.τPerm r).mem_iff.mpr hx
      simp only [PureEqv.transport]
      rw [ih σ τ]
      have hσ : (σ.reorder (PureEqv.σPerm r).symm).reorder hΓ.symm
          = σ.reorder ((PureEqv.σPerm r).trans hΓ).symm := by
        apply Valuation.ext hndΓ'
        intro x S hx
        rw [Valuation.lookup_reorder (h := hΓ.symm)
          (σ := σ.reorder (PureEqv.σPerm r).symm)
            hx (hΓ.symm.mem_iff.mp hx),
          Valuation.lookup_reorder (h := (PureEqv.σPerm r).symm) (σ := σ)
            (hΓ.symm.mem_iff.mp hx) (hxΓ (hΓ.symm.mem_iff.mp hx)),
          Valuation.lookup_reorder (h := ((PureEqv.σPerm r).trans hΓ).symm)
            (σ := σ) hx
            (((PureEqv.σPerm r).trans hΓ).symm.mem_iff.mp hx)]
      have hτ : (τ.reorder (PureEqv.τPerm r).symm).reorder hΔ.symm
          = τ.reorder ((PureEqv.τPerm r).trans hΔ).symm := by
        apply Valuation.ext hndΔ'
        intro x S hx
        rw [Valuation.lookup_reorder (h := hΔ.symm)
          (σ := τ.reorder (PureEqv.τPerm r).symm)
            hx (hΔ.symm.mem_iff.mp hx),
          Valuation.lookup_reorder (h := (PureEqv.τPerm r).symm) (σ := τ)
            (hΔ.symm.mem_iff.mp hx) (hxΔ (hΔ.symm.mem_iff.mp hx)),
          Valuation.lookup_reorder (h := ((PureEqv.τPerm r).trans hΔ).symm)
            (σ := τ) hx
            (((PureEqv.τPerm r).trans hΔ).symm.mem_iff.mp hx)]
      rw [hσ, hτ]

/-- Transporting from the empty pure context: the pattern-derivation case
needed by the branch uniqueness step. -/
theorem PureEqv.transport_nil_eq {Γⱼ₁ Γⱼ₂ : Context} {e : Expression}
    {T : DataType} {dPat₁ : PureDerivation [] Γⱼ₁ e T}
    {dPat₂ : PureDerivation [] Γⱼ₂ e T} (hp : PureEqv dPat₁ dPat₂) :
    ∀ σⱼ : Valuation Γⱼ₁,
      hp.transport Valuation.nil σⱼ
        = (Valuation.nil, σⱼ.reorder (hp.τPerm).symm) := by
  intro σⱼ
  have h := PureEqv.transport_eq hp Valuation.nil σⱼ
  rw [h]
  rfl

/-! ### The compatibility conditions

The three `Shared` predicates record how the sub-witnesses' transports must
align with the decomposition permutations recorded by the enclosing rule —
the analogue of the paper recording the decomposition in the judgment.
They are mutually recursive (`mix` constrains its pure witness, `ctrl` its
mixed and branch witnesses, each branch its pattern and body witnesses), so
they are computed through the combined mutual recursor with all three
motives set to the constant `Prop`: the cross-type recursion then appears
as the recursor's own induction hypotheses, and every constructor binder
(including the implicit context decompositions) can be named in the
case functions.  The three entry points below apply the same case family
through each type's recursor; the values agree because the case functions
are identical. -/

/-- Compatibility for pure equivalences. -/
def PureEqv.Shared {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression} {T : DataType}
    {d₁ : PureDerivation Γ₁ Δ₁ e₁ T} {d₂ : PureDerivation Γ₂ Δ₂ e₂ T}
    (r : PureEqv d₁ d₂) : Prop :=
  PureEqv.rec
    (motive_1 := fun {_ _ _ _ _ _ _} _ _ _ => Prop)
    (motive_2 := fun {_ _ _ _} _ _ _ => Prop)
    (motive_3 := fun {_ _ _ _ _ _ _ _} _ _ _ _ {_ _ _ _} _ _ _ => Prop)
    (fun {Γ₁ Γ₂ : Context} {_ : Context.WellFormed Γ₁}
        {_ : Context.WellFormed Γ₂} _ => True)
    (fun {Γa₁ Γb₁ Γa₂ Γb₂ : Context} {x : Variable} {T : DataType}
        {_ : Context.WellFormed (Γa₁ ++ [(x, T)] ++ Γb₁)}
        {_ : Context.WellFormed (Γa₂ ++ [(x, T)] ++ Γb₂)} _ => True)
    (fun {Γ₁ Γ₂ : Context} {x : Variable} {_ : DataType}
        {_ : Context.WellFormed Γ₁} {_ : Context.WellFormed Γ₂}
        {_ : x ∉ Context.dom Γ₁} {_ : x ∉ Context.dom Γ₂} _ => True)
    (fun {Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' : Context} {e₀ e₁ : Expression}
        {T₀ T₁ : DataType}
        {_ : Context.WellFormed Γ₁} {_ : Context.WellFormed Γ₂}
        {_ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
        {_ : Context.WellFormed (Δ' ++ Δ₀' ++ Δ₁')}
        (hΓ : List.Perm Γ₁ Γ₂) (hΔ : List.Perm Δ Δ')
        (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
        {d₀ : PureDerivation Γ₁ (Δ ++ Δ₀) e₀ T₀}
        {d₁ : PureDerivation Γ₁ (Δ ++ Δ₁) e₁ T₁}
        {d₀' : PureDerivation Γ₂ (Δ' ++ Δ₀') e₀ T₀}
        {d₁' : PureDerivation Γ₂ (Δ' ++ Δ₁') e₁ T₁}
        (r₀ : PureEqv d₀ d₀') (r₁ : PureEqv d₁ d₁')
        (ih₀ ih₁ : Prop) =>
      ih₀ ∧ ih₁ ∧
        (∀ (σ : Valuation Γ₁) (τ : Valuation (Δ ++ Δ₀ ++ Δ₁)),
          let p := Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ
          let q := p.1.split (Γ := Δ) (Δ := Δ₀)
          r₀.transport σ p.1
            = (σ.reorder hΓ.symm,
              (q.1.reorder hΔ.symm).append (q.2.reorder h₀.symm))) ∧
        (∀ (σ : Valuation Γ₁) (τ : Valuation (Δ ++ Δ₀ ++ Δ₁)),
          let p := Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ
          let q := p.1.split (Γ := Δ) (Δ := Δ₀)
          r₁.transport σ (q.1.append p.2)
            = (σ.reorder hΓ.symm,
              (q.1.reorder hΔ.symm).append (p.2.reorder h₁.symm))))
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' G₂ G₂' D₂ D₂' : Context} {e : Expression}
        {T T' : DataType} {l₁ l₂ : List ((Expression × Expression) × Context)}
        {_ : Context.WellFormed (Γ₁ ++ Γ₁' ++ Δ₁ ++ Δ₁')}
        {_ : Context.WellFormed (G₂ ++ G₂' ++ D₂ ++ D₂')}
        (_ : l₁.map Prod.fst = l₂.map Prod.fst)
        (hΓ : List.Perm Γ₁ G₂) (hΓ' : List.Perm Γ₁' G₂')
        (hΔ : List.Perm Δ₁ D₂) (hΔ' : List.Perm Δ₁' D₂')
        {dMix₁ : MixedDerivation (Γ₁ ++ Δ₁) e T}
        {dMix₂ : MixedDerivation (G₂ ++ D₂) e T}
        (r : MixedEqv dMix₁ dMix₂)
        {_ : Ortho T (l₁.map (Prod.fst ∘ Prod.fst))}
        {_ : Ortho T (l₂.map (Prod.fst ∘ Prod.fst))}
        {_ : ∀ x, x ∈ Context.dom Δ₁ →
          Erases x T' (l₁.map (Prod.snd ∘ Prod.fst))}
        {_ : ∀ x, x ∈ Context.dom D₂ →
          Erases x T' (l₂.map (Prod.snd ∘ Prod.fst))}
        {dB₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
        {dB₂ : BranchDerivation G₂ G₂' D₂ D₂' l₂ T T'}
        (_ : BranchEqv hΓ hΓ' hΔ hΔ' dB₁ dB₂)
        (ihr ihrb : Prop) =>
      ihr ∧ ihrb ∧
        (∀ (σ : Valuation (Γ₁ ++ Γ₁')) (τ : Valuation (Δ₁ ++ Δ₁')),
          r.transport
              ((Valuation.split (Γ := Γ₁) (Δ := Γ₁') σ).1.append
                (Valuation.split (Γ := Δ₁) (Δ := Δ₁') τ).1)
            = ((Valuation.split (Γ := G₂) (Δ := G₂')
                  (σ.reorder (hΓ.append hΓ').symm)).1).append
                ((Valuation.split (Γ := D₂) (Δ := D₂')
                  (τ.reorder (hΔ.append hΔ').symm)).1)))
    (fun {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e : Expression} {f : Program}
        {T T' : DataType} {_ _ : ProgramDerivation f (T ⇝ T')}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        hΓ hΔ _ r ih =>
      ih ∧ (∀ (σ : Valuation Γ₁) (τ : Valuation Δ₁),
        r.transport σ τ = (σ.reorder hΓ.symm, τ.reorder hΔ.symm)))
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Γ₁'} {_ : Context.WellFormed Δ₁'}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        _ _ _ ih => ih)
    (fun {Γ₁ Δ₁ Γ₂ Γ₂' Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Γ₂'} {_ : Context.WellFormed Δ₂'}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        _ _ _ ih => ih)
    (fun {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₁} {_ : Context.WellFormed Δ₂}
        (h : List.Perm Δ₁ Δ₂)
        (dp₁ : PureDerivation [] Δ₁ e T) (dp₂ : PureDerivation [] Δ₂ e T)
        (pq : PureEqv dp₁ dp₂) (ihpq : Prop) =>
      ihpq ∧ (∀ τ : Valuation Δ₁,
        pq.transport Valuation.nil τ = (Valuation.nil, τ.reorder h.symm)))
    (fun {Δ₁ Δ₁' Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₁'}
        {_ : MixedDerivation Δ₁ e T} {_ : MixedDerivation Δ₂ e T} _ _ ih => ih)
    (fun {Δ₁ Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₂'}
        {_ : MixedDerivation Δ₁ e T} {_ : MixedDerivation Δ₂ e T} _ _ ih => ih)
    (fun {Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' e₀ e₁ T₀ T₁ _ _} hΔ h₀ h₁
        {_ : MixedDerivation (Δ ++ Δ₀) e₀ T₀} {_ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
        {_ : MixedDerivation (Δ' ++ Δ₀') e₀ T₀} {_ : MixedDerivation (Δ' ++ Δ₁') e₁ T₁}
        r₀ r₁ ih₀ ih₁ =>
      ih₀ ∧ ih₁ ∧
        (∀ (a : Valuation Δ) (b : Valuation Δ₀),
          r₀.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
        (∀ (a : Valuation Δ) (b : Valuation Δ₁),
          r₁.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₁.symm)))
    (fun {Δ₀ Δ₁ Δ₀' Δ₁' e₀ e₁ T _ _} _ _
        {_ : MixedDerivation Δ₀ e₀ T} {_ : MixedDerivation Δ₁ e₁ T}
        {_ : MixedDerivation Δ₀' e₀ T} {_ : MixedDerivation Δ₁' e₁ T}
        _ _ ih₀ ih₁ => ih₀ ∧ ih₁)
    (fun {Δ Δ' : Context} {e : Expression} {f : Program} {T T' : DataType}
        {_ _ : ProgramDerivation f (T ⇛ T')}
        {_ : MixedDerivation Δ e T} {_ : MixedDerivation Δ' e T}
        _ _ ih => ih)
    (fun {Δ Δ₀ Δ₁ Δs Δ₀s Δ₁s : Context} {e₀ e₁ : Expression}
        {T₀ T₁ : DataType}
        {_ : Context.WellFormed ((Δs ++ Δ₀s) ++ Δ₁s)}
        {_ : Context.WellFormed ((Δ ++ Δ₀) ++ Δ₁)}
        {_ : Context.WellFormed (Δs ++ Δ₀s)}
        {_ : Context.WellFormed (Δs ++ Δ₁s)}
        {_ : PureDerivation [] (Δs ++ Δ₀s) e₀ T₀}
        {_ : PureDerivation [] (Δs ++ Δ₁s) e₁ T₁}
        hΔ h₀ h₁
        {_ : MixedDerivation (Δ ++ Δ₀) e₀ T₀}
        {_ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
        r₀ r₁ ih₀ ih₁ =>
      ih₀ ∧ ih₁ ∧
        (∀ (a : Valuation Δs) (b : Valuation Δ₀s),
          r₀.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
        (∀ (a : Valuation Δs) (b : Valuation Δ₁s),
          r₁.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₁.symm)))
    (fun {Δd Δ : Context} {e : Expression} {f : Program} {T T' : DataType}
        {_ : Context.WellFormed Δd}
        {_ : PureDerivation [] Δd e T}
        {_ : ProgramDerivation f (T ⇝ T')}
        {_ : MixedDerivation Δ e T}
        _ ih => ih)
    (fun {_ _ _ _ _ _ _ _ _ _ _ _ _ _} => True)
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' _ _ _ _ hΓ hΓ' hΔ hΔ' _ _ Γⱼ₁ _ _ _ _ _
          _ _ _ _ _ _} hp hb _ ihp ihb ihrt =>
      ihp ∧ ihb ∧ ihrt ∧
        (∀ (σ : Valuation (Γ₁ ++ Γ₁')) (τ : Valuation (Δ₁ ++ Δ₁'))
            (σⱼ : Valuation Γⱼ₁),
          hb.transport (σ.append σⱼ) τ
            = ((σ.reorder (hΓ.append hΓ').symm).append
                (σⱼ.reorder (hp.τPerm).symm),
              τ.reorder (hΔ.append hΔ').symm)))
    r

/-- Compatibility for mixed equivalences. -/
def MixedEqv.Shared {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    {d₁ : MixedDerivation Δ₁ e T} {d₂ : MixedDerivation Δ₂ e T}
    (r : MixedEqv d₁ d₂) : Prop :=
  MixedEqv.rec
    (motive_1 := fun {_ _ _ _ _ _ _} _ _ _ => Prop)
    (motive_2 := fun {_ _ _ _} _ _ _ => Prop)
    (motive_3 := fun {_ _ _ _ _ _ _ _} _ _ _ _ {_ _ _ _} _ _ _ => Prop)
    (fun {Γ₁ Γ₂ : Context} {_ : Context.WellFormed Γ₁}
        {_ : Context.WellFormed Γ₂} _ => True)
    (fun {Γa₁ Γb₁ Γa₂ Γb₂ : Context} {x : Variable} {T : DataType}
        {_ : Context.WellFormed (Γa₁ ++ [(x, T)] ++ Γb₁)}
        {_ : Context.WellFormed (Γa₂ ++ [(x, T)] ++ Γb₂)} _ => True)
    (fun {Γ₁ Γ₂ : Context} {x : Variable} {_ : DataType}
        {_ : Context.WellFormed Γ₁} {_ : Context.WellFormed Γ₂}
        {_ : x ∉ Context.dom Γ₁} {_ : x ∉ Context.dom Γ₂} _ => True)
    (fun {Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' : Context} {e₀ e₁ : Expression}
        {T₀ T₁ : DataType}
        {_ : Context.WellFormed Γ₁} {_ : Context.WellFormed Γ₂}
        {_ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
        {_ : Context.WellFormed (Δ' ++ Δ₀' ++ Δ₁')}
        (hΓ : List.Perm Γ₁ Γ₂) (hΔ : List.Perm Δ Δ')
        (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
        {d₀ : PureDerivation Γ₁ (Δ ++ Δ₀) e₀ T₀}
        {d₁ : PureDerivation Γ₁ (Δ ++ Δ₁) e₁ T₁}
        {d₀' : PureDerivation Γ₂ (Δ' ++ Δ₀') e₀ T₀}
        {d₁' : PureDerivation Γ₂ (Δ' ++ Δ₁') e₁ T₁}
        (r₀ : PureEqv d₀ d₀') (r₁ : PureEqv d₁ d₁')
        (ih₀ ih₁ : Prop) =>
      ih₀ ∧ ih₁ ∧
        (∀ (σ : Valuation Γ₁) (τ : Valuation (Δ ++ Δ₀ ++ Δ₁)),
          let p := Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ
          let q := p.1.split (Γ := Δ) (Δ := Δ₀)
          r₀.transport σ p.1
            = (σ.reorder hΓ.symm,
              (q.1.reorder hΔ.symm).append (q.2.reorder h₀.symm))) ∧
        (∀ (σ : Valuation Γ₁) (τ : Valuation (Δ ++ Δ₀ ++ Δ₁)),
          let p := Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ
          let q := p.1.split (Γ := Δ) (Δ := Δ₀)
          r₁.transport σ (q.1.append p.2)
            = (σ.reorder hΓ.symm,
              (q.1.reorder hΔ.symm).append (p.2.reorder h₁.symm))))
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' G₂ G₂' D₂ D₂' : Context} {e : Expression}
        {T T' : DataType} {l₁ l₂ : List ((Expression × Expression) × Context)}
        {_ : Context.WellFormed (Γ₁ ++ Γ₁' ++ Δ₁ ++ Δ₁')}
        {_ : Context.WellFormed (G₂ ++ G₂' ++ D₂ ++ D₂')}
        (_ : l₁.map Prod.fst = l₂.map Prod.fst)
        (hΓ : List.Perm Γ₁ G₂) (hΓ' : List.Perm Γ₁' G₂')
        (hΔ : List.Perm Δ₁ D₂) (hΔ' : List.Perm Δ₁' D₂')
        {dMix₁ : MixedDerivation (Γ₁ ++ Δ₁) e T}
        {dMix₂ : MixedDerivation (G₂ ++ D₂) e T}
        (r : MixedEqv dMix₁ dMix₂)
        {_ : Ortho T (l₁.map (Prod.fst ∘ Prod.fst))}
        {_ : Ortho T (l₂.map (Prod.fst ∘ Prod.fst))}
        {_ : ∀ x, x ∈ Context.dom Δ₁ →
          Erases x T' (l₁.map (Prod.snd ∘ Prod.fst))}
        {_ : ∀ x, x ∈ Context.dom D₂ →
          Erases x T' (l₂.map (Prod.snd ∘ Prod.fst))}
        {dB₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
        {dB₂ : BranchDerivation G₂ G₂' D₂ D₂' l₂ T T'}
        (_ : BranchEqv hΓ hΓ' hΔ hΔ' dB₁ dB₂)
        (ihr ihrb : Prop) =>
      ihr ∧ ihrb ∧
        (∀ (σ : Valuation (Γ₁ ++ Γ₁')) (τ : Valuation (Δ₁ ++ Δ₁')),
          r.transport
              ((Valuation.split (Γ := Γ₁) (Δ := Γ₁') σ).1.append
                (Valuation.split (Γ := Δ₁) (Δ := Δ₁') τ).1)
            = ((Valuation.split (Γ := G₂) (Δ := G₂')
                  (σ.reorder (hΓ.append hΓ').symm)).1).append
                ((Valuation.split (Γ := D₂) (Δ := D₂')
                  (τ.reorder (hΔ.append hΔ').symm)).1)))
    (fun {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e : Expression} {f : Program}
        {T T' : DataType} {_ _ : ProgramDerivation f (T ⇝ T')}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        hΓ hΔ _ r ih =>
      ih ∧ (∀ (σ : Valuation Γ₁) (τ : Valuation Δ₁),
        r.transport σ τ = (σ.reorder hΓ.symm, τ.reorder hΔ.symm)))
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Γ₁'} {_ : Context.WellFormed Δ₁'}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        _ _ _ ih => ih)
    (fun {Γ₁ Δ₁ Γ₂ Γ₂' Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Γ₂'} {_ : Context.WellFormed Δ₂'}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        _ _ _ ih => ih)
    (fun {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₁} {_ : Context.WellFormed Δ₂}
        (h : List.Perm Δ₁ Δ₂)
        (dp₁ : PureDerivation [] Δ₁ e T) (dp₂ : PureDerivation [] Δ₂ e T)
        (pq : PureEqv dp₁ dp₂) (ihpq : Prop) =>
      ihpq ∧ (∀ τ : Valuation Δ₁,
        pq.transport Valuation.nil τ = (Valuation.nil, τ.reorder h.symm)))
    (fun {Δ₁ Δ₁' Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₁'}
        {_ : MixedDerivation Δ₁ e T} {_ : MixedDerivation Δ₂ e T} _ _ ih => ih)
    (fun {Δ₁ Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₂'}
        {_ : MixedDerivation Δ₁ e T} {_ : MixedDerivation Δ₂ e T} _ _ ih => ih)
    (fun {Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' e₀ e₁ T₀ T₁ _ _} hΔ h₀ h₁
        {_ : MixedDerivation (Δ ++ Δ₀) e₀ T₀} {_ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
        {_ : MixedDerivation (Δ' ++ Δ₀') e₀ T₀} {_ : MixedDerivation (Δ' ++ Δ₁') e₁ T₁}
        r₀ r₁ ih₀ ih₁ =>
      ih₀ ∧ ih₁ ∧
        (∀ (a : Valuation Δ) (b : Valuation Δ₀),
          r₀.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
        (∀ (a : Valuation Δ) (b : Valuation Δ₁),
          r₁.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₁.symm)))
    (fun {Δ₀ Δ₁ Δ₀' Δ₁' e₀ e₁ T _ _} _ _
        {_ : MixedDerivation Δ₀ e₀ T} {_ : MixedDerivation Δ₁ e₁ T}
        {_ : MixedDerivation Δ₀' e₀ T} {_ : MixedDerivation Δ₁' e₁ T}
        _ _ ih₀ ih₁ => ih₀ ∧ ih₁)
    (fun {Δ Δ' : Context} {e : Expression} {f : Program} {T T' : DataType}
        {_ _ : ProgramDerivation f (T ⇛ T')}
        {_ : MixedDerivation Δ e T} {_ : MixedDerivation Δ' e T}
        _ _ ih => ih)
    (fun {Δ Δ₀ Δ₁ Δs Δ₀s Δ₁s : Context} {e₀ e₁ : Expression}
        {T₀ T₁ : DataType}
        {_ : Context.WellFormed ((Δs ++ Δ₀s) ++ Δ₁s)}
        {_ : Context.WellFormed ((Δ ++ Δ₀) ++ Δ₁)}
        {_ : Context.WellFormed (Δs ++ Δ₀s)}
        {_ : Context.WellFormed (Δs ++ Δ₁s)}
        {_ : PureDerivation [] (Δs ++ Δ₀s) e₀ T₀}
        {_ : PureDerivation [] (Δs ++ Δ₁s) e₁ T₁}
        hΔ h₀ h₁
        {_ : MixedDerivation (Δ ++ Δ₀) e₀ T₀}
        {_ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
        r₀ r₁ ih₀ ih₁ =>
      ih₀ ∧ ih₁ ∧
        (∀ (a : Valuation Δs) (b : Valuation Δ₀s),
          r₀.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
        (∀ (a : Valuation Δs) (b : Valuation Δ₁s),
          r₁.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₁.symm)))
    (fun {Δd Δ : Context} {e : Expression} {f : Program} {T T' : DataType}
        {_ : Context.WellFormed Δd}
        {_ : PureDerivation [] Δd e T}
        {_ : ProgramDerivation f (T ⇝ T')}
        {_ : MixedDerivation Δ e T}
        _ ih => ih)
    (fun {_ _ _ _ _ _ _ _ _ _ _ _ _ _} => True)
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' _ _ _ _ hΓ hΓ' hΔ hΔ' _ _ Γⱼ₁ _ _ _ _ _
          _ _ _ _ _ _} hp hb _ ihp ihb ihrt =>
      ihp ∧ ihb ∧ ihrt ∧
        (∀ (σ : Valuation (Γ₁ ++ Γ₁')) (τ : Valuation (Δ₁ ++ Δ₁'))
            (σⱼ : Valuation Γⱼ₁),
          hb.transport (σ.append σⱼ) τ
            = ((σ.reorder (hΓ.append hΓ').symm).append
                (σⱼ.reorder (hp.τPerm).symm),
              τ.reorder (hΔ.append hΔ').symm)))
    r

/-- Compatibility for branch equivalences. -/
def BranchEqv.Shared {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context}
    {hΓ : List.Perm Γ₁ Γ₂} {hΓ' : List.Perm Γ₁' Γ₂'}
    {hΔ : List.Perm Δ₁ Δ₂} {hΔ' : List.Perm Δ₁' Δ₂'}
    {l₁ l₂ : List ((Expression × Expression) × Context)} {T T' : DataType}
    {b₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
    {b₂ : BranchDerivation Γ₂ Γ₂' Δ₂ Δ₂' l₂ T T'}
    (rb : BranchEqv hΓ hΓ' hΔ hΔ' b₁ b₂) : Prop :=
  BranchEqv.rec
    (motive_1 := fun {_ _ _ _ _ _ _} _ _ _ => Prop)
    (motive_2 := fun {_ _ _ _} _ _ _ => Prop)
    (motive_3 := fun {_ _ _ _ _ _ _ _} _ _ _ _ {_ _ _ _} _ _ _ => Prop)
    (fun {Γ₁ Γ₂ : Context} {_ : Context.WellFormed Γ₁}
        {_ : Context.WellFormed Γ₂} _ => True)
    (fun {Γa₁ Γb₁ Γa₂ Γb₂ : Context} {x : Variable} {T : DataType}
        {_ : Context.WellFormed (Γa₁ ++ [(x, T)] ++ Γb₁)}
        {_ : Context.WellFormed (Γa₂ ++ [(x, T)] ++ Γb₂)} _ => True)
    (fun {Γ₁ Γ₂ : Context} {x : Variable} {_ : DataType}
        {_ : Context.WellFormed Γ₁} {_ : Context.WellFormed Γ₂}
        {_ : x ∉ Context.dom Γ₁} {_ : x ∉ Context.dom Γ₂} _ => True)
    (fun {Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' : Context} {e₀ e₁ : Expression}
        {T₀ T₁ : DataType}
        {_ : Context.WellFormed Γ₁} {_ : Context.WellFormed Γ₂}
        {_ : Context.WellFormed (Δ ++ Δ₀ ++ Δ₁)}
        {_ : Context.WellFormed (Δ' ++ Δ₀' ++ Δ₁')}
        (hΓ : List.Perm Γ₁ Γ₂) (hΔ : List.Perm Δ Δ')
        (h₀ : List.Perm Δ₀ Δ₀') (h₁ : List.Perm Δ₁ Δ₁')
        {d₀ : PureDerivation Γ₁ (Δ ++ Δ₀) e₀ T₀}
        {d₁ : PureDerivation Γ₁ (Δ ++ Δ₁) e₁ T₁}
        {d₀' : PureDerivation Γ₂ (Δ' ++ Δ₀') e₀ T₀}
        {d₁' : PureDerivation Γ₂ (Δ' ++ Δ₁') e₁ T₁}
        (r₀ : PureEqv d₀ d₀') (r₁ : PureEqv d₁ d₁')
        (ih₀ ih₁ : Prop) =>
      ih₀ ∧ ih₁ ∧
        (∀ (σ : Valuation Γ₁) (τ : Valuation (Δ ++ Δ₀ ++ Δ₁)),
          let p := Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ
          let q := p.1.split (Γ := Δ) (Δ := Δ₀)
          r₀.transport σ p.1
            = (σ.reorder hΓ.symm,
              (q.1.reorder hΔ.symm).append (q.2.reorder h₀.symm))) ∧
        (∀ (σ : Valuation Γ₁) (τ : Valuation (Δ ++ Δ₀ ++ Δ₁)),
          let p := Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ
          let q := p.1.split (Γ := Δ) (Δ := Δ₀)
          r₁.transport σ (q.1.append p.2)
            = (σ.reorder hΓ.symm,
              (q.1.reorder hΔ.symm).append (p.2.reorder h₁.symm))))
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' G₂ G₂' D₂ D₂' : Context} {e : Expression}
        {T T' : DataType} {l₁ l₂ : List ((Expression × Expression) × Context)}
        {_ : Context.WellFormed (Γ₁ ++ Γ₁' ++ Δ₁ ++ Δ₁')}
        {_ : Context.WellFormed (G₂ ++ G₂' ++ D₂ ++ D₂')}
        (_ : l₁.map Prod.fst = l₂.map Prod.fst)
        (hΓ : List.Perm Γ₁ G₂) (hΓ' : List.Perm Γ₁' G₂')
        (hΔ : List.Perm Δ₁ D₂) (hΔ' : List.Perm Δ₁' D₂')
        {dMix₁ : MixedDerivation (Γ₁ ++ Δ₁) e T}
        {dMix₂ : MixedDerivation (G₂ ++ D₂) e T}
        (r : MixedEqv dMix₁ dMix₂)
        {_ : Ortho T (l₁.map (Prod.fst ∘ Prod.fst))}
        {_ : Ortho T (l₂.map (Prod.fst ∘ Prod.fst))}
        {_ : ∀ x, x ∈ Context.dom Δ₁ →
          Erases x T' (l₁.map (Prod.snd ∘ Prod.fst))}
        {_ : ∀ x, x ∈ Context.dom D₂ →
          Erases x T' (l₂.map (Prod.snd ∘ Prod.fst))}
        {dB₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T'}
        {dB₂ : BranchDerivation G₂ G₂' D₂ D₂' l₂ T T'}
        (_ : BranchEqv hΓ hΓ' hΔ hΔ' dB₁ dB₂)
        (ihr ihrb : Prop) =>
      ihr ∧ ihrb ∧
        (∀ (σ : Valuation (Γ₁ ++ Γ₁')) (τ : Valuation (Δ₁ ++ Δ₁')),
          r.transport
              ((Valuation.split (Γ := Γ₁) (Δ := Γ₁') σ).1.append
                (Valuation.split (Γ := Δ₁) (Δ := Δ₁') τ).1)
            = ((Valuation.split (Γ := G₂) (Δ := G₂')
                  (σ.reorder (hΓ.append hΓ').symm)).1).append
                ((Valuation.split (Γ := D₂) (Δ := D₂')
                  (τ.reorder (hΔ.append hΔ').symm)).1)))
    (fun {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e : Expression} {f : Program}
        {T T' : DataType} {_ _ : ProgramDerivation f (T ⇝ T')}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        hΓ hΔ _ r ih =>
      ih ∧ (∀ (σ : Valuation Γ₁) (τ : Valuation Δ₁),
        r.transport σ τ = (σ.reorder hΓ.symm, τ.reorder hΔ.symm)))
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Γ₁'} {_ : Context.WellFormed Δ₁'}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        _ _ _ ih => ih)
    (fun {Γ₁ Δ₁ Γ₂ Γ₂' Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Γ₂'} {_ : Context.WellFormed Δ₂'}
        {_ : PureDerivation Γ₁ Δ₁ e T} {_ : PureDerivation Γ₂ Δ₂ e T}
        _ _ _ ih => ih)
    (fun {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₁} {_ : Context.WellFormed Δ₂}
        (h : List.Perm Δ₁ Δ₂)
        (dp₁ : PureDerivation [] Δ₁ e T) (dp₂ : PureDerivation [] Δ₂ e T)
        (pq : PureEqv dp₁ dp₂) (ihpq : Prop) =>
      ihpq ∧ (∀ τ : Valuation Δ₁,
        pq.transport Valuation.nil τ = (Valuation.nil, τ.reorder h.symm)))
    (fun {Δ₁ Δ₁' Δ₂ : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₁'}
        {_ : MixedDerivation Δ₁ e T} {_ : MixedDerivation Δ₂ e T} _ _ ih => ih)
    (fun {Δ₁ Δ₂ Δ₂' : Context} {e : Expression} {T : DataType}
        {_ : Context.WellFormed Δ₂'}
        {_ : MixedDerivation Δ₁ e T} {_ : MixedDerivation Δ₂ e T} _ _ ih => ih)
    (fun {Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' e₀ e₁ T₀ T₁ _ _} hΔ h₀ h₁
        {_ : MixedDerivation (Δ ++ Δ₀) e₀ T₀} {_ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
        {_ : MixedDerivation (Δ' ++ Δ₀') e₀ T₀} {_ : MixedDerivation (Δ' ++ Δ₁') e₁ T₁}
        r₀ r₁ ih₀ ih₁ =>
      ih₀ ∧ ih₁ ∧
        (∀ (a : Valuation Δ) (b : Valuation Δ₀),
          r₀.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
        (∀ (a : Valuation Δ) (b : Valuation Δ₁),
          r₁.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₁.symm)))
    (fun {Δ₀ Δ₁ Δ₀' Δ₁' e₀ e₁ T _ _} _ _
        {_ : MixedDerivation Δ₀ e₀ T} {_ : MixedDerivation Δ₁ e₁ T}
        {_ : MixedDerivation Δ₀' e₀ T} {_ : MixedDerivation Δ₁' e₁ T}
        _ _ ih₀ ih₁ => ih₀ ∧ ih₁)
    (fun {Δ Δ' : Context} {e : Expression} {f : Program} {T T' : DataType}
        {_ _ : ProgramDerivation f (T ⇛ T')}
        {_ : MixedDerivation Δ e T} {_ : MixedDerivation Δ' e T}
        _ _ ih => ih)
    (fun {Δ Δ₀ Δ₁ Δs Δ₀s Δ₁s : Context} {e₀ e₁ : Expression}
        {T₀ T₁ : DataType}
        {_ : Context.WellFormed ((Δs ++ Δ₀s) ++ Δ₁s)}
        {_ : Context.WellFormed ((Δ ++ Δ₀) ++ Δ₁)}
        {_ : Context.WellFormed (Δs ++ Δ₀s)}
        {_ : Context.WellFormed (Δs ++ Δ₁s)}
        {_ : PureDerivation [] (Δs ++ Δ₀s) e₀ T₀}
        {_ : PureDerivation [] (Δs ++ Δ₁s) e₁ T₁}
        hΔ h₀ h₁
        {_ : MixedDerivation (Δ ++ Δ₀) e₀ T₀}
        {_ : MixedDerivation (Δ ++ Δ₁) e₁ T₁}
        r₀ r₁ ih₀ ih₁ =>
      ih₀ ∧ ih₁ ∧
        (∀ (a : Valuation Δs) (b : Valuation Δ₀s),
          r₀.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
        (∀ (a : Valuation Δs) (b : Valuation Δ₁s),
          r₁.transport (a.append b)
            = (a.reorder hΔ.symm).append (b.reorder h₁.symm)))
    (fun {Δd Δ : Context} {e : Expression} {f : Program} {T T' : DataType}
        {_ : Context.WellFormed Δd}
        {_ : PureDerivation [] Δd e T}
        {_ : ProgramDerivation f (T ⇝ T')}
        {_ : MixedDerivation Δ e T}
        _ ih => ih)
    (fun {_ _ _ _ _ _ _ _ _ _ _ _ _ _} => True)
    (fun {Γ₁ Γ₁' Δ₁ Δ₁' _ _ _ _ hΓ hΓ' hΔ hΔ' _ _ Γⱼ₁ _ _ _ _ _
          _ _ _ _ _ _} hp hb _ ihp ihb ihrt =>
      ihp ∧ ihb ∧ ihrt ∧
        (∀ (σ : Valuation (Γ₁ ++ Γ₁')) (τ : Valuation (Δ₁ ++ Δ₁'))
            (σⱼ : Valuation Γⱼ₁),
          hb.transport (σ.append σⱼ) τ
            = ((σ.reorder (hΓ.append hΓ').symm).append
                (σⱼ.reorder (hp.τPerm).symm),
              τ.reorder (hΔ.append hΔ').symm)))
    rb

/-- Paper-faithful mixed amplitude uniqueness: equivalent proofs compute
equal amplitudes at correspondingly transported valuations. -/
def MixedUnique (n : Nat) : Prop :=
  ∀ {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : MixedDerivation Δ₁ e T) (d₂ : MixedDerivation Δ₂ e T),
    d₁.depth + d₂.depth ≤ n → (r : MixedEqv d₁ d₂) → MixedEqv.Shared r →
    ∀ (τ τ' : Valuation Δ₁) (v v' : Value T),
      mixedAmplitude d₁ τ τ' v v'
        = mixedAmplitude d₂ (r.transport τ) (r.transport τ') v v'

/-- Paper-faithful pure amplitude uniqueness: equivalent pure proofs compute
equal amplitudes at correspondingly transported valuations. -/
abbrev PureUniqueAt (n : Nat) : Prop :=
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression} {T : DataType}
    (d₁ : PureDerivation Γ₁ Δ₁ e₁ T) (d₂ : PureDerivation Γ₂ Δ₂ e₂ T),
    d₁.depth + d₂.depth ≤ n → (r : PureEqv d₁ d₂) → PureEqv.Shared r →
    ∀ (σ₁ : Valuation Γ₁) (τ₁ : Valuation Δ₁) (v : Value T),
      pureAmplitude d₁ σ₁ τ₁ v
        = pureAmplitude d₂ (r.transport σ₁ τ₁).1 (r.transport σ₁ τ₁).2 v

/-- Paper-faithful branch amplitude uniqueness: equivalent branch lists
compute equal amplitudes at correspondingly transported valuations, given
equal per-branch probabilities. -/
abbrev BranchUniqueAt (n : Nat) : Prop :=
  ∀ {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context}
    {l₁ l₂ : List ((Expression × Expression) × Context)} {T T' : DataType}
    (hΓ : List.Perm Γ₁ Γ₂) (hΓ' : List.Perm Γ₁' Γ₂')
    (hΔ : List.Perm Δ₁ Δ₂) (hΔ' : List.Perm Δ₁' Δ₂')
    (b₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T')
    (b₂ : BranchDerivation Γ₂ Γ₂' Δ₂ Δ₂' l₂ T T')
    (rb : BranchEqv hΓ hΓ' hΔ hΔ' b₁ b₂) (_ : BranchEqv.Shared rb),
    b₁.depth + b₂.depth ≤ n →
    ∀ (prob₁ prob₂ : Value T → ℂ), (∀ u, prob₁ u = prob₂ u) →
      ∀ (σ₁ : Valuation (Γ₁ ++ Γ₁')) (τ₁ : Valuation (Δ₁ ++ Δ₁'))
        (v : Value T'),
        branchAmplitude b₁ prob₁ σ₁ τ₁ v
          = branchAmplitude b₂ prob₂
              (BranchEqv.transport hΓ hΓ' hΔ hΔ' σ₁ τ₁).1
              (BranchEqv.transport hΓ hΓ' hΔ hΔ' σ₁ τ₁).2 v

abbrev PureAmpUniqueAt (n : Nat) : Prop :=
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : PureDerivation Γ₁ Δ₁ e T) (d₂ : PureDerivation Γ₂ Δ₂ e T),
    d₁.depth + d₂.depth ≤ n →
    ∀ (σ₁ : Valuation Γ₁) (τ₁ : Valuation Δ₁) (σ₂ : Valuation Γ₂)
      (τ₂ : Valuation Δ₂) (v : Value T),
      (σ₁.append τ₁).Agreed (σ₂.append τ₂) →
      pureAmplitude d₁ σ₁ τ₁ v = pureAmplitude d₂ σ₂ τ₂ v

/-- Base case: every mixed derivation has positive depth. -/
theorem mixedUnique_base : MixedUnique 0 := by
  intro Δ₁ Δ₂ e T d₁ d₂ hsum r hshared
  have h₁ : 0 < d₁.depth := by cases d₁ <;> simp [MixedDerivation.depth]
  have h₂ : 0 < d₂.depth := by cases d₂ <;> simp [MixedDerivation.depth]
  exact absurd hsum (by omega)

/-- **Successor step** for paper-faithful mixed uniqueness.  Each rule of the
equivalence gives one case.  The `mtry` case is the one the old
arbitrary-context statement could not prove: the trace tests are taken
along each side's own decomposition, and here the two decompositions
correspond by construction, with `transport_inj` transferring the equality
tests across the transport. -/
theorem List.star_sum {α : Type} [AddCommMonoid α] [StarAddMonoid α]
    (l : List α) : star l.sum = (l.map star).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem List.sum_map_mul_sum_map_aux {α : Type} (l₁ l₂ : List α)
    (f g : α → ℂ) :
    ((l₁.map fun a => ((l₂.map fun b => f a * g b).sum)).sum)
      = ((l₁.map f).sum) * ((l₂.map g).sum) := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, List.sum_map_mul_left]
      ring

theorem List.sum_mul_star_sum {α : Type} (l : List α) (f g : α → ℂ) :
    (l.map f).sum * star ((l.map g).sum)
      = (l.map fun a => (l.map fun b => f a * star (g b)).sum).sum := by
  rw [List.star_sum, List.map_map]
  change (l.map f).sum * (l.map (fun b => star (g b))).sum
    = (l.map fun a => (l.map fun b => f a * star (g b)).sum).sum
  rw [← List.sum_map_mul_sum_map_aux l l f (fun b => star (g b))]

theorem mixedUnique_step (pureIH : PureUniqueAt n) (ih : MixedUnique n) :
    MixedUnique (n + 1) := by
  intro Δ₁ Δ₂ e T d₁ d₂ hsum r hshared
  revert hshared
  revert hsum
  induction r using MixedEqv.induct with
  | @hmix Δ₁ Δ₂ e T hW₁ hW₂ h dp₁ dp₂ pq =>
      intro hsum hshared τ τ' v v'
      obtain ⟨hpq, hcomp⟩ :=
        (hshared : PureEqv.Shared pq ∧
          ∀ τ : Valuation Δ₁,
            pq.transport Valuation.nil τ = (Valuation.nil, τ.reorder h.symm))
      have hdp : dp₁.depth + dp₂.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum; omega
      have hfτ : (pq.transport Valuation.nil τ).1
          = (Valuation.nil : Valuation []) :=
        congrArg Prod.fst (hcomp τ)
      have hsτ : (pq.transport Valuation.nil τ).2
          = τ.reorder h.symm :=
        congrArg Prod.snd (hcomp τ)
      have hfτ' : (pq.transport Valuation.nil τ').1
          = (Valuation.nil : Valuation []) :=
        congrArg Prod.fst (hcomp τ')
      have hsτ' : (pq.transport Valuation.nil τ').2
          = τ'.reorder h.symm :=
        congrArg Prod.snd (hcomp τ')
      simp only [MixedEqv.transport, mixedAmplitude]
      rw [pureIH dp₁ dp₂ hdp pq hpq Valuation.nil τ v,
        pureIH dp₁ dp₂ hdp pq hpq Valuation.nil τ' v',
        hfτ, hsτ, hfτ', hsτ']

  | @hpermL _ _ _ _ _ _ dᵢ d₂o h' r' _ =>
      intro hsum hshared τ τ' v v'
      have hd : dᵢ.depth + d₂o.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum; omega
      simp only [MixedEqv.transport, mixedAmplitude]
      exact ih dᵢ d₂o hd r' hshared (τ.reorder h') (τ'.reorder h') v v'
  | @hpermR _ Δᵢ _ _ _ _ d₁ dᵢ r' h' _ =>
      intro hsum hshared τ τ' v v'
      have hndᵢ : List.Nodup Δᵢ := Context.WellFormed.nodup
        (HasMixedType.context_well_formed dᵢ.toProp)
      have hd : d₁.depth + dᵢ.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum; omega
      have hrr : ∀ σ : Valuation Δᵢ, ((σ.reorder h'.symm).reorder h') = σ :=
        fun σ => Valuation.reorder_reorder (h := h'.symm) hndᵢ σ
      simp only [MixedEqv.transport, mixedAmplitude]
      rw [hrr (r'.transport τ), hrr (r'.transport τ')]
      exact ih d₁ dᵢ hd r' hshared τ τ' v v'
  | @happ _ _ _ _ _ _ _ _ de₁ de₂ hprog r' _ =>
      intro hsum hshared τ τ' v v'
      have hd : de₁.depth + de₂.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum; omega
      simp only [MixedEqv.transport, mixedAmplitude]
      rw [hprog]
      refine congrArg List.sum (List.map_congr_left fun w _ => ?_)
      refine congrArg List.sum (List.map_congr_left fun w' _ => ?_)
      rw [ih de₁ de₂ hd r' hshared τ τ' w w']
  | @hmtry Δ₀ Δ₁ Δ₀' Δ₁' _ _ Ti hW₁ hW₂ h₀ h₁ d₀ d₁ d₀' d₁' r₀ r₁ _ _ =>
      intro hsum hshared
      obtain ⟨hs₀, hs₁⟩ :=
        (hshared : MixedEqv.Shared r₀ ∧ MixedEqv.Shared r₁)
      intro τ τ' v v'
      have hnd₁ : List.Nodup (Δ₀ ++ Δ₁) := Context.WellFormed.nodup hW₁
      have hnd₂ : List.Nodup (Δ₀' ++ Δ₁') := Context.WellFormed.nodup hW₂
      have hndL : List.Nodup Δ₀ := List.Nodup.of_append_left hnd₁
      have hndL' : List.Nodup Δ₀' := List.Nodup.of_append_left hnd₂
      have hndR : List.Nodup Δ₁ := List.Nodup.of_append_right hnd₁
      have hndR' : List.Nodup Δ₁' := List.Nodup.of_append_right hnd₂
      have hd₀ : d₀.depth + d₀'.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum
        have m₁ := Nat.le_max_left d₀.depth d₁.depth
        have m₂ := Nat.le_max_right d₀.depth d₁.depth
        have m₃ := Nat.le_max_left d₀'.depth d₁'.depth
        have m₄ := Nat.le_max_right d₀'.depth d₁'.depth
        omega
      have hd₁ : d₁.depth + d₁'.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum
        have m₁ := Nat.le_max_left d₀.depth d₁.depth
        have m₂ := Nat.le_max_right d₀.depth d₁.depth
        have m₃ := Nat.le_max_left d₀'.depth d₁'.depth
        have m₄ := Nat.le_max_right d₀'.depth d₁'.depth
        omega
      have e₀ : ∀ (a a' : Value Ti),
          mixedAmplitude d₀ (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1
              (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1 a a'
          = mixedAmplitude d₀' (r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1)
              (r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1) a a' :=
        fun a a' => ih d₀ d₀' hd₀ r₀ hs₀ _ _ a a'
      have e₁ : ∀ (a a' : Value Ti),
          mixedAmplitude d₁ (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).2
              (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').2 a a'
          = mixedAmplitude d₁' (r₁.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).2)
              (r₁.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').2) a a' :=
        fun a a' => ih d₁ d₁' hd₁ r₁ hs₁ _ _ a a'
      have htrR : ((if (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).2
            = (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').2 then (1 : ℂ) else 0))
          = (if (r₁.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).2)
              = (r₁.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').2)
              then (1 : ℂ) else 0) := by
        by_cases hc : (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).2
            = (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').2
        · rw [ite_eq_left hc, ite_eq_left (by rw [hc])]
        · rw [ite_eq_right hc, ite_eq_right (fun hcon =>
            hc (MixedEqv.transport_inj r₁ hndR hndR' hcon))]
      have htrL : ((if (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1
            = (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1 then (1 : ℂ) else 0))
          = (if (r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1)
              = (r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1)
              then (1 : ℂ) else 0) := by
        by_cases hc : (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1
            = (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1
        · rw [ite_eq_left hc, ite_eq_left (by rw [hc])]
        · rw [ite_eq_right hc, ite_eq_right (fun hcon =>
            hc (MixedEqv.transport_inj r₀ hndL hndL' hcon))]
      have hfstτ : (MixedEqv.transport (r := MixedEqv.mtry h₀ h₁ r₀ r₁) τ).split.1
          = r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1 :=
        congrArg Prod.fst
          (MixedEqv.transport_mtry_split (hW₁ := hW₁) (hW₂ := hW₂) h₀ h₁ r₀ r₁ τ)
      have hsndτ : (MixedEqv.transport (r := MixedEqv.mtry h₀ h₁ r₀ r₁) τ).split.2
          = r₁.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).2 :=
        congrArg Prod.snd
          (MixedEqv.transport_mtry_split (hW₁ := hW₁) (hW₂ := hW₂) h₀ h₁ r₀ r₁ τ)
      have hfstτ' : (MixedEqv.transport (r := MixedEqv.mtry h₀ h₁ r₀ r₁) τ').split.1
          = r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1 :=
        congrArg Prod.fst
          (MixedEqv.transport_mtry_split (hW₁ := hW₁) (hW₂ := hW₂) h₀ h₁ r₀ r₁ τ')
      have hsndτ' : (MixedEqv.transport (r := MixedEqv.mtry h₀ h₁ r₀ r₁) τ').split.2
          = r₁.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').2 :=
        congrArg Prod.snd
          (MixedEqv.transport_mtry_split (hW₁ := hW₁) (hW₂ := hW₂) h₀ h₁ r₀ r₁ τ')
      have hsumEq : ((Value.enum Ti).map fun w =>
          mixedAmplitude d₀ (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1
            (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1 w w).sum
          = ((Value.enum Ti).map fun w =>
              mixedAmplitude d₀' (r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ).1)
                (r₀.transport (Valuation.split (Γ := Δ₀) (Δ := Δ₁) τ').1) w w).sum :=
        congrArg List.sum (List.map_congr_left fun w _ => e₀ w w)
      simp only [mixedAmplitude]
      rw [hfstτ, hsndτ, hfstτ', hsndτ', htrR, htrL,
        e₀ v v', e₁ v v', hsumEq]
  | @hpair Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' _ _ T₀ T₁ hW₁ hW₂ hΔ h₀ h₁ d₀ d₁ d₀' d₁' r₀ r₁ _ _ =>
      intro hsum hshared
      have hs : MixedEqv.Shared r₀ ∧ MixedEqv.Shared r₁ ∧
          (∀ (a : Valuation Δ) (b : Valuation Δ₀),
            r₀.transport (a.append b)
              = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
          (∀ (a : Valuation Δ) (b : Valuation Δ₁),
            r₁.transport (a.append b)
              = (a.reorder hΔ.symm).append (b.reorder h₁.symm)) := hshared
      obtain ⟨hs₀, hs₁, hcomp₀, hcomp₁⟩ :=
        (hshared : MixedEqv.Shared r₀ ∧ MixedEqv.Shared r₁ ∧
          (∀ (a : Valuation Δ) (b : Valuation Δ₀),
            r₀.transport (a.append b)
              = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
          (∀ (a : Valuation Δ) (b : Valuation Δ₁),
            r₁.transport (a.append b)
              = (a.reorder hΔ.symm).append (b.reorder h₁.symm)))
      intro τ τ' v v'
      have hd₀ : d₀.depth + d₀'.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum
        have m₁ := Nat.le_max_left d₀.depth d₁.depth
        have m₂ := Nat.le_max_left d₀'.depth d₁'.depth
        omega
      have hd₁ : d₁.depth + d₁'.depth ≤ n := by
        simp only [MixedDerivation.depth] at hsum
        have m₁ := Nat.le_max_right d₀.depth d₁.depth
        have m₂ := Nat.le_max_right d₀'.depth d₁'.depth
        omega
      have e₀ : ∀ (a a' : Value T₀),
          mixedAmplitude d₀ (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1
              (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1 a a'
          = mixedAmplitude d₀' (r₀.transport (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1)
              (r₀.transport (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1) a a' :=
        fun a a' => ih d₀ d₀' hd₀ r₀ hs₀ _ _ a a'
      have e₁ : ∀ (a a' : Value T₁),
          mixedAmplitude d₁ (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
              (Γ := Δ) (Δ := Δ₀)).1.append
            (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2)
          (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1.split
              (Γ := Δ) (Δ := Δ₀)).1.append
            (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').2) a a'
          = mixedAmplitude d₁' (r₁.transport (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
              (Γ := Δ) (Δ := Δ₀)).1.append
            (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2))
              (r₁.transport (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1.split
              (Γ := Δ) (Δ := Δ₀)).1.append
            (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').2)) a a' :=
        fun a a' => ih d₁ d₁' hd₁ r₁ hs₁ _ _ a a'
      have key₀ : r₀.transport (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1
          = ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).2.reorder h₀.symm) :=
        Eq.trans (congrArg r₀.transport
          (Valuation.split_append_inv Δ Δ₀
            (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1))
          (hcomp₀ _ _)
      have key₀' : r₀.transport (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1
          = ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1).2.reorder h₀.symm) :=
        Eq.trans (congrArg r₀.transport
          (Valuation.split_append_inv Δ Δ₀
            (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1))
          (hcomp₀ _ _)
      have key₁ : r₁.transport (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
              (Γ := Δ) (Δ := Δ₀)).1.append
            (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2)
          = ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2.reorder h₁.symm) :=
        hcomp₁ _ _
      have key₁' : r₁.transport (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1.split
              (Γ := Δ) (Δ := Δ₀)).1.append
            (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').2)
          = ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').1).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ').2.reorder h₁.symm) :=
        hcomp₁ _ _
      simp only [mixedAmplitude]
      rw [Valuation.pair_first_split hW₁ τ, Valuation.pair_second_split hW₁ τ,
        Valuation.pair_first_split hW₁ τ', Valuation.pair_second_split hW₁ τ',
        Valuation.pair_first_split hW₂
          (MixedEqv.transport (r := MixedEqv.pair hΔ h₀ h₁ r₀ r₁) τ),
        Valuation.pair_second_split hW₂
          (MixedEqv.transport (r := MixedEqv.pair hΔ h₀ h₁ r₀ r₁) τ),
        Valuation.pair_first_split hW₂
          (MixedEqv.transport (r := MixedEqv.pair hΔ h₀ h₁ r₀ r₁) τ'),
        Valuation.pair_second_split hW₂
          (MixedEqv.transport (r := MixedEqv.pair hΔ h₀ h₁ r₀ r₁) τ')]
      simp only [MixedEqv.transport, Valuation.split_append]
      rw [e₀ v.unpair.1 (Value.unpair v').1,
        e₁ v.unpair.2 (Value.unpair v').2,
        key₀, key₀', key₁, key₁']
  | @hmixPair Δ Δ₀ Δ₁ Δs Δ₀s Δ₁s e₀ e₁ T₀ T₁ hWs hW hW₀s hW₁s dp₀ dp₁
      hΔ h₀ h₁ d₀ d₁ r₀ r₁ _ _ =>
      intro hsum hshared
      obtain ⟨hs₀, hs₁, hcomp₀, hcomp₁⟩ :=
        (hshared : MixedEqv.Shared r₀ ∧ MixedEqv.Shared r₁ ∧
          (∀ (a : Valuation Δs) (b : Valuation Δ₀s),
            r₀.transport (a.append b)
              = (a.reorder hΔ.symm).append (b.reorder h₀.symm)) ∧
          (∀ (a : Valuation Δs) (b : Valuation Δ₁s),
            r₁.transport (a.append b)
              = (a.reorder hΔ.symm).append (b.reorder h₁.symm)))
      intro τ τ' v v'
      have hd₀ : (MixedDerivation.hasTypeMix hW₀s dp₀).depth + d₀.depth ≤ n := by
        simp only [MixedDerivation.depth, PureDerivation.depth] at hsum ⊢
        have m₁ := Nat.le_max_left dp₀.depth dp₁.depth
        have m₂ := Nat.le_max_left d₀.depth d₁.depth
        omega
      have hd₁ : (MixedDerivation.hasTypeMix hW₁s dp₁).depth + d₁.depth ≤ n := by
        simp only [MixedDerivation.depth, PureDerivation.depth] at hsum ⊢
        have m₁ := Nat.le_max_right dp₀.depth dp₁.depth
        have m₂ := Nat.le_max_right d₀.depth d₁.depth
        omega
      have e₀ : ∀ (a a' : Value T₀),
          mixedAmplitude (.hasTypeMix hW₀s dp₀) (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).1.append ((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).2)
            (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.append ((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).2) a a'
          = mixedAmplitude d₀ ((((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).1.reorder hΔ.symm).append (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).2.reorder h₀.symm))
              ((((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.reorder hΔ.symm).append (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).2.reorder h₀.symm)) a a' := by
        intro a a'
        have h := ih (.hasTypeMix hW₀s dp₀) d₀ hd₀ r₀ hs₀ (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).1.append ((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).2) (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.append ((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).2) a a'
        rw [hcomp₀] at h
        have h2 : r₀.transport (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.append ((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).2)
            = (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.reorder hΔ.symm).append (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).2.reorder h₀.symm) := hcomp₀ _ _
        rw [h2] at h
        exact h
      have e₁ : ∀ (a a' : Value T₁),
          mixedAmplitude (.hasTypeMix hW₁s dp₁) (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).1.append (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).2)
            (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.append (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').2) a a'
          = mixedAmplitude d₁ ((((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).2.reorder h₁.symm))
              ((((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').2.reorder h₁.symm)) a a' := by
        intro a a'
        have h := ih (.hasTypeMix hW₁s dp₁) d₁ hd₁ r₁ hs₁ (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1.split (Γ := Δs) (Δ := Δ₀s)).1.append (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).2) (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.append (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').2) a a'
        rw [hcomp₁] at h
        have h2 : r₁.transport (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.append (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').2)
            = (((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1.split (Γ := Δs) (Δ := Δ₀s)).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').2.reorder h₁.symm) := hcomp₁ _ _
        rw [h2] at h
        exact h
      simp only [mixedAmplitude, pureAmplitude]
      rw [Valuation.pair_first_split hWs τ, Valuation.pair_second_split hWs τ,
        Valuation.pair_first_split hWs τ', Valuation.pair_second_split hWs τ',
        Valuation.pair_first_split hW
          (MixedEqv.transport (r := MixedEqv.mixPair hΔ h₀ h₁ r₀ r₁) τ),
        Valuation.pair_second_split hW
          (MixedEqv.transport (r := MixedEqv.mixPair hΔ h₀ h₁ r₀ r₁) τ),
        Valuation.pair_first_split hW
          (MixedEqv.transport (r := MixedEqv.mixPair hΔ h₀ h₁ r₀ r₁) τ'),
        Valuation.pair_second_split hW
          (MixedEqv.transport (r := MixedEqv.mixPair hΔ h₀ h₁ r₀ r₁) τ')]
      simp only [MixedEqv.transport, Valuation.split_append]
      rw [Valuation.split_append_inv Δs Δ₀s
            (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ).1,
          Valuation.split_append_inv Δs Δ₀s
            (Valuation.split (Γ := Δs ++ Δ₀s) (Δ := Δ₁s) τ').1]
      simp only [Valuation.split_append]
      rw [← e₀ (Value.unpair v).1 (Value.unpair v').1,
        ← e₁ (Value.unpair v).2 (Value.unpair v').2]
      simp only [mixedAmplitude]
      rw [star_mul]
      ring

  | @hmixApp Δd Δ e f T T' hWd dp₀ df de r' _ =>
      intro hsum hshared
      have hs : MixedEqv.Shared r' := hshared
      intro τ τ' v v'
      have hd : (MixedDerivation.hasTypeMix hWd dp₀).depth + de.depth ≤ n := by
        simp only [MixedDerivation.depth, PureDerivation.depth] at hsum ⊢
        omega
      have hEq : ∀ (a a' : Value T),
          mixedAmplitude de (r'.transport τ) (r'.transport τ') a a'
            = mixedAmplitude (.hasTypeMix hWd dp₀) τ τ' a a' :=
        fun a a' => (ih (.hasTypeMix hWd dp₀) de hd r' hs τ τ' a a').symm
      simp only [mixedAmplitude, pureAmplitude, programAmplitude,
        MixedEqv.transport, hEq]
      rw [List.sum_mul_star_sum (Value.enum T)
        (fun w => programAmplitude df w v *
          pureAmplitude dp₀ Valuation.nil τ w)
        (fun w' => programAmplitude df w' v' *
          pureAmplitude dp₀ Valuation.nil τ' w')]
      congr 1
      apply List.map_congr_left
      intro a _
      congr 1
      apply List.map_congr_left
      intro b _
      rw [star_mul]
      ring
/-! ### Pure uniqueness -/

/-- Base case: depth-zero pure proofs are the leaf rules. -/
theorem pureUnique_base : PureUniqueAt 0 := by
  intro Γ₁ Δ₁ Γ₂ Δ₂ e₁ e₂ T d₁ d₂ hsum r _hs σ₁ τ₁ v
  induction r using PureEqv.induct with
  | @hunit Γ₁ Γ₂ hW₁ hW₂ hΓ =>
      simp only [PureEqv.transport]
      cases τ₁
      cases v
      unfold pureAmplitude
      rfl
  | @hcvar Γa₁ Γb₁ Γa₂ Γb₂ x T hW₁ hW₂ hΓ =>
      simp only [PureEqv.transport, pureAmplitude]
      have hx₁ : (x, T) ∈ Γa₁ ++ [(x, T)] ++ Γb₁ :=
        List.mem_append_left Γb₁
          (List.mem_append_right Γa₁ (List.mem_singleton_self (x, T)))
      have hx₂ : (x, T) ∈ Γa₂ ++ [(x, T)] ++ Γb₂ :=
        List.mem_append_left Γb₂
          (List.mem_append_right Γa₂ (List.mem_singleton_self (x, T)))
      have his₁ : (Valuation.lookup σ₁ x T).isSome = true :=
        Valuation.lookup_isSome σ₁ hx₁
      have his₂ : (Valuation.lookup (σ₁.reorder hΓ.symm) x T).isSome = true :=
        Valuation.lookup_isSome _ hx₂
      have hlook : Valuation.lookup σ₁ x T
          = Valuation.lookup (σ₁.reorder hΓ.symm) x T :=
        (Valuation.lookup_reorder (h := hΓ.symm) (σ := σ₁) hx₂ hx₁).symm
      have hget : (Valuation.lookup σ₁ x T).get his₁
          = (Valuation.lookup (σ₁.reorder hΓ.symm) x T).get his₂ := by
        have hs : some ((Valuation.lookup σ₁ x T).get his₁)
            = some ((Valuation.lookup (σ₁.reorder hΓ.symm) x T).get his₂) := by
          rw [option_some_get_eq _ his₁, option_some_get_eq _ his₂, hlook]
        injection hs
      rw [hget]
  | @hqvar Γ₁ Γ₂ x T hW₁ hW₂ hx₁ hx₂ hΓ =>
      simp only [PureEqv.transport, pureAmplitude]
  | @hpurePair Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' e₀ e₁ T₀ T₁ hWΓ₁ hWΓ₂ hWΔ₁ hWΔ₂ hΓ hΔ
      h₀ h₁ d₀ d₁ d₀' d₁' r₀ r₁ ih₀ ih₁ =>
      simp only [PureDerivation.depth] at hsum
      omega
  | @hctrl Γ₁ Γ₁' Δ₁ Δ₁' G₂ G₂' D₂ D₂' e T T' l₁ l₂ hW₁ hW₂ hl hΓ hΓ' hΔ hΔ'
      dMix₁ dMix₂ r hO₁ hO₂ hE₁ hE₂ dB₁ dB₂ rb =>
      simp only [PureDerivation.depth] at hsum
      omega
  | @hpureApp Γ₁ Δ₁ Γ₂ Δ₂ e f T T' df₁ df₂ de₁ de₂ hΓ hΔ hprog r ih =>
      simp only [PureDerivation.depth] at hsum
      omega
  | @hpermL Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Δ₂ e T hWΓ hWΔ d₁ d₂ hΓ hΔ r ih =>
      simp only [PureDerivation.depth] at hsum
      omega
  | @hpermR Γ₁ Δ₁ Γ₂ Γ₂' Δ₂ Δ₂' e T hWΓ hWΔ d₁ d₂ r hΓ hΔ ih =>
      simp only [PureDerivation.depth] at hsum
      omega

/-- **Successor step** for pure uniqueness.  The `ctrl` arm is where the
refinement pays off: the recorded mixed equivalence transports the control
valuation exactly as the `Shared` condition prescribes, and the branch
equivalence applies at the frame reorder; the `purePair` arm mirrors the
mixed pair arm, with the reassociation handled by the same
`pair_first_split`/`pair_second_split` lemmas. -/
theorem pureUnique_step {n : Nat} (mixedIH : MixedUnique n)
    (branchIH : BranchUniqueAt n) : PureUniqueAt (n + 1) := by
  intro Γ₁ Δ₁ Γ₂ Δ₂ e₁ e₂ T d₁ d₂ hsum r hs
  revert hs
  revert hsum
  induction r using PureEqv.induct with
  | @hunit Γ₁ Γ₂ hW₁ hW₂ hΓ =>
      intro hsum _hs σ τ v
      simp only [PureEqv.transport]
      cases τ
      cases v
      unfold pureAmplitude
      rfl
  | @hcvar Γa₁ Γb₁ Γa₂ Γb₂ x T hW₁ hW₂ hΓ =>
      intro hsum _hs σ τ v
      simp only [PureEqv.transport, pureAmplitude]
      have hx₁ : (x, T) ∈ Γa₁ ++ [(x, T)] ++ Γb₁ :=
        List.mem_append_left Γb₁
          (List.mem_append_right Γa₁ (List.mem_singleton_self (x, T)))
      have hx₂ : (x, T) ∈ Γa₂ ++ [(x, T)] ++ Γb₂ :=
        List.mem_append_left Γb₂
          (List.mem_append_right Γa₂ (List.mem_singleton_self (x, T)))
      have his₁ : (Valuation.lookup σ x T).isSome = true :=
        Valuation.lookup_isSome σ hx₁
      have his₂ : (Valuation.lookup (σ.reorder hΓ.symm) x T).isSome = true :=
        Valuation.lookup_isSome _ hx₂
      have hlook : Valuation.lookup σ x T
          = Valuation.lookup (σ.reorder hΓ.symm) x T :=
        (Valuation.lookup_reorder (h := hΓ.symm) (σ := σ) hx₂ hx₁).symm
      have hget : (Valuation.lookup σ x T).get his₁
          = (Valuation.lookup (σ.reorder hΓ.symm) x T).get his₂ := by
        have hs : some ((Valuation.lookup σ x T).get his₁)
            = some ((Valuation.lookup (σ.reorder hΓ.symm) x T).get his₂) := by
          rw [option_some_get_eq _ his₁, option_some_get_eq _ his₂, hlook]
        injection hs
      rw [hget]
  | @hqvar Γ₁ Γ₂ x T hW₁ hW₂ hx₁ hx₂ hΓ =>
      intro hsum _hs σ τ v
      simp only [PureEqv.transport, pureAmplitude]
  | @hpurePair Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ' Δ₀' Δ₁' e₀ e₁ T₀ T₁ hWΓ₁ hWΓ₂ hWΔ₁ hWΔ₂ hΓ
      hΔ h₀ h₁ d₀ d₁ d₀' d₁' r₀ r₁ ih₀ ih₁ =>
      intro hsum hshared σ τ v
      obtain ⟨hs₀, hs₁, hcomp₀, hcomp₁⟩ :=
        (hshared : PureEqv.Shared r₀ ∧ PureEqv.Shared r₁ ∧
          (∀ (σ : Valuation Γ₁) (τ : Valuation (Δ ++ Δ₀ ++ Δ₁)),
            r₀.transport σ (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1
              = (σ.reorder hΓ.symm,
                ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).2.reorder h₀.symm))) ∧
          (∀ (σ : Valuation Γ₁) (τ : Valuation (Δ ++ Δ₀ ++ Δ₁)),
            r₁.transport σ (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
              (Γ := Δ) (Δ := Δ₀)).1.append (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2)
              = (σ.reorder hΓ.symm,
                ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2.reorder h₁.symm))))
      have hd₀ : d₀.depth + d₀'.depth ≤ n := by
        simp only [PureDerivation.depth] at hsum
        have m₁ := Nat.le_max_left d₀.depth d₁.depth
        have m₂ := Nat.le_max_left d₀'.depth d₁'.depth
        omega
      have hd₁ : d₁.depth + d₁'.depth ≤ n := by
        simp only [PureDerivation.depth] at hsum
        have m₁ := Nat.le_max_right d₀.depth d₁.depth
        have m₂ := Nat.le_max_right d₀'.depth d₁'.depth
        omega
      have e₀ : ∀ (a : Value T₀),
          pureAmplitude d₀ σ (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1 a
          = pureAmplitude d₀' (σ.reorder hΓ.symm)
              (((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).2.reorder h₀.symm)) a := by
        intro a
        have h : pureAmplitude d₀ σ
              (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1 a
            = pureAmplitude d₀'
              (r₀.transport σ (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).1
              (r₀.transport σ (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).2 a :=
          ih₀ (by omega) hs₀ σ _ a
        rw [hcomp₀ σ τ] at h
        exact h
      have e₁ : ∀ (a : Value T₁),
          pureAmplitude d₁ σ (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
              (Γ := Δ) (Δ := Δ₀)).1.append (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2) a
          = pureAmplitude d₁' (σ.reorder hΓ.symm)
              (((Valuation.split (Γ := Δ) (Δ := Δ₀) (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1).1.reorder hΔ.symm).append ((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2.reorder h₁.symm)) a := by
        intro a
        have h : pureAmplitude d₁ σ
              (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
                (Γ := Δ) (Δ := Δ₀)).1.append
              (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2) a
            = pureAmplitude d₁'
              (r₁.transport σ (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
                (Γ := Δ) (Δ := Δ₀)).1.append
              (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2)).1
              (r₁.transport σ (((Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).1.split
                (Γ := Δ) (Δ := Δ₀)).1.append
              (Valuation.split (Γ := Δ ++ Δ₀) (Δ := Δ₁) τ).2)).2 a :=
          ih₁ (by omega) hs₁ σ _ a
        rw [hcomp₁ σ τ] at h
        exact h
      simp only [pureAmplitude, PureEqv.transport]
      rw [Valuation.pair_first_split hWΔ₁ τ, Valuation.pair_second_split hWΔ₁ τ,
        Valuation.pair_first_split hWΔ₂,
        Valuation.pair_second_split hWΔ₂]
      simp only [Valuation.split_append]
      rw [e₀ (Value.unpair v).1, e₁ (Value.unpair v).2]
  | @hctrl Γ₁ Γ₁' Δ₁ Δ₁' G₂ G₂' D₂ D₂' e T T' l₁ l₂ hW₁ hW₂ hl hΓ hΓ' hΔ hΔ'
      dMix₁ dMix₂ r hO₁ hO₂ hE₁ hE₂ dB₁ dB₂ rb =>
      intro hsum hshared σ τ v
      obtain ⟨hr, hrb, hctrlcomp⟩ :=
        (hshared : MixedEqv.Shared r ∧ BranchEqv.Shared rb ∧
          (∀ (σ : Valuation (Γ₁ ++ Γ₁')) (τ : Valuation (Δ₁ ++ Δ₁')),
            r.transport
                ((Valuation.split (Γ := Γ₁) (Δ := Γ₁') σ).1.append
                  (Valuation.split (Γ := Δ₁) (Δ := Δ₁') τ).1)
              = ((Valuation.split (Γ := G₂) (Δ := G₂')
                  (σ.reorder (hΓ.append hΓ').symm)).1).append
                ((Valuation.split (Γ := D₂) (Δ := D₂')
                  (τ.reorder (hΔ.append hΔ').symm)).1)))
      have hdm : dMix₁.depth + dMix₂.depth ≤ n := by
        simp only [PureDerivation.depth] at hsum
        have m₁ := Nat.le_max_left dMix₁.depth dB₁.depth
        have m₂ := Nat.le_max_left dMix₂.depth dB₂.depth
        omega
      have hdb : dB₁.depth + dB₂.depth ≤ n := by
        simp only [PureDerivation.depth] at hsum
        have m₁ := Nat.le_max_right dMix₁.depth dB₁.depth
        have m₂ := Nat.le_max_right dMix₂.depth dB₂.depth
        omega
      have hprob : ∀ u : Value T,
          mixedAmplitude dMix₁
              ((Valuation.split (Γ := Γ₁) (Δ := Γ₁') σ).1.append
                (Valuation.split (Γ := Δ₁) (Δ := Δ₁') τ).1)
              ((Valuation.split (Γ := Γ₁) (Δ := Γ₁') σ).1.append
                (Valuation.split (Γ := Δ₁) (Δ := Δ₁') τ).1) u u
          = mixedAmplitude dMix₂
              (((Valuation.split (Γ := G₂) (Δ := G₂')
                  (σ.reorder (hΓ.append hΓ').symm)).1).append
                ((Valuation.split (Γ := D₂) (Δ := D₂')
                  (τ.reorder (hΔ.append hΔ').symm)).1))
              (((Valuation.split (Γ := G₂) (Δ := G₂')
                  (σ.reorder (hΓ.append hΓ').symm)).1).append
                ((Valuation.split (Γ := D₂) (Δ := D₂')
                  (τ.reorder (hΔ.append hΔ').symm)).1)) u u := by
        intro u
        have h := mixedIH dMix₁ dMix₂ hdm r hr
          ((Valuation.split (Γ := Γ₁) (Δ := Γ₁') σ).1.append
            (Valuation.split (Γ := Δ₁) (Δ := Δ₁') τ).1)
          ((Valuation.split (Γ := Γ₁) (Δ := Γ₁') σ).1.append
            (Valuation.split (Γ := Δ₁) (Δ := Δ₁') τ).1) u u
        rw [hctrlcomp σ τ] at h
        exact h
      simp only [pureAmplitude, PureEqv.transport]
      exact branchIH hΓ hΓ' hΔ hΔ' dB₁ dB₂ rb hrb hdb _ _ hprob σ τ v
  | @hpureApp Γ₁ Δ₁ Γ₂ Δ₂ e f T T' df₁ df₂ de₁ de₂ hΓ hΔ hprog r ih =>
      intro hsum hshared σ τ v
      obtain ⟨hr, hcomp⟩ :=
        (hshared : PureEqv.Shared r ∧
          (∀ (σ : Valuation Γ₁) (τ : Valuation Δ₁),
            r.transport σ τ = (σ.reorder hΓ.symm, τ.reorder hΔ.symm)))
      have hde : de₁.depth + de₂.depth ≤ n := by
        simp only [PureDerivation.depth] at hsum
        have m₁ := Nat.le_max_right df₁.depth de₁.depth
        have m₂ := Nat.le_max_right df₂.depth de₂.depth
        omega
      simp only [pureAmplitude, PureEqv.transport]
      refine congrArg List.sum (List.map_congr_left fun w _ => ?_)
      rw [hprog, ih (by omega) hr σ τ w, hcomp σ τ]
  | @hpermL Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Δ₂ e T hWΓ hWΔ d₁ d₂ hΓ hΔ r ih =>
      intro hsum hshared σ τ v
      have hinner : d₁.depth + d₂.depth ≤ n + 1 := by
        simp only [PureDerivation.depth] at hsum
        omega
      simp only [PureEqv.transport, pureAmplitude]
      exact ih hinner hshared (σ.reorder hΓ) (τ.reorder hΔ) v
  | @hpermR Γ₁ Δ₁ Γ₂ Γ₂' Δ₂ Δ₂' e T hWΓ hWΔ d₁ d₂ r hΓ hΔ ih =>
      intro hsum hshared σ τ v
      have hinner : d₁.depth + d₂.depth ≤ n + 1 := by
        simp only [PureDerivation.depth] at hsum
        omega
      have hndΓ₂ : Γ₂.Nodup :=
        List.Nodup.of_append_left
          (HasPureType.context_well_formed d₂.toProp).nodup
      have hndΔ₂ : Δ₂.Nodup :=
        List.Nodup.of_append_right
          (HasPureType.context_well_formed d₂.toProp).nodup
      have hrrΓ : ∀ σ : Valuation Γ₂,
          ((σ.reorder hΓ.symm).reorder hΓ) = σ :=
        fun σ => Valuation.reorder_reorder (h := hΓ.symm) hndΓ₂ σ
      have hrrΔ : ∀ τ : Valuation Δ₂,
          ((τ.reorder hΔ.symm).reorder hΔ) = τ :=
        fun τ => Valuation.reorder_reorder (h := hΔ.symm) hndΔ₂ τ
      simp only [PureEqv.transport, pureAmplitude]
      rw [hrrΓ (PureEqv.transport r σ τ).1, hrrΔ (PureEqv.transport r σ τ).2]
      exact ih hinner hshared σ τ v


/-! ## The strengthened uniqueness statement -/

/-- Reindex a sum over `Valuation.enum` along a permutation of contexts.

If `f₁` on `Δ₁` corresponds to `f₂` on `Δ₂` under reordering along `h`
(assumption `hf`), the two sums agree.  This is the workhorse for all the
`enum`-summed program amplitudes (`hasCoherentTypeAbs`, `hasTypeRphase`,
`hasChannelTypeAbs`). -/
theorem List.sum_map_enum_perm {Δ₁ Δ₂ : Context} (h : List.Perm Δ₁ Δ₂)
    (hnd₂ : Δ₂.Nodup)
    (f₁ : Valuation Δ₁ → ℂ) (f₂ : Valuation Δ₂ → ℂ)
    (hf : ∀ τ : Valuation Δ₂, f₁ (τ.reorder h) = f₂ τ) :
    ((Valuation.enum Δ₁).map f₁).sum = ((Valuation.enum Δ₂).map f₂).sum := by
  have hnd₁ : Δ₁.Nodup := h.nodup_iff.mpr hnd₂
  have hp := Valuation.enum_map_reorder_perm h hnd₂
  have hsum := (hp.map f₂).sum_eq
  rw [List.map_map] at hsum
  have hcongr : (f₂ ∘ fun τ₁ : Valuation Δ₁ => τ₁.reorder h.symm) = f₁ := by
    funext τ₁
    have hrr := Valuation.reorder_reorder (h := h.symm) hnd₁ τ₁
    calc f₂ (τ₁.reorder h.symm)
        = f₁ ((τ₁.reorder h.symm).reorder h) := (hf _).symm
      _ = f₁ τ₁ := by rw [hrr]
  rw [hcongr] at hsum
  exact hsum

/-! ### Branch uniqueness -/

/-- Base case: branch lists of depth zero are empty on both sides. -/
theorem branchUnique_base : BranchUniqueAt 0 := by
  intro Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' l₁ l₂ T T'
    hΓ hΓ' hΔ hΔ' b₁ b₂ rb _hs hsum prob₁ prob₂ hprob σ₁ τ₁ v
  cases rb
  · simp only [branchAmplitude]
  · simp only [BranchDerivation.depth] at hsum
    omega

/-- **Successor step** for branch uniqueness.  The `cons` case reindexes the
per-branch classical-context enumeration along the pattern equivalence's
recorded permutation (`PureEqv.transport_nil_eq` turns the transport into
that reorder) and uses the body equivalence at the merged valuation, where
the `Shared` condition matches the frame transport. -/
theorem branchUnique_step {n : Nat} (pureIH : PureUniqueAt n)
    (_ : BranchUniqueAt n) : BranchUniqueAt (n + 1) := by
  intro Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' l₁ l₂ T T'
    hΓ hΓ' hΔ hΔ' b₁ b₂ rb hs hsum
  revert hs
  revert hsum
  induction rb using BranchEqv.induct with
  | @hnil Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' T T' hΓ hΓ' hΔ hΔ' =>
      intro _hs hsum prob₁ prob₂ hprob σ τ v
      simp only [branchAmplitude]
  | @hcons Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' hΓ hΓ' hΔ hΔ' T T' Γⱼ₁ Γⱼ₂ eⱼ eⱼ' l₁ l₂
      dPat₁ dPat₂ dBody₁ dBody₂ b₁ b₂ hp hb rt ihrt =>
      intro hsum hshared prob₁ prob₂ hprob σ τ v
      obtain ⟨hsp, hsb, hsrt, hcond⟩ :=
        (hshared : PureEqv.Shared hp ∧ PureEqv.Shared hb ∧
          BranchEqv.Shared rt ∧
            (∀ (σ : Valuation (Γ₁ ++ Γ₁')) (τ : Valuation (Δ₁ ++ Δ₁'))
                (σⱼ : Valuation Γⱼ₁),
              hb.transport (σ.append σⱼ) τ
                = ((σ.reorder (hΓ.append hΓ').symm).append
                    (σⱼ.reorder (hp.τPerm).symm),
                  τ.reorder (hΔ.append hΔ').symm)))
      have hpat : dPat₁.depth + dPat₂.depth ≤ n := by
        simp only [BranchDerivation.depth] at hsum
        have m₁ := Nat.le_max_left (max dPat₁.depth dBody₁.depth) b₁.depth
        have m₂ := Nat.le_max_left (max dPat₂.depth dBody₂.depth) b₂.depth
        have m₃ := Nat.le_max_left dPat₁.depth dBody₁.depth
        have m₄ := Nat.le_max_left dPat₂.depth dBody₂.depth
        omega
      have hbody : dBody₁.depth + dBody₂.depth ≤ n := by
        simp only [BranchDerivation.depth] at hsum
        have m₁ := Nat.le_max_left (max dPat₁.depth dBody₁.depth) b₁.depth
        have m₂ := Nat.le_max_left (max dPat₂.depth dBody₂.depth) b₂.depth
        have m₃ := Nat.le_max_right dPat₁.depth dBody₁.depth
        have m₄ := Nat.le_max_right dPat₂.depth dBody₂.depth
        omega
      have htail : b₁.depth + b₂.depth ≤ n := by
        simp only [BranchDerivation.depth] at hsum
        have m₁ := Nat.le_max_right (max dPat₁.depth dBody₁.depth) b₁.depth
        have m₂ := Nat.le_max_right (max dPat₂.depth dBody₂.depth) b₂.depth
        omega
      have hptr := PureEqv.transport_nil_eq hp
      have hndΓⱼ₂ : Γⱼ₂.Nodup :=
        List.Nodup.of_append_right
          (HasPureType.context_well_formed dPat₂.toProp).nodup
      have hndΓⱼ₁ : Γⱼ₁.Nodup :=
        (hp.τPerm.nodup_iff.mpr hndΓⱼ₂)
      -- the tail equality
      have htailEq : branchAmplitude b₁ prob₁ σ τ v
          = branchAmplitude b₂ prob₂
              (σ.reorder (hΓ.append hΓ').symm)
              (τ.reorder (hΔ.append hΔ').symm) v :=
        ihrt (by omega) hsrt prob₁ prob₂ hprob σ τ v
      -- the per-branch enumeration sums agree
      have hinner : ∀ u : Value T,
          ((Valuation.enum Γⱼ₁).map fun σⱼ =>
              star (pureAmplitude dPat₁ Valuation.nil σⱼ u) *
                pureAmplitude dBody₁ (σ.append σⱼ) τ v).sum
            = ((Valuation.enum Γⱼ₂).map fun σⱼ₂ =>
                star (pureAmplitude dPat₂ Valuation.nil σⱼ₂ u) *
                  pureAmplitude dBody₂
                    ((σ.reorder (hΓ.append hΓ').symm).append σⱼ₂)
                    (τ.reorder (hΔ.append hΔ').symm) v).sum := by
        intro u
        refine List.sum_map_enum_perm (hp.τPerm) hndΓⱼ₂ _ _ ?_
        intro τ₂
        have hσⱼ := hptr (Valuation.reorder hp.τPerm τ₂)
        have hback : (τ₂.reorder hp.τPerm).reorder (hp.τPerm).symm = τ₂ :=
          Valuation.reorder_reorder (hp.τPerm) hndΓⱼ₂ τ₂
        have hpatAmp : pureAmplitude dPat₁ Valuation.nil
            (τ₂.reorder hp.τPerm) u
            = pureAmplitude dPat₂ Valuation.nil τ₂ u := by
          have h := pureIH dPat₁ dPat₂ hpat hp hsp Valuation.nil
            (τ₂.reorder hp.τPerm) u
          rw [hσⱼ] at h
          rw [h, hback]
        have hbodyAmp : pureAmplitude dBody₁
            (σ.append (τ₂.reorder hp.τPerm)) τ v
            = pureAmplitude dBody₂
                ((σ.reorder (hΓ.append hΓ').symm).append τ₂)
                (τ.reorder (hΔ.append hΔ').symm) v := by
          have h := pureIH dBody₁ dBody₂ hbody hb hsb
            (σ.append (τ₂.reorder hp.τPerm)) τ v
          rw [hcond σ τ (τ₂.reorder hp.τPerm)] at h
          rw [h, hback]
        rw [hpatAmp, hbodyAmp]
      -- the per-branch block sums agree
      have hhead : ((Value.enum T).map fun u =>
            prob₁ u * ((Valuation.enum Γⱼ₁).map fun σⱼ =>
              star (pureAmplitude dPat₁ Valuation.nil σⱼ u) *
                pureAmplitude dBody₁ (σ.append σⱼ) τ v).sum).sum
          = ((Value.enum T).map fun u =>
            prob₂ u * ((Valuation.enum Γⱼ₂).map fun σⱼ₂ =>
              star (pureAmplitude dPat₂ Valuation.nil σⱼ₂ u) *
                pureAmplitude dBody₂
                  ((σ.reorder (hΓ.append hΓ').symm).append σⱼ₂)
                  (τ.reorder (hΔ.append hΔ').symm) v).sum).sum :=
        congrArg List.sum (List.map_congr_left fun u _ => by
          rw [hprob u, hinner u])
      simp only [branchAmplitude, BranchEqv.transport]
      rw [hhead, htailEq]


/-- The classical contexts a program derivation ranges over.  Agreement of
this pair is the side condition of the `prog` field. -/
def programCtx {f : Program} {F : ProgramType}
    (d : ProgramDerivation f F) : Context × Context :=
  match d with
  | .hasTypeGate => ([], [])
  | .hasTypeLeft => ([], [])
  | .hasTypeRight => ([], [])
  | .hasCoherentTypeAbs (Δ := Δ) _ _ => (Δ, [])
  | .hasTypeRphase (Δ := Δ) _ => (Δ, [])
  | .hasTypeChannel d => programCtx d
  | .hasChannelTypeAbs (Δ := Δ) (Δ₀ := Δ₀) _ _ => (Δ, Δ₀)
termination_by structural d


/-! ### Program equivalences and uniqueness -/

/-- Equivalent program proofs: same program and type.  The context
decompositions chosen by the rules (`coherentAbs`/`rphase` record one
context, `channelAbs` records a two-way split) are related by recorded
permutations, and the pure/mixed/program sub-proofs carry their own
equivalences.

The paper's Appendix G also claims a cross case, T-Channel vs
T-MixedAbs.  Under the paper's own `Δ₀`-generalized T-MixedAbs rule (the
text after Figure 4 explicitly allows the pure sub-proof's context to
extend beyond the mixed one, with the extra variables *measured*), that
cross identity is false: for `λ(z ⊗ w) ↦ (x ⊗ y)`, both a channel proof
(channel of a coherent proof with shared-padded pair contexts) and a
channel-abs proof (with `Δ₀ = [z, w]`) exist, but the channel-of-coherent
composes the input dyad while the channel-abs measures the `Δ₀` part, and
the amplitudes differ by the resulting trace factor.  The refined
equivalence therefore does not relate those two proofs; the same-rule
cases below are all provable. -/
inductive ProgEqv : {f : Program} → {F : ProgramType} →
    ProgramDerivation f F → ProgramDerivation f F → Type where
  | gate {θ φ ρ : RealConstant} :
      ProgEqv (.hasTypeGate (θ := θ) (φ := φ) (ρ := ρ))
          (.hasTypeGate (θ := θ) (φ := φ) (ρ := ρ))
  | left {T₀ T₁ : DataType} : ProgEqv .hasTypeLeft .hasTypeLeft
  | right {T₀ T₁ : DataType} : ProgEqv .hasTypeRight .hasTypeRight
  | coherentAbs {Δ₁ Δ₂ : Context} {e e' : Expression} {T T' : DataType}
      {dp₁ : PureDerivation [] Δ₁ e T} {dq₁ : PureDerivation [] Δ₁ e' T'}
      {dp₂ : PureDerivation [] Δ₂ e T} {dq₂ : PureDerivation [] Δ₂ e' T'}
      (hΔ : List.Perm Δ₁ Δ₂) (rp : PureEqv dp₁ dp₂) (rq : PureEqv dq₁ dq₂) :
      ProgEqv (.hasCoherentTypeAbs dp₁ dq₁) (.hasCoherentTypeAbs dp₂ dq₂)
  | rphase {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
      {γ γ' : RealConstant}
      {dp₁ : PureDerivation [] Δ₁ e T} {dp₂ : PureDerivation [] Δ₂ e T}
      (hΔ : List.Perm Δ₁ Δ₂) (rp : PureEqv dp₁ dp₂) :
      ProgEqv (.hasTypeRphase (γ := γ) (γ' := γ') dp₁)
          (.hasTypeRphase (γ := γ) (γ' := γ') dp₂)
  | channel {f : Program} {T T' : DataType}
      {df₁ df₂ : ProgramDerivation f (T ⇝ T')} (r : ProgEqv df₁ df₂) :
      ProgEqv (.hasTypeChannel df₁) (.hasTypeChannel df₂)
  | channelAbs {Δ₁ Δ₀₁ Δ₂ Δ₀₂ : Context} {e e' : Expression}
      {T T' : DataType}
      {dp₁ : PureDerivation [] (Δ₁ ++ Δ₀₁) e T}
      {dm₁ : MixedDerivation Δ₁ e' T'}
      {dp₂ : PureDerivation [] (Δ₂ ++ Δ₀₂) e T}
      {dm₂ : MixedDerivation Δ₂ e' T'}
      (hΔ : List.Perm Δ₁ Δ₂) (hΔ₀ : List.Perm Δ₀₁ Δ₀₂)
      (rp : PureEqv dp₁ dp₂) (rm : MixedEqv dm₁ dm₂) :
      ProgEqv (.hasChannelTypeAbs dp₁ dm₁) (.hasChannelTypeAbs dp₂ dm₂)

/-- Compatibility for program equivalences: the pure and mixed witnesses
must transport exactly along the decomposition permutations recorded by
the enclosing rule. -/
def ProgEqv.Shared {f : Program} {F : ProgramType}
    {d₁ d₂ : ProgramDerivation f F} (r : ProgEqv d₁ d₂) : Prop :=
  match r with
  | .gate .. => True
  | .left .. => True
  | .right .. => True
  | @coherentAbs Δ₁ Δ₂ e e' T T' dp₁ dq₁ dp₂ dq₂ hΔ rp rq =>
      PureEqv.Shared rp ∧ PureEqv.Shared rq ∧
        (∀ τ : Valuation Δ₁,
          rp.transport Valuation.nil τ = (Valuation.nil, τ.reorder hΔ.symm)) ∧
        (∀ τ : Valuation Δ₁,
          rq.transport Valuation.nil τ = (Valuation.nil, τ.reorder hΔ.symm))
  | @rphase Δ₁ Δ₂ e T γ γ' dp₁ dp₂ hΔ rp =>
      PureEqv.Shared rp ∧
        (∀ τ : Valuation Δ₁,
          rp.transport Valuation.nil τ = (Valuation.nil, τ.reorder hΔ.symm))
  | .channel r' => Shared r'
  | @channelAbs Δ₁ Δ₀₁ Δ₂ Δ₀₂ e e' T T' dp₁ dm₁ dp₂ dm₂ hΔ hΔ₀ rp rm =>
      PureEqv.Shared rp ∧ MixedEqv.Shared rm ∧
        (∀ τ : Valuation Δ₁, rm.transport τ = τ.reorder hΔ.symm) ∧
        (∀ (τ : Valuation Δ₁) (τ₀ : Valuation Δ₀₁),
          rp.transport Valuation.nil (τ.append τ₀)
            = (Valuation.nil,
              (τ.reorder hΔ.symm).append (τ₀.reorder hΔ₀.symm)))

/-- Paper-faithful program uniqueness: equivalent program proofs compute
the same denotation. -/
abbrev ProgUniqueAt (n : Nat) : Prop :=
  ∀ {f : Program} {F : ProgramType} (d₁ d₂ : ProgramDerivation f F),
    d₁.depth + d₂.depth ≤ n → (r : ProgEqv d₁ d₂) → ProgEqv.Shared r →
    programAmplitude d₁ = programAmplitude d₂

/-- Base case: depth-zero program proofs are the leaf rules. -/
theorem progUnique_base : ProgUniqueAt 0 := by
  intro f F d₁ d₂ hsum r _hs
  revert _hs
  revert hsum
  induction r with
  | @gate θ φ ρ => intro _hsum _hs; rfl
  | @left T₀ T₁ => intro _hsum _hs; rfl
  | @right T₀ T₁ => intro _hsum _hs; rfl
  | @coherentAbs Δ₁ Δ₂ e e' T T' dp₁ dq₁ dp₂ dq₂ hΔ rp rq =>
      intro hsum _hs
      simp only [ProgramDerivation.depth] at hsum
      omega
  | @rphase Δ₁ Δ₂ e T γ γ' dp₁ dp₂ hΔ rp =>
      intro hsum _hs
      simp only [ProgramDerivation.depth] at hsum
      omega
  | @channel f T T' df₁ df₂ r ih =>
      intro hsum _hs
      simp only [ProgramDerivation.depth] at hsum
      omega
  | @channelAbs Δ₁ Δ₀₁ Δ₂ Δ₀₂ e e' T T' dp₁ dm₁ dp₂ dm₂ hΔ hΔ₀ rp rm =>
      intro hsum _hs
      simp only [ProgramDerivation.depth] at hsum
      omega

/-- **Successor step** for program uniqueness.  The `coherentAbs` and
`rphase` arms reindex their context enumerations along the recorded
permutation; the `channelAbs` arm reindexes all three levels and applies
the pure and mixed uniqueness layers through the `Shared` transport
agreements. -/
theorem progUnique_step {n : Nat} (pureIH : PureUniqueAt n)
    (mixedIH : MixedUnique n) : ProgUniqueAt (n + 1) := by
  intro f F d₁ d₂ hsum r hs
  revert hs
  revert hsum
  induction r with
  | @gate θ φ ρ => intro _hsum _hs; rfl
  | @left T₀ T₁ => intro _hsum _hs; rfl
  | @right T₀ T₁ => intro _hsum _hs; rfl
  | @coherentAbs Δ₁ Δ₂ e e' T T' dp₁ dq₁ dp₂ dq₂ hΔ rp rq =>
      intro hsum hshared
      obtain ⟨hrp, hrq, hcompP, hcompQ⟩ :=
        (hshared : PureEqv.Shared rp ∧ PureEqv.Shared rq ∧
          (∀ τ : Valuation Δ₁,
            rp.transport Valuation.nil τ = (Valuation.nil, τ.reorder hΔ.symm)) ∧
          (∀ τ : Valuation Δ₁,
            rq.transport Valuation.nil τ = (Valuation.nil, τ.reorder hΔ.symm)))
      have hdp : dp₁.depth + dp₂.depth ≤ n := by
        simp only [ProgramDerivation.depth] at hsum
        have m₁ := Nat.le_max_left dp₁.depth dq₁.depth
        have m₂ := Nat.le_max_left dp₂.depth dq₂.depth
        omega
      have hdq : dq₁.depth + dq₂.depth ≤ n := by
        simp only [ProgramDerivation.depth] at hsum
        have m₁ := Nat.le_max_right dp₁.depth dq₁.depth
        have m₂ := Nat.le_max_right dp₂.depth dq₂.depth
        omega
      have hnd₂ : Δ₂.Nodup :=
        List.Nodup.of_append_right
          (HasPureType.context_well_formed dp₂.toProp).nodup
      funext v w
      simp only [programAmplitude]
      refine List.sum_map_enum_perm hΔ hnd₂ _ _ ?_
      intro τ₂
      have hfP : (rp.transport Valuation.nil (τ₂.reorder hΔ)).1
          = (Valuation.nil : Valuation []) :=
        congrArg Prod.fst (hcompP (τ₂.reorder hΔ))
      have hsP : (rp.transport Valuation.nil (τ₂.reorder hΔ)).2
          = (τ₂.reorder hΔ).reorder hΔ.symm :=
        congrArg Prod.snd (hcompP (τ₂.reorder hΔ))
      have hfQ : (rq.transport Valuation.nil (τ₂.reorder hΔ)).1
          = (Valuation.nil : Valuation []) :=
        congrArg Prod.fst (hcompQ (τ₂.reorder hΔ))
      have hsQ : (rq.transport Valuation.nil (τ₂.reorder hΔ)).2
          = (τ₂.reorder hΔ).reorder hΔ.symm :=
        congrArg Prod.snd (hcompQ (τ₂.reorder hΔ))
      have h1 := pureIH dp₁ dp₂ hdp rp hrp Valuation.nil (τ₂.reorder hΔ) v
      rw [hfP, hsP, Valuation.reorder_reorder hΔ hnd₂ τ₂] at h1
      have h2 := pureIH dq₁ dq₂ hdq rq hrq Valuation.nil (τ₂.reorder hΔ) w
      rw [hfQ, hsQ, Valuation.reorder_reorder hΔ hnd₂ τ₂] at h2
      rw [h1, h2]
  | @rphase Δ₁ Δ₂ e T γ γ' dp₁ dp₂ hΔ rp =>
      intro hsum hshared
      obtain ⟨hrp, hcompP⟩ :=
        (hshared : PureEqv.Shared rp ∧
          (∀ τ : Valuation Δ₁,
            rp.transport Valuation.nil τ = (Valuation.nil, τ.reorder hΔ.symm)))
      have hdp : dp₁.depth + dp₂.depth ≤ n := by
        simp only [ProgramDerivation.depth] at hsum
        omega
      have hnd₂ : Δ₂.Nodup :=
        List.Nodup.of_append_right
          (HasPureType.context_well_formed dp₂.toProp).nodup
      funext v w
      simp only [programAmplitude]
      have hP : ((Valuation.enum Δ₁).map fun τ =>
            pureAmplitude dp₁ Valuation.nil τ w *
              star (pureAmplitude dp₁ Valuation.nil τ v)).sum
          = ((Valuation.enum Δ₂).map fun τ =>
              pureAmplitude dp₂ Valuation.nil τ w *
                star (pureAmplitude dp₂ Valuation.nil τ v)).sum := by
        refine List.sum_map_enum_perm hΔ hnd₂ _ _ ?_
        intro τ₂
        have hfP : (rp.transport Valuation.nil (τ₂.reorder hΔ)).1
            = (Valuation.nil : Valuation []) :=
          congrArg Prod.fst (hcompP (τ₂.reorder hΔ))
        have hsP : (rp.transport Valuation.nil (τ₂.reorder hΔ)).2
            = (τ₂.reorder hΔ).reorder hΔ.symm :=
          congrArg Prod.snd (hcompP (τ₂.reorder hΔ))
        have h1 := pureIH dp₁ dp₂ hdp rp hrp Valuation.nil (τ₂.reorder hΔ) w
        rw [hfP, hsP, Valuation.reorder_reorder hΔ hnd₂ τ₂] at h1
        have h2 := pureIH dp₁ dp₂ hdp rp hrp Valuation.nil (τ₂.reorder hΔ) v
        rw [hfP, hsP, Valuation.reorder_reorder hΔ hnd₂ τ₂] at h2
        rw [h1, h2]
      rw [hP]
  | @channel f T T' df₁ df₂ r ih =>
      intro hsum hshared
      have hdf : df₁.depth + df₂.depth ≤ n := by
        simp only [ProgramDerivation.depth] at hsum
        omega
      have key := ih (by omega) hshared
      funext v v' w w'
      simp only [programAmplitude]
      rw [key]
  | @channelAbs Δ₁ Δ₀₁ Δ₂ Δ₀₂ e e' T T' dp₁ dm₁ dp₂ dm₂ hΔ hΔ₀ rp rm =>
      intro hsum hshared
      obtain ⟨hrp, hrm, hcompM, hcompP⟩ :=
        (hshared : PureEqv.Shared rp ∧ MixedEqv.Shared rm ∧
          (∀ τ : Valuation Δ₁, rm.transport τ = τ.reorder hΔ.symm) ∧
          (∀ (τ : Valuation Δ₁) (τ₀ : Valuation Δ₀₁),
            rp.transport Valuation.nil (τ.append τ₀)
              = (Valuation.nil,
                (τ.reorder hΔ.symm).append (τ₀.reorder hΔ₀.symm))))
      have hdp : dp₁.depth + dp₂.depth ≤ n := by
        simp only [ProgramDerivation.depth] at hsum
        have m₁ := Nat.le_max_left dp₁.depth dm₁.depth
        have m₂ := Nat.le_max_left dp₂.depth dm₂.depth
        omega
      have hdm : dm₁.depth + dm₂.depth ≤ n := by
        simp only [ProgramDerivation.depth] at hsum
        have m₁ := Nat.le_max_right dp₁.depth dm₁.depth
        have m₂ := Nat.le_max_right dp₂.depth dm₂.depth
        omega
      have hndΔ₂ : Δ₂.Nodup :=
        (HasMixedType.context_well_formed dm₂.toProp).nodup
      have hndΔ₀₂ : Δ₀₂.Nodup :=
        List.Nodup.of_append_right
          (HasPureType.context_well_formed dp₂.toProp).nodup
      funext v v' w w'
      simp only [programAmplitude]
      refine List.sum_map_enum_perm hΔ hndΔ₂ _ _ ?_
      intro τ₂
      refine List.sum_map_enum_perm hΔ hndΔ₂ _ _ ?_
      intro τ₂'
      -- the mixed factor does not depend on the innermost sum's variable
      have hpm : mixedAmplitude dm₁ (τ₂.reorder hΔ) (τ₂'.reorder hΔ) w w'
          = mixedAmplitude dm₂ τ₂ τ₂' w w' := by
        have h := mixedIH dm₁ dm₂ hdm rm hrm (τ₂.reorder hΔ)
          (τ₂'.reorder hΔ) w w'
        rw [hcompM (τ₂.reorder hΔ), hcompM (τ₂'.reorder hΔ),
          Valuation.reorder_reorder hΔ hndΔ₂ τ₂,
          Valuation.reorder_reorder hΔ hndΔ₂ τ₂'] at h
        exact h
      rw [hpm]
      refine congrArg (fun S => mixedAmplitude dm₂ τ₂ τ₂' w w' * S) ?_
      refine List.sum_map_enum_perm hΔ₀ hndΔ₀₂ _ _ ?_
      intro τ₀₂
      -- the pure factors
      have hpp : pureAmplitude dp₁ Valuation.nil
          ((τ₂.reorder hΔ).append (τ₀₂.reorder hΔ₀)) v
          = pureAmplitude dp₂ Valuation.nil (τ₂.append τ₀₂) v := by
        have h : pureAmplitude dp₁ Valuation.nil
            ((τ₂.reorder hΔ).append (τ₀₂.reorder hΔ₀)) v
            = pureAmplitude dp₂ (rp.transport Valuation.nil
                ((τ₂.reorder hΔ).append (τ₀₂.reorder hΔ₀))).1
              (rp.transport Valuation.nil
                ((τ₂.reorder hΔ).append (τ₀₂.reorder hΔ₀))).2 v :=
          pureIH dp₁ dp₂ hdp rp hrp Valuation.nil _ v
        have hf : (rp.transport Valuation.nil
            ((τ₂.reorder hΔ).append (τ₀₂.reorder hΔ₀))).1
            = (Valuation.nil : Valuation []) :=
          congrArg Prod.fst
            (hcompP (τ₂.reorder hΔ) (τ₀₂.reorder hΔ₀))
        have hs : (rp.transport Valuation.nil
            ((τ₂.reorder hΔ).append (τ₀₂.reorder hΔ₀))).2
            = ((τ₂.reorder hΔ).reorder hΔ.symm).append
              ((τ₀₂.reorder hΔ₀).reorder hΔ₀.symm) :=
          congrArg Prod.snd
            (hcompP (τ₂.reorder hΔ) (τ₀₂.reorder hΔ₀))
        rw [hf, hs, Valuation.reorder_reorder hΔ hndΔ₂ τ₂,
          Valuation.reorder_reorder hΔ₀ hndΔ₀₂ τ₀₂] at h
        exact h
      have hpp' : pureAmplitude dp₁ Valuation.nil
          ((τ₂'.reorder hΔ).append (τ₀₂.reorder hΔ₀)) v'
          = pureAmplitude dp₂ Valuation.nil (τ₂'.append τ₀₂) v' := by
        have h : pureAmplitude dp₁ Valuation.nil
            ((τ₂'.reorder hΔ).append (τ₀₂.reorder hΔ₀)) v'
            = pureAmplitude dp₂ (rp.transport Valuation.nil
                ((τ₂'.reorder hΔ).append (τ₀₂.reorder hΔ₀))).1
              (rp.transport Valuation.nil
                ((τ₂'.reorder hΔ).append (τ₀₂.reorder hΔ₀))).2 v' :=
          pureIH dp₁ dp₂ hdp rp hrp Valuation.nil _ v'
        have hf : (rp.transport Valuation.nil
            ((τ₂'.reorder hΔ).append (τ₀₂.reorder hΔ₀))).1
            = (Valuation.nil : Valuation []) :=
          congrArg Prod.fst
            (hcompP (τ₂'.reorder hΔ) (τ₀₂.reorder hΔ₀))
        have hs : (rp.transport Valuation.nil
            ((τ₂'.reorder hΔ).append (τ₀₂.reorder hΔ₀))).2
            = ((τ₂'.reorder hΔ).reorder hΔ.symm).append
              ((τ₀₂.reorder hΔ₀).reorder hΔ₀.symm) :=
          congrArg Prod.snd
            (hcompP (τ₂'.reorder hΔ) (τ₀₂.reorder hΔ₀))
        rw [hf, hs, Valuation.reorder_reorder hΔ hndΔ₂ τ₂',
          Valuation.reorder_reorder hΔ₀ hndΔ₀₂ τ₀₂] at h
        exact h
      rw [hpp, hpp']

/-! ## The combined induction and the main theorem -/

/-- Everything the successor steps need, at depth budget `n`: the three
uniqueness statements, mutually closed by `pureUnique_step`,
`mixedUnique_step`, and `branchUnique_step`. -/
structure WDUpTo (n : Nat) : Prop where
  pure : PureUniqueAt n
  mixed : MixedUnique n
  branch : BranchUniqueAt n
  prog : ProgUniqueAt n

theorem wd_base : WDUpTo 0 where
  pure := pureUnique_base
  mixed := mixedUnique_base
  branch := branchUnique_base
  prog := progUnique_base

theorem wd_step {n : Nat} (h : WDUpTo n) : WDUpTo (n + 1) where
  pure := pureUnique_step h.mixed h.branch
  mixed := mixedUnique_step h.pure h.mixed
  branch := branchUnique_step h.pure h.branch
  prog := progUnique_step h.pure h.mixed

/-- **Well-definedness by induction on derivation depth**: the three
successor steps close mutually, so the conjunction holds at every budget. -/
theorem wd_all (n : Nat) : WDUpTo n := by
  induction n with
  | zero => exact wd_base
  | succ n ih => exact wd_step ih

/-! ### The final theorems (Definition G.3)

Each layer quantifies over *all* pairs of derivations of the same judgment
shape; the equivalence witness `r` (Definition G.2, with its recorded
decompositions) is carried as a hypothesis, and the comparison is at the
correspondingly transported valuations. -/

/-- **Pure judgments**: equivalent pure proofs compute equal amplitudes at
correspondingly transported valuations. -/
theorem pure_wellDefined {Γ₁ Δ₁ Γ₂ Δ₂ : Context} {e₁ e₂ : Expression}
    {T : DataType} (d₁ : PureDerivation Γ₁ Δ₁ e₁ T)
    (d₂ : PureDerivation Γ₂ Δ₂ e₂ T) (r : PureEqv d₁ d₂) (hs : r.Shared) :
    ∀ (σ : Valuation Γ₁) (τ : Valuation Δ₁) (v : Value T),
      pureAmplitude d₁ σ τ v
        = pureAmplitude d₂ (r.transport σ τ).1 (r.transport σ τ).2 v :=
  (wd_all (d₁.depth + d₂.depth)).pure d₁ d₂ (Nat.le_refl _) r hs

/-- **Mixed judgments**: equivalent mixed proofs compute equal amplitudes
at correspondingly transported valuations. -/
theorem mixed_wellDefined {Δ₁ Δ₂ : Context} {e : Expression} {T : DataType}
    (d₁ : MixedDerivation Δ₁ e T) (d₂ : MixedDerivation Δ₂ e T)
    (r : MixedEqv d₁ d₂) (hs : r.Shared) :
    ∀ (τ τ' : Valuation Δ₁) (v v' : Value T),
      mixedAmplitude d₁ τ τ' v v'
        = mixedAmplitude d₂ (r.transport τ) (r.transport τ') v v' :=
  (wd_all (d₁.depth + d₂.depth)).mixed d₁ d₂ (Nat.le_refl _) r hs

/-- **Branch lists**: equivalent branch proofs compute equal amplitudes at
correspondingly transported merged valuations, given equal probabilities. -/
theorem branch_wellDefined {Γ₁ Γ₁' Δ₁ Δ₁' Γ₂ Γ₂' Δ₂ Δ₂' : Context}
    {l₁ l₂ : List ((Expression × Expression) × Context)} {T T' : DataType}
    (hΓ : List.Perm Γ₁ Γ₂) (hΓ' : List.Perm Γ₁' Γ₂')
    (hΔ : List.Perm Δ₁ Δ₂) (hΔ' : List.Perm Δ₁' Δ₂')
    (b₁ : BranchDerivation Γ₁ Γ₁' Δ₁ Δ₁' l₁ T T')
    (b₂ : BranchDerivation Γ₂ Γ₂' Δ₂ Δ₂' l₂ T T')
    (rb : BranchEqv hΓ hΓ' hΔ hΔ' b₁ b₂) (hs : rb.Shared) :
    ∀ (prob₁ prob₂ : Value T → ℂ), (∀ u, prob₁ u = prob₂ u) →
      ∀ (σ₁ : Valuation (Γ₁ ++ Γ₁')) (τ₁ : Valuation (Δ₁ ++ Δ₁'))
        (v : Value T'),
        branchAmplitude b₁ prob₁ σ₁ τ₁ v
          = branchAmplitude b₂ prob₂
              (BranchEqv.transport hΓ hΓ' hΔ hΔ' σ₁ τ₁).1
              (BranchEqv.transport hΓ hΓ' hΔ hΔ' σ₁ τ₁).2 v :=
  (wd_all (b₁.depth + b₂.depth)).branch hΓ hΓ' hΔ hΔ' b₁ b₂ rb hs
    (Nat.le_refl _)

/-- **Program judgments**: equivalent program proofs compute the same
denotation — the third bullet of Definition G.3. -/
theorem prog_wellDefined {f : Program} {F : ProgramType}
    (d₁ d₂ : ProgramDerivation f F) (r : ProgEqv d₁ d₂) (hs : r.Shared) :
    programAmplitude d₁ = programAmplitude d₂ :=
  (wd_all (d₁.depth + d₂.depth)).prog d₁ d₂ (Nat.le_refl _) r hs

end Qunity
