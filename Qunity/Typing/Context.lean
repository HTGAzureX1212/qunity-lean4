import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Qunity.Language.Types

namespace Qunity

abbrev Variable := String
abbrev Binding := Variable × DataType
abbrev Context := List Binding

def Context.dom (Γ : Context) : Finset Variable :=
  (Γ.map Prod.fst).toFinset

@[simp]
lemma Context.dom_nil : Context.dom [] = ∅ := by
  trivial

@[simp]
lemma Context.dom_cons : Context.dom ((x, T) :: Γ) = insert x (Context.dom Γ) := by
  simp [Context.dom]

@[simp]
lemma Context.mem_dom_iff_in_context (x : Variable) (Γ : Context) :
  x ∈ Context.dom Γ ↔ x ∈ Γ.map Prod.fst := by
  simp [Context.dom]

def Context.Disjoint (Γ₁ Γ₂ : Context) : Prop :=
  (Γ₁.map Prod.fst).Disjoint (Γ₂.map Prod.fst)

inductive Context.WellFormed : Context -> Prop where
  | nil : WellFormed []
  | cons : WellFormed Γ → x ∉ dom Γ → WellFormed ((x, T) :: Γ)

lemma Context.well_formed_iff_variables_distinct :
  Context.WellFormed Γ ↔ (Γ.map Prod.fst).Nodup := by induction Γ with
    | nil =>
      constructor <;> intro _
      · simp -- WellFormed → Nodup
      · exact WellFormed.nil -- Nodup → WellFormed
    | cons _ tΓ ih =>
      constructor <;> intro h
      · cases h with -- WellFormed → Nodup
        | cons hΓ hx =>
          apply List.nodup_cons.mpr
          constructor
          · simpa using hx
          · exact ih.mp hΓ
      · have ⟨hx, hΓ⟩ := List.nodup_cons.mp h -- Nodup → WellFormed
        apply WellFormed.cons
        exact ih.mpr hΓ
        simpa using hx

lemma Context.disjoint_of_shared_prefix_concatenation {Γ A B C : Context}
    (dAB : Disjoint Γ (A ++ B))
    (dAC : Disjoint Γ (A ++ C)) :
    Disjoint Γ (A ++ B ++ C) := by
  simp only [Disjoint] at dAB dAC ⊢
  intro x hx hmem
  rw [List.map_append, List.mem_append] at hmem
  cases hmem with
  | inl hmem => exact dAB hx hmem
  | inr hmem =>
    exact dAC hx (by
      rw [List.map_append, List.mem_append]
      exact Or.inr hmem)

@[simp]
lemma Context.permutation_nil : Γ.Perm [] ↔ Γ = [] := by
  exact List.perm_nil

@[simp]
lemma Context.nil_permutation : [].Perm Γ ↔ Γ = [] := by
  exact List.nil_perm

@[simp]
lemma Context.permutation_singleton : Γ.Perm [a] ↔ Γ = [a] := by
  exact List.perm_singleton

@[simp]
lemma Context.singleton_permutation : [a].Perm Γ ↔ [a] = Γ := by
  exact List.singleton_perm

@[simp]
lemma perm_pair_iff : Γ.Perm [a, b] ↔ Γ = [a, b] ∨ Γ = [b, a] := by
  exact List.perm_pair

theorem Context.concatenation_well_formed_iff_disjoint :
  WellFormed (Γ₁ ++ Γ₂) ↔ WellFormed Γ₁ ∧ WellFormed Γ₂ ∧ Disjoint Γ₁ Γ₂ := by
  constructor
  · intro h
    rw [well_formed_iff_variables_distinct] at h
    rw [List.map_append] at h
    rcases List.nodup_append'.mp h with ⟨hΓ₁, hΓ₂, hDisjoint⟩
    constructor
    · exact well_formed_iff_variables_distinct.mpr hΓ₁
    · constructor
      · exact well_formed_iff_variables_distinct.mpr hΓ₂
      · exact hDisjoint
  · intro h
    apply well_formed_iff_variables_distinct.mpr
    rw [List.map_append]
    apply List.nodup_append'.mpr
    rcases h with ⟨hΓ₁, hΓ₂, hDisjoint⟩
    constructor
    · exact well_formed_iff_variables_distinct.mp hΓ₁
    · constructor
      · exact well_formed_iff_variables_distinct.mp hΓ₂
      · exact hDisjoint

theorem Context.permutation_preserves_well_formedness (h : Γ₁.Perm Γ₂) :
  WellFormed Γ₁ ↔ WellFormed Γ₂ := by
  rw [well_formed_iff_variables_distinct, well_formed_iff_variables_distinct]
  exact (h.map Prod.fst).nodup_iff

theorem Context.permutation_preserves_dom (h : Γ₁.Perm Γ₂) :
  Context.dom Γ₁ = Context.dom Γ₂ := by
  unfold Context.dom
  exact List.toFinset_eq_of_perm _ _ (h.map Prod.fst)

theorem Context.permutation_preserves_dom_membership (h : Γ₁.Perm Γ₂) :
  x ∈ Context.dom Γ₁ ↔ x ∈ Context.dom Γ₂ := by
  rw [mem_dom_iff_in_context, mem_dom_iff_in_context]
  exact (h.map Prod.fst).mem_iff
end Qunity
