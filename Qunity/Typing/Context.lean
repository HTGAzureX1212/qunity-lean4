import Mathlib.Data.Finset.Basic
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

theorem Context.well_formed_iff_variables_distinct :
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
end Qunity
