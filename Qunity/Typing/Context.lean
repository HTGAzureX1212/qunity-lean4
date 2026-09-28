import Mathlib.Data.Finset.Basic
import Qunity.Language.Types

namespace Qunity

abbrev Variable := String
abbrev Binding := Variable × DataType
abbrev Context := List Binding

structure ClassicalContext where
  bindings : Context

structure QuantumContext where
  bindings : Context

def Context.dom (Γ : Context) : Finset Variable :=
  (Γ.map Prod.fst).toFinset

inductive Context.WellFormed : Context -> Prop where
  | nil : WellFormed []
  | cons : WellFormed Γ → x ∉ dom Γ → WellFormed ((x, T) :: Γ)

lemma Context.well_formed_iff_variables_distinct :
  Context.WellFormed Γ ↔ (Γ.map Prod.fst).Nodup := by induction Γ with
    | nil =>
      constructor <;> intro _
      · trivial -- WellFormed → Nodup
      · exact WellFormed.nil -- Nodup → WellFormed
    | cons _ tΓ ih =>
      constructor <;> intro h
      · cases h with -- WellFormed → Nodup
        | cons hΓ hx =>
          apply List.nodup_cons.mpr
          constructor
          · simpa [Context.dom] using hx
          · exact ih.mp hΓ
      · have ⟨hx, hΓ⟩ := List.nodup_cons.mp h -- Nodup → WellFormed
        apply WellFormed.cons
        exact ih.mpr hΓ
        simpa [Context.dom] using hx

end Qunity
