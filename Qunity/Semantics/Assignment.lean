import Qunity.Semantics.Valuation
import Qunity.Typing.Context

namespace Qunity

structure Assignment (Γ : Context) where
  val : ∀ x T, (x, T) ∈ Γ → Value T

def Valuation.toAssignment {Γ} (τ : Valuation Γ) : Assignment Γ where
  val x T hm := (lookup τ x T).get (lookup_isSome τ hm)

def Assignment.toValuation : ∀ {Γ}, Assignment Γ → Valuation Γ
  | [], _ => .nil
  | (x, T) :: _, σ =>
      .cons (σ.val x T List.mem_cons_self)
        (toValuation ⟨fun y S hm => σ.val y S (List.mem_cons_of_mem _ hm)⟩)

def Assignment.ofPerm {Γ Γ'} (h : List.Perm Γ Γ') (σ : Assignment Γ) : Assignment Γ' where
  val x T hm := σ.val x T (h.mem_iff.mpr hm)

def Valuation.reorder {Γ Γ'} (h : List.Perm Γ' Γ) (σ : Valuation Γ) : Valuation Γ' :=
  (σ.toAssignment.ofPerm h.symm).toValuation

end Qunity
