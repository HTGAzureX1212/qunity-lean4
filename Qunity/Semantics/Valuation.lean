import Qunity.Language.Types
import Qunity.Math.List
import Qunity.Typing.Context

namespace Qunity

inductive Value : DataType -> Type where
  | unit : Value .unit
  | inl : Value A → Value (A ⊕ B)
  | inr {A B} : Value B → Value (A ⊕ B)
  | pair {A B} : Value A → Value B → Value (A ⊗ B)
deriving DecidableEq

inductive Valuation : Context → Type where
  | nil : Valuation []
  | cons {x T Γ} : Value T → Valuation Γ → Valuation ((x, T) :: Γ)
deriving DecidableEq

def Value.enum : (T : DataType) → List (Value T)
  | .void => []
  | .unit => [.unit]
  | .sum A B => (enum A).map .inl ++ (enum B).map .inr
  | .product A B =>
      ((enum A).product (enum B)).map fun (v, w) => .pair v w

def Value.unpair
    (v : Value (A ⊗ B)) : Value A × Value B :=
  match v with
  | .pair v₀ v₁ => (v₀, v₁)

def Valuation.enum : (Γ : Context) → List (Valuation Γ)
  | [] => [.nil]
  | (_, T) :: Γ =>
      (Value.enum T).flatMap fun v => (enum Γ).map fun τ => .cons v τ

def Valuation.singleton
    (τ : Valuation [(x, T)]) : Value T :=
  match τ with
  | .cons v .nil => v

theorem Value.mem_enum : ∀ {T} (v : Value T), v ∈ enum T
  | .unit, .unit => by simp [enum]
  | .sum A B, .inl v => by
      rw [enum, List.mem_append]
      exact Or.inl (List.mem_map_of_mem (f := Value.inl) (mem_enum v))
  | .sum A B, .inr v => by
      rw [enum, List.mem_append]
      exact Or.inr (List.mem_map_of_mem (f := Value.inr) (mem_enum v))
  | .product A B, .pair v w => by
      rw [enum]
      exact List.mem_map_of_mem
        (f := fun p : Value A × Value B => Value.pair p.1 p.2)
        (List.pair_mem_product.mpr ⟨mem_enum v, mem_enum w⟩)

theorem Value.enum_nodup : ∀ T, (enum T).Nodup
  | .void => by simp [enum]
  | .unit => by simp [enum]
  | .sum A B => by
      rw [enum, List.nodup_append]
      refine ⟨
        List.nodup_map_of_injective (fun h => by cases h; rfl) (enum_nodup A),
        List.nodup_map_of_injective (fun h => by cases h; rfl) (enum_nodup B),
        ?_⟩
      intro _ h₁ _ h₂
      simp only [List.mem_map] at h₁ h₂
      rcases h₁ with ⟨_, _, rfl⟩
      rcases h₂ with ⟨_, _, rfl⟩
      exact fun h => nomatch h
  | .product A B => by
      rw [enum]
      refine List.nodup_map_of_injective ?_
        (List.nodup_product (enum_nodup A) (enum_nodup B))
      rintro ⟨v₁, w₁⟩ ⟨v₂, w₂⟩ h
      cases h
      rfl

theorem Valuation.mem_enum : ∀ {Γ} (τ : Valuation Γ), τ ∈ enum Γ
  | _, .nil => by simp [enum]
  | _, .cons v τ => by
      simp only [enum, List.mem_flatMap, List.mem_map]
      exact ⟨v, Value.mem_enum v, τ, mem_enum τ, rfl⟩

def Valuation.append : ∀ {Γ Δ}, Valuation Γ → Valuation Δ → Valuation (Γ ++ Δ)
  | _, _, .nil, τ => τ
  | _, _, .cons v σ, τ => .cons v (append σ τ)

def Valuation.split : ∀ {Γ Δ}, Valuation (Γ ++ Δ) → Valuation Γ × Valuation Δ
  | [], _, τ => (.nil, τ)
  | (_x, _T) :: Γ, _, .cons v τ =>
      let p := split (Γ := Γ) τ
      (.cons v p.1, p.2)

def Valuation.lookup : ∀ {Γ}, Valuation Γ → Variable → (T : DataType) → Option (Value T)
  | [], .nil, _, _ => none
  | (y, S) :: _, .cons v τ, x, T =>
      if h : y = x ∧ S = T then some (h.2 ▸ v) else lookup τ x T

theorem Valuation.lookup_isSome :
    ∀ {Γ} (τ : Valuation Γ) {x T}, (x, T) ∈ Γ → (lookup τ x T).isSome
  | [], .nil, _, _, hm => by simp at hm
  | (_y, _S) :: _, .cons _ τ, x, T, hm => by
      rw [lookup.eq_2]
      split_ifs with h
      · simp
      · apply lookup_isSome τ
        simp only [List.mem_cons] at hm
        cases hm with
        | inl heq =>
            cases heq
            exact absurd ⟨rfl, rfl⟩ h
        | inr hm => exact hm

theorem Valuation.enum_nodup : ∀ Γ, (enum Γ).Nodup
  | [] => by simp [enum]
  | (_, T) :: Γ => by
      rw [enum, List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
      refine ⟨?_, ?_⟩
      · intro v _
        rw [← List.nodup_iff_pairwise_ne]
        exact List.nodup_map_of_injective (fun h => by cases h; rfl) (enum_nodup Γ)
      · have hv := Value.enum_nodup T
        rw [List.nodup_iff_pairwise_ne] at hv
        refine hv.imp ?_
        intro v₁ v₂ hne τ hτ₁ τ' hτ₂ heq
        simp only [List.mem_map] at hτ₁ hτ₂
        obtain ⟨_, _, rfl⟩ := hτ₁
        obtain ⟨_, _, rfl⟩ := hτ₂
        apply hne
        exact congrArg (fun ρ => match ρ with | .cons v _ => v) heq
