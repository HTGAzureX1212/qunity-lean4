import Batteries

namespace Qunity

theorem List.nodup_map_of_injective {α β} {f : α → β}
    (hf : ∀ {x y}, f x = f y → x = y) {l : List α} (h : l.Nodup) :
    (l.map f).Nodup :=
  List.pairwise_map.mpr (h.imp fun hne heq => hne (hf heq))

theorem List.nodup_product {α β} {l₁ : List α} {l₂ : List β}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) : (l₁.product l₂).Nodup := by
  induction l₁ with
  | nil => simp [List.product]
  | cons a l ih =>
    rw [List.product, List.flatMap_cons, ← List.product]
    rw [List.nodup_append]
    have ha := List.nodup_cons.mp h₁
    refine ⟨List.nodup_map_of_injective (fun h => by cases h; rfl) h₂, ih ha.2, ?_⟩
    intro p hp q hq
    simp only [List.mem_map] at hp
    obtain ⟨_, _, rfl⟩ := hp
    obtain ⟨hq1, _⟩ := List.pair_mem_product.mp ((Prod.eta q).symm ▸ hq)
    intro heq
    cases heq
    exact ha.1 hq1

end Qunity
