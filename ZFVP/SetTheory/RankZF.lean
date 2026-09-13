import ZFVP.SetTheory.RankZermelo

/-! The ZF rank criterion, including every external instance of Replacement. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankDomain_models_zf {θ : V} [IsOrdinal θ] [Nonempty (SetDomain (hierarchy θ))]
    (hω : (ω : V) ∈ θ) (hs : ∀ β ∈ θ, succ β ∈ θ) (hθ : NoLowRankCofinalMaps θ) :
    (SetDomain (hierarchy θ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let A := hierarchy θ
  let : (SetDomain A)↓[ℒₛₑₜ] ⊧* 𝗭 := rankDomain_models_zermelo hω hs
  have ht := hierarchy_transitive θ
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models (SetDomain A) (𝗘𝗤 ℒₛₑₜ) hφ
  | axiom_of_empty_set => exact Theory.models (SetDomain A) 𝗭 Zermelo.axiom_of_empty_set
  | axiom_of_extentionality => exact Theory.models (SetDomain A) 𝗭 Zermelo.axiom_of_extentionality
  | axiom_of_pairing => exact Theory.models (SetDomain A) 𝗭 Zermelo.axiom_of_pairing
  | axiom_of_union => exact Theory.models (SetDomain A) 𝗭 Zermelo.axiom_of_union
  | axiom_of_power_set => exact Theory.models (SetDomain A) 𝗭 Zermelo.axiom_of_power_set
  | axiom_of_infinity => exact Theory.models (SetDomain A) 𝗭 Zermelo.axiom_of_infinity
  | axiom_of_foundation => exact Theory.models (SetDomain A) 𝗭 Zermelo.axiom_of_foundation
  | axiom_of_separation ψ => exact Theory.models (SetDomain A) 𝗭 (Zermelo.axiom_of_separation ψ)
  | axiom_of_replacement ψ =>
    simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
    intro e hf X
    let R := fun x y : V ↦ (relativize ψ).Eval ![x, y] (fun i ↦ i.elim A (fun j ↦ (e j).val))
    have hR : ℒₛₑₜ-relation R := by
      apply Language.Definable.of_iff (relativizedEvaluation_definable A ψ e)
      intro v
      have hv : ![v 0, v 1] = v := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
      change (relativize ψ).Eval ![v 0, v 1] _ ↔ (relativize ψ).Eval v _
      rw [hv]
    have hRiff (x y : SetDomain A) : R x.val y.val ↔ ψ.Eval ![x, y] e := by
      have he := eval_relativize A ψ ![x, y] e
      have hv : (fun i ↦ ((![x, y] : Fin 2 → SetDomain A) i).val) = ![x.val, y.val] := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
      rw [hv] at he
      exact he
    have hex : ∀ x ∈ X.val, ∃! y, y ∈ A ∧ R x y := by
      intro x hx
      let u : SetDomain A := ⟨x, ht.mem_trans hx X.property⟩
      obtain ⟨y, hy, huy⟩ := hf u
      refine ⟨y.val, ⟨y.property, (hRiff u y).mpr hy⟩, ?_⟩
      intro z hz
      exact congrArg Subtype.val (huy ⟨z, hz.1⟩ ((hRiff u ⟨z, hz.1⟩).mp hz.2))
    obtain ⟨b, hb, hmem⟩ := hθ.replacement hs X.property R hR hex
    refine ⟨⟨b, hb⟩, ?_⟩
    intro y
    change y.val ∈ b ↔ ∃ x : SetDomain A, x.val ∈ X.val ∧ ψ.Eval ![x, y] e
    rw [hmem y.val y.property]
    constructor
    · rintro ⟨x, hx, hxy⟩
      let u : SetDomain A := ⟨x, ht.mem_trans hx X.property⟩
      exact ⟨u, hx, (hRiff u y).mp hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x.val, hx, (hRiff x y).mpr hxy⟩

end ZFVP
