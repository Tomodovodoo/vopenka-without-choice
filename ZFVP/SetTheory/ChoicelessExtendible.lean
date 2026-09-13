import ZFVP.SetTheory.CnExtendible

/-! Extendibility with a prescribed lower bound on a variable critical point.
The alpha-relative predicate follows Mohammd's Definition 2.1. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def alphaChoicelessExtendibleFormula (n : ℕ) : SetTheorySemisentence 2 :=
  f“α γ. !IsOrdinal.dfn γ ∧ α ∈ γ ∧ ∀ μ, !(cnFormula n) μ → γ ∈ μ →
    ∃ ν e κ, !(cnFormula n) ν ∧
      !piOneMembershipEmbeddingFormula (!hierarchyFormula μ) (!hierarchyFormula ν) e ∧
      !boundedCriticalPointFormula (!hierarchyFormula μ) e κ ∧ α ∈ κ ∧ μ ∈ !value.dfn e γ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsAlphaChoicelessExtendible (n : ℕ) (α γ : V) : Prop :=
  IsOrdinal γ ∧ α ∈ γ ∧ ∀ μ, Cn n μ → γ ∈ μ → ∃ ν e κ,
    Cn n ν ∧ IsCodedMembershipEmbedding (hierarchy μ) (hierarchy ν) e ∧
      IsCriticalPoint (hierarchy μ) e κ ∧ α ∈ κ ∧ μ ∈ e ‘ γ

theorem eval_alphaChoicelessExtendibleFormula (n : ℕ) (α γ : V) :
    (alphaChoicelessExtendibleFormula n).Evalb ![α, γ] ↔ IsAlphaChoicelessExtendible n α γ := by
  simp [alphaChoicelessExtendibleFormula, IsAlphaChoicelessExtendible]
  intro hγ hαγ
  apply forall_congr'
  intro μ
  apply imp_congr_right
  intro hμ
  apply imp_congr_right
  intro hγμ
  apply exists_congr
  intro ν
  apply and_congr_right
  intro hν
  apply exists_congr
  intro e
  apply and_congr_right
  intro he
  apply exists_congr
  intro κ
  let := hμ.ordinal
  let := hierarchy_transitive μ
  exact and_congr (criticalPoint_iff_graphSpec he.function).symm Iff.rfl

instance alphaChoicelessExtendibleFormula_defined (n : ℕ) :
    ℒₛₑₜ-relation[V] (IsAlphaChoicelessExtendible n) via alphaChoicelessExtendibleFormula n :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change (alphaChoicelessExtendibleFormula n).Evalb v ↔ IsAlphaChoicelessExtendible n (v 0) (v 1)
    rw [← hv]
    exact eval_alphaChoicelessExtendibleFormula _ _ _⟩

instance alphaChoicelessExtendible_definable (n : ℕ) :
    ℒₛₑₜ-relation[V] (IsAlphaChoicelessExtendible n) :=
  (alphaChoicelessExtendibleFormula_defined n).to_definable

theorem IsAlphaChoicelessExtendible.ordinal {n : ℕ} {α γ : V}
    (h : IsAlphaChoicelessExtendible n α γ) : IsOrdinal γ := h.1

theorem IsAlphaChoicelessExtendible.bound_ordinal {n : ℕ} {α γ : V}
    (h : IsAlphaChoicelessExtendible n α γ) : IsOrdinal α := by
  let := h.ordinal
  exact IsOrdinal.of_mem h.2.1

theorem IsCnExtendible.alphaChoiceless {n : ℕ} {κ α : V} (hκ : IsCnExtendible n κ)
    (hα : α ∈ κ) : IsAlphaChoicelessExtendible n α κ := by
  refine ⟨hκ.1.1, hα, ?_⟩
  intro μ hμ hκμ
  obtain ⟨ν, e, _, hν, he, hc, hm⟩ := hκ.2 μ hμ hκμ
  exact ⟨ν, e, κ, hν, he, hc, hα, hm⟩

theorem IsAlphaChoicelessExtendible.lower_bound {n : ℕ} {α β γ : V}
    (h : IsAlphaChoicelessExtendible n α γ) (hβα : β ∈ α) :
    IsAlphaChoicelessExtendible n β γ := by
  let := h.ordinal
  refine ⟨h.ordinal, IsOrdinal.toIsTransitive.mem_trans hβα h.2.1, ?_⟩
  intro μ hμ hγμ
  obtain ⟨ν, e, κ, hν, he, hc, hακ, hm⟩ := h.2.2 μ hμ hγμ
  let := hc.ordinal
  exact ⟨ν, e, κ, hν, he, hc, IsOrdinal.toIsTransitive.mem_trans hβα hακ, hm⟩

theorem IsAlphaChoicelessExtendible.raise_ordinal {n : ℕ} {α γ δ : V}
    (h : IsAlphaChoicelessExtendible n α γ) (hδ : IsOrdinal δ) (hγδ : γ ∈ δ) :
    IsAlphaChoicelessExtendible n α δ := by
  let := h.ordinal
  let := hδ
  refine ⟨hδ, IsOrdinal.toIsTransitive.mem_trans h.2.1 hγδ, ?_⟩
  intro μ hμ hδμ
  let := hμ.ordinal
  let := hierarchy_transitive μ
  have hγμ := IsOrdinal.toIsTransitive.mem_trans hγδ hδμ
  obtain ⟨ν, e, κ, hν, he, hc, hακ, hm⟩ := h.2.2 μ hμ hγμ
  let := hν.ordinal
  let := hierarchy_transitive ν
  have hγV := ordinal_subset_hierarchy μ γ hγμ
  have hδV := ordinal_subset_hierarchy μ δ hδμ
  let := he.value_ordinal hδ hδV
  have hj := (he.value_mem_iff hγV hδV).mpr hγδ
  exact ⟨ν, e, κ, hν, he, hc, hακ, IsOrdinal.toIsTransitive.mem_trans hm hj⟩

theorem leastAlphaChoicelessExtendible_existsUnique (n : ℕ) (α : V)
    (h : ∃ γ, IsAlphaChoicelessExtendible n α γ) :
    ∃! γ, IsLeastOrdinal (IsAlphaChoicelessExtendible n α) γ := by
  apply leastOrdinal_existsUnique _ (by definability)
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, hγ.ordinal, hγ⟩

end ZFVP
