import ZFVP.SetTheory.WoodinSupercompact

/-! Small Woodin embeddings with a specified lower bound for the critical point. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def highCriticalWoodinWitnessFormula : SetTheorySemisentence 4 :=
  f“κ γ a η. !IsOrdinal.dfn γ ∧ ∃ δ, δ ∈ κ ∧ !sigmaOneStarCorrectFormula δ ∧
    ∃ x ∈ !hierarchyFormula δ, ∃ e,
    !piOneMembershipEmbeddingFormula (!hierarchyFormula (!succ.dfn δ))
      (!hierarchyFormula (!succ.dfn γ)) e ∧
    ∃ c, !boundedCriticalPointFormula (!hierarchyFormula (!succ.dfn δ)) e c ∧
      !boundedPairMemberFormula e c κ ∧ !boundedPairMemberFormula e x a ∧ η ∈ c”

def highCriticalWoodinFormula : SetTheorySemisentence 1 :=
  f“κ. !initialOrdinalFormula κ ∧ !isω ∈ κ ∧ ∀ γ, κ ∈ γ → !sigmaOneStarCorrectFormula γ →
    ∀ a ∈ !hierarchyFormula γ, ∀ η ∈ κ, !highCriticalWoodinWitnessFormula κ γ a η”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def HighCriticalWoodinWitness (κ γ a η : V) : Prop :=
  IsOrdinal γ ∧ ∃ δ, δ ∈ κ ∧ IsSigmaOneStarCorrect δ ∧ ∃ x ∈ hierarchy δ,
    ∃ e, IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ γ)) e ∧
    ∃ c, IsCriticalPoint (hierarchy (succ δ)) e c ∧ e ‘ c = κ ∧ e ‘ x = a ∧ η ∈ c

def HasHighCriticalWoodinWitnesses (κ : V) : Prop :=
  IsInitialOrdinal κ ∧ (ω : V) ∈ κ ∧ ∀ γ, κ ∈ γ → IsSigmaOneStarCorrect γ →
    ∀ a ∈ hierarchy γ, ∀ η ∈ κ, HighCriticalWoodinWitness κ γ a η

instance highCriticalWoodinWitnessFormula_defined :
    ℒₛₑₜ-relation₄[V] HighCriticalWoodinWitness via highCriticalWoodinWitnessFormula :=
  ⟨fun v ↦ by
    simp [highCriticalWoodinWitnessFormula, HighCriticalWoodinWitness]
    intro _
    apply exists_congr
    intro δ
    apply and_congr_right
    intro _
    apply and_congr_right
    intro hδ
    let := hδ.1.ordinal
    let := hierarchy_transitive (succ δ)
    apply exists_congr
    intro x
    apply and_congr_right
    intro hx
    apply exists_congr
    intro e
    apply and_congr_right
    intro he
    let := IsFunction.of_mem he.function
    apply exists_congr
    intro c
    rw [← criticalPoint_iff_graphSpec he.function]
    apply and_congr_right
    intro hc
    have hx' : x ∈ hierarchy (succ δ) :=
      hierarchy_mono (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _ hx
    have hcD : c ∈ domain e := by rw [domain_eq_of_mem_function he.function]; exact hc.mem_domain
    have hxD : x ∈ domain e := by rw [domain_eq_of_mem_function he.function]; exact hx'
    simp [kpair_mem_iff_value, hcD, hxD]⟩

instance highCriticalWoodinWitness_definable : ℒₛₑₜ-relation₄[V] HighCriticalWoodinWitness :=
  highCriticalWoodinWitnessFormula_defined.to_definable

instance highCriticalWoodinFormula_defined :
    ℒₛₑₜ-predicate[V] HasHighCriticalWoodinWitnesses via highCriticalWoodinFormula :=
  ⟨fun v ↦ by simp [highCriticalWoodinFormula, HasHighCriticalWoodinWitnesses]⟩

instance hasHighCriticalWoodinWitnesses_definable : ℒₛₑₜ-predicate[V] HasHighCriticalWoodinWitnesses :=
  highCriticalWoodinFormula_defined.to_definable

theorem HighCriticalWoodinWitness.toWoodin {κ γ a η : V} (h : HighCriticalWoodinWitness κ γ a η) :
    WoodinSupercompactWitness κ γ a := by
  obtain ⟨hγ, δ, hδκ, hδ, x, hx, e, he, c, hc, hκ, ha, _⟩ := h
  exact ⟨hγ, δ, hδκ, hδ, x, hx, e, he, c, hc, hκ, ha⟩

theorem HasHighCriticalWoodinWitnesses.woodinSupercompact {κ : V}
    (hκ : HasHighCriticalWoodinWitnesses κ) : IsWoodinSupercompact κ := by
  let := hκ.1.1
  have hz : (∅ : V) ∈ κ := IsOrdinal.toIsTransitive.mem_trans (show (∅ : V) ∈ (ω : V) by simp) hκ.2.1
  exact ⟨hκ.1, fun γ hγ hs a ha ↦ (hκ.2.2 γ hγ hs a ha ∅ hz).toWoodin⟩

end ZFVP
