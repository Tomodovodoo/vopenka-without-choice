import ZFVP.SetTheory.SigmaOneStarCorrectness
import ZFVP.SetTheory.CnExtendible

/-! Woodin's small-embedding definition of supercompactness in ZF,
as stated in Spoerl, Definition 21. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSupercompactWitnessFormula : SetTheorySemisentence 3 :=
  f“κ γ a. !IsOrdinal.dfn γ ∧ ∃ δ, δ ∈ κ ∧ !sigmaOneStarCorrectFormula δ ∧
    ∃ x ∈ !hierarchyFormula δ, ∃ e,
    !piOneMembershipEmbeddingFormula (!hierarchyFormula (!succ.dfn δ))
      (!hierarchyFormula (!succ.dfn γ)) e ∧
    ∃ c, !boundedCriticalPointFormula (!hierarchyFormula (!succ.dfn δ)) e c ∧
      !boundedPairMemberFormula e c κ ∧ !boundedPairMemberFormula e x a”

def woodinSupercompactFormula : SetTheorySemisentence 1 :=
  f“κ. !initialOrdinalFormula κ ∧ ∀ γ, κ ∈ γ → !sigmaOneStarCorrectFormula γ →
    ∀ a ∈ !hierarchyFormula γ, !woodinSupercompactWitnessFormula κ γ a”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def WoodinSupercompactWitness (κ γ a : V) : Prop :=
  IsOrdinal γ ∧ ∃ δ, δ ∈ κ ∧ IsSigmaOneStarCorrect δ ∧ ∃ x ∈ hierarchy δ,
    ∃ e, IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ γ)) e ∧
    ∃ c, IsCriticalPoint (hierarchy (succ δ)) e c ∧ e ‘ c = κ ∧ e ‘ x = a

def IsWoodinSupercompact (κ : V) : Prop :=
  IsInitialOrdinal κ ∧ ∀ γ, κ ∈ γ → IsSigmaOneStarCorrect γ →
    ∀ a ∈ hierarchy γ, WoodinSupercompactWitness κ γ a

instance woodinSupercompactWitnessFormula_defined :
    ℒₛₑₜ-relation₃[V] WoodinSupercompactWitness via woodinSupercompactWitnessFormula :=
  ⟨fun v ↦ by
    simp [woodinSupercompactWitnessFormula, WoodinSupercompactWitness]
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

instance woodinSupercompactFormula_defined :
    ℒₛₑₜ-predicate[V] IsWoodinSupercompact via woodinSupercompactFormula :=
  ⟨fun v ↦ by simp [woodinSupercompactFormula, IsWoodinSupercompact]⟩

instance woodinSupercompactWitness_definable : ℒₛₑₜ-relation₃[V] WoodinSupercompactWitness :=
  woodinSupercompactWitnessFormula_defined.to_definable

instance woodinSupercompact_definable : ℒₛₑₜ-predicate[V] IsWoodinSupercompact :=
  woodinSupercompactFormula_defined.to_definable

end ZFVP


