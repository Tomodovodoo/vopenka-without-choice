import ZFVP.SetTheory.OmegaJonssonExistence
import ZFVP.ModelTheory.CriticalLimitStrongLimit
import ZFVP.ModelTheory.KunenCnTwo

/-! Kunen's theorem with the omega-Jonsson hypothesis discharged.

The Kunen modules `ZFVP.ModelTheory.KunenCnTwo` and `ZFVP.ModelTheory.KunenFixedStage` carry an
omega-Jonsson function for the critical limit as a hypothesis. With internal choice in the
background that hypothesis is free: the critical limit of a coded rank self-embedding is an
initial ordinal of cofinality `ω` whose smaller power sets all inject into it, which is exactly
what the Erdos-Hajnal construction `exists_omegaJonsson` needs. The resulting function is a subset
of `℘ lam ×ˢ lam`, hence lives inside the stage. So under choice a coded self-embedding of a rank
stage whose critical limit lies in the stage is already contradictory, and likewise for an
embedding between stages that fixes an ordinal above its critical point. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Under choice the critical limit of a coded rank self-embedding carries an omega-Jonsson
function inside the stage. -/
theorem exists_omegaJonsson_criticalLimit (hAC : InternalChoice V) {k : ℕ} {δ f κ : V}
    (hδ : Cn (k + 1) δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hlim : criticalLimit f κ ∈ hierarchy δ) :
    ∃ F ∈ hierarchy δ, IsOmegaJonsson F (criticalLimit f κ) := by
  let := hδ.ordinal
  obtain ⟨F, hFsub, hFJ⟩ := exists_omegaJonsson hAC
    (CriticalSequence.limit_initial hδ h hκ)
    (CriticalSequence.omega_mem_limit hδ h hκ)
    ⟨criticalSequence f κ, CriticalSequence.sequence_function hδ h hκ,
      CriticalSequence.cofinal hδ h hκ⟩
    (fun _ hα ↦ CriticalSequence.limit_power_cardLE hδ h hκ hAC hα)
  refine ⟨F, ?_, hFJ⟩
  exact subset_mem_hierarchy_limit hδ.successor_closed
    (prod_mem_hierarchy_limit hδ.successor_closed
      (power_mem_hierarchy_limit hδ.successor_closed hlim) hlim) hFsub

/-- Kunen's contradiction under choice: a `C(2)` rank stage admits no coded self-embedding whose
critical limit lies inside the stage. -/
theorem false_of_selfEmbedding_criticalLimit (hAC : InternalChoice V) {δ f κ : V} (hδ : Cn 2 δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hlim : criticalLimit f κ ∈ hierarchy δ) : False :=
  no_omegaJonsson_selfEmbedding_two hδ h hκ hlim
    (exists_omegaJonsson_criticalLimit hAC hδ h hκ hlim)

/-- Kunen's contradiction under choice at a fixed stage: an embedding between rank stages that
fixes a `C(2)` ordinal `η` above its critical point, with the critical limit below `η`, does not
exist. -/
theorem false_of_fixed_stage_embedding_choice (hAC : InternalChoice V) {k l : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε) (hηc : Cn 2 η)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η)
    (hlimη : criticalLimit f κ ∈ η) : False := by
  let := hη
  have hg : IsCodedMembershipEmbedding (hierarchy η) (hierarchy η) (f ↾ (hierarchy η)) :=
    selfRestriction_of_fixed_ordinal hδ hε h hκ hη hηδ hfix hκη
  have hκg : IsCriticalPoint (hierarchy η) (f ↾ (hierarchy η)) κ :=
    criticalPoint_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  have heq : criticalLimit (f ↾ (hierarchy η)) κ = criticalLimit f κ :=
    criticalLimit_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  let := CriticalSequence.limit_ordinal hηc hg hκg
  have hlim : criticalLimit (f ↾ (hierarchy η)) κ ∈ hierarchy η :=
    ordinal_mem_hierarchy_iff.mpr (by rw [heq]; exact hlimη)
  exact false_of_selfEmbedding_criticalLimit hAC hηc hg hκg hlim

end ZFVP
