import ZFVP.SetTheory.ForcingIterationSystem
import ZFVP.SetTheory.ForcingLimitOrder
import ZFVP.SetTheory.ForcingLimitTop
import ZFVP.ModelTheory.SuccessorForcingOrder
import ZFVP.ModelTheory.SuccessorForcingTop
import ZFVP.ModelTheory.ForcingColumnFunctions
import ZFVP.ModelTheory.ForcingColumnSectionCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingIterationSystem.successorColumn {θ P R π E L t k Q S u : V}
    (h : IsForcingIterationSystem θ P R π E L t)
    (hk : k ∈ θ) (hmax : ∀ i ∈ θ, i ⊆ k)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S u) :
    IsForcingIterationColumn θ P R π E L t (twoStepConditions (P ‘ k) (R ‘ k) Q u)
      (twoStepOrder (P ‘ k) (R ‘ k) Q S u)
      (successorProjectionColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q u) π k)
      (successorSectionColumn θ P E k u)
      (successorLiftColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q u) P L k) ⟨t ‘ k, u⟩ₖ :=
  ⟨successor_splitColumn h.split hk hmax (h.order.preorder k hk) (h.tops.top k hk) hQ,
    successor_orderedColumn h.split h.order hk hmax (h.tops.top k hk) hQ,
    successor_functionalColumn h.split hk hmax (h.order.preorder k hk) (h.tops.top k hk) hQ,
    successor_toppedColumn h.tops hk hmax (h.order.preorder k hk) hQ,
    successor_coherentLiftColumn h.lifts hk hmax (h.order.preorder k hk) (h.tops.top k hk) hQ,
    successor_sectionCompatibleColumn h.split h.lifts h.compatible hk hmax
      (h.order.preorder k hk) (h.tops.top k hk) hQ⟩

private theorem lower_projection_mono {θ P R π E L t : V} [IsOrdinal θ]
    (h : IsForcingIterationSystem θ P R π E L t) :
    ∀ i ∈ θ, ∀ j ∈ i, ∀ p ∈ P ‘ i, ∀ q ∈ P ‘ i, ⟨p, q⟩ₖ ∈ R ‘ i →
      ⟨(π ‘ ⟨j, i⟩ₖ) ‘ p, (π ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j := by
  intro i hi j hj
  let := IsOrdinal.of_mem hi
  exact h.order.projMono j (IsOrdinal.toIsTransitive.transitive _ hi _ hj) i hi
    (IsOrdinal.toIsTransitive.transitive _ hj)

theorem IsForcingIterationSystem.inverseColumn {θ P R π E L t U k : V} [IsOrdinal θ]
    (h : IsForcingIterationSystem θ P R π E L t)
    (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    IsForcingIterationColumn θ P R π E L t (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingLimitProjectionColumn θ (forcingInverseLimit θ P π U))
      (forcingLimitSectionColumn θ P π E)
      (forcingLimitLiftColumn (forcingInverseLimit θ P π U) θ P π L)
      (forcingSectionThread θ π E k (t ‘ k)) := by
  have hD := forcingDirectLimit_subset θ P π E U
  exact ⟨forcingLimit_splitColumn h.split hU hD (fun _ hf ↦ hf),
    forcingLimit_orderedColumn h.split h.order hU hD (fun _ hf ↦ hf),
    forcingLimit_functionalColumn h.split hU hD (fun _ hf ↦ hf),
    forcingLimit_toppedColumn h.split h.tops hk hU hD (fun _ hf ↦ hf),
    forcingInverseLimit_coherentLiftColumn h.split h.lifts hU (lower_projection_mono h),
    forcingLimit_sectionCompatibleColumn h.split h.lifts h.compatible hU hD⟩

theorem IsForcingIterationSystem.directColumn {θ P R π E L t U k : V} [IsOrdinal θ]
    (h : IsForcingIterationSystem θ P R π E L t)
    (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    IsForcingIterationColumn θ P R π E L t (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingLimitProjectionColumn θ (forcingDirectLimit θ P π E U))
      (forcingLimitSectionColumn θ P π E)
      (forcingLimitLiftColumn (forcingDirectLimit θ P π E U) θ P π L)
      (forcingSectionThread θ π E k (t ‘ k)) := by
  have hI := forcingDirectLimit_subset θ P π E U
  exact ⟨forcingLimit_splitColumn h.split hU (fun _ hf ↦ hf) hI,
    forcingLimit_orderedColumn h.split h.order hU (fun _ hf ↦ hf) hI,
    forcingLimit_functionalColumn h.split hU (fun _ hf ↦ hf) hI,
    forcingLimit_toppedColumn h.split h.tops hk hU (fun _ hf ↦ hf) hI,
    forcingDirectLimit_coherentLiftColumn h.split h.lifts hU (lower_projection_mono h)
      h.compatible.compatible,
    forcingLimit_sectionCompatibleColumn h.split h.lifts h.compatible hU (fun _ hf ↦ hf)⟩

end ZFVP
