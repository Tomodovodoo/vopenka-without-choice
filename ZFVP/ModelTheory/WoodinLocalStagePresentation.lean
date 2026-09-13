import ZFVP.ModelTheory.WoodinRecursionUniform
import ZFVP.ModelTheory.WoodinCoordinateProjection
import ZFVP.SetTheory.ForcingStageConditions
import ZFVP.SetTheory.ForcingSectionOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- A condition with its stage index, defined without an endpoint parameter. -/
@[irreducible] def woodinLocalStageConditionFormula : SetTheorySemisentence 1 :=
  f“z. ∃ i, ∃ p, !IsOrdinal.dfn i ∧
    p ∈ !value.dfn (!forcingCodePFormula (!kpair.π₁.dfn (!woodinIterationRecFormula i))) i ∧
    z = !kpair.dfn i p”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinLocalStageCondition (z : V) : Prop :=
  ∃ i p : V, IsOrdinal i ∧ p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i ∧ z = ⟨i, p⟩ₖ

instance woodinLocalStageConditionFormula_defined :
    ℒₛₑₜ-predicate[V] IsWoodinLocalStageCondition via woodinLocalStageConditionFormula :=
  ⟨fun v ↦ by simp [woodinLocalStageConditionFormula, IsWoodinLocalStageCondition]⟩

variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j)))
include hs

/-- The prefix presentation is a restriction of the parameter-free stage class. -/
theorem woodinStageConditions_iff_local {z : V} :
    z ∈ forcingStageConditions θ (forcingCodeP (woodinIterationPrefix θ))
      (forcingCodeUniverse (woodinIterationPrefix θ)) ↔
      IsWoodinLocalStageCondition z ∧ kpair.π₁ z ∈ θ := by
  constructor
  · intro hz
    obtain ⟨i, hi, p, _, hp, rfl⟩ := (mem_forcingStageConditions_iff _ _ _ _).mp hz
    rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i)] at hp
    exact ⟨⟨i, p, IsOrdinal.of_mem hi, hp, rfl⟩, by simpa using hi⟩
  · rintro ⟨⟨i, p, _, hp, rfl⟩, hi⟩
    simp only [kpair.π₁_kpair] at hi
    rw [← woodinIterationPrefix_poset_value hs hi (mem_succ_self i)] at hp
    exact (kpair_mem_forcingStageConditions_iff _ _ _ _ _).mpr
      ⟨hi, (woodinIterationPrefix_of_stages hs).code.subset_universe i hi p hp, hp⟩

/-- Supported-thread comparison uses only the recursion at a common support. -/
theorem woodinSection_order_iff_local {i j k p q : V}
    (hi : i ∈ θ) (hj : j ∈ θ) (hk : k ∈ θ) (hik : i ⊆ k) (hjk : j ⊆ k)
    (hp : p ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hq : q ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    ⟨forcingSectionThread θ (forcingCodeπ (woodinIterationPrefix θ))
        (forcingCodeE (woodinIterationPrefix θ)) i p,
      forcingSectionThread θ (forcingCodeπ (woodinIterationPrefix θ))
        (forcingCodeE (woodinIterationPrefix θ)) j q⟩ₖ ∈
      forcingThreadOrder θ (forcingCodeR (woodinIterationPrefix θ))
        (forcingDirectLimit θ (forcingCodeP (woodinIterationPrefix θ))
          (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ))
          (forcingCodeUniverse (woodinIterationPrefix θ))) ↔
    ⟨((forcingCodeE (kpair.π₁ (woodinIterationRec k))) ‘ ⟨i, k⟩ₖ) ‘ p,
      ((forcingCodeE (kpair.π₁ (woodinIterationRec k))) ‘ ⟨j, k⟩ₖ) ‘ q⟩ₖ ∈
      (forcingCodeR (kpair.π₁ (woodinIterationRec k))) ‘ k := by
  let := IsOrdinal.of_mem hk
  have h := (woodinIterationPrefix_of_stages hs).code
  have he := forcingSectionThread_order_iff_common_stage h.system.split hi hj hk hik hjk hp hq
    h.subset_universe
    (fun l hl ↦ h.system.order.projMono l (IsOrdinal.toIsTransitive.mem_trans hl hk) k hk
      (fun x hx ↦ IsOrdinal.toIsTransitive.mem_trans hx hl))
    (fun l hl hkl a ha b hb hab ↦ h.system.order.secMono h.system.split hk hl hkl ha hb hab)
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hi' : i ∈ succ k := by
    rcases IsOrdinal.subset_iff.mp hik with rfl | hik
    · exact mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr hik)
  have hj' : j ∈ succ k := by
    rcases IsOrdinal.subset_iff.mp hjk with rfl | hjk
    · exact mem_succ_self _
    · exact mem_succ_iff.mpr (Or.inr hjk)
  rwa [woodinIterationPrefix_section_value hs hk hi' (mem_succ_self k),
    woodinIterationPrefix_section_value hs hk hj' (mem_succ_self k),
    woodinIterationPrefix_order_value hs hk (mem_succ_self k)] at he

end ZFVP
