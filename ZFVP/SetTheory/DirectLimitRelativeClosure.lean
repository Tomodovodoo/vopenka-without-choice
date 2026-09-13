import ZFVP.SetTheory.DirectLimitClosure
import ZFVP.SetTheory.ForcingRelativeClosure
import ZFVP.SetTheory.ForcingThreadMaps
import ZFVP.SetTheory.FiniteCofinality

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingDirectLimit_relativeDirectedClosedAt {θ P R π E U α i : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ) (hα : α ∈ internalCofinality θ)
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hclosed : ∀ k ∈ θ, i ⊆ k →
      IsForcingRelativeDirectedClosedAt (P ‘ i) (R ‘ i) (P ‘ k) (R ‘ k) (π ‘ ⟨i, k⟩ₖ) α)
    (hπ : ∀ j ∈ θ, ∀ k ∈ θ, j ∈ k → ∀ p ∈ P ‘ k, ∀ q ∈ P ‘ k,
      ⟨p, q⟩ₖ ∈ R ‘ k → ⟨(π ‘ ⟨j, k⟩ₖ) ‘ p, (π ‘ ⟨j, k⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j)
    (hE : ∀ k ∈ θ, ∀ j ∈ θ, k ⊆ j → ∀ p ∈ P ‘ k, ∀ q ∈ P ‘ k,
      ⟨p, q⟩ₖ ∈ R ‘ k → ⟨(E ‘ ⟨k, j⟩ₖ) ‘ p, (E ‘ ⟨k, j⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j) :
    IsForcingRelativeDirectedClosedAt (P ‘ i) (R ‘ i) (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i) α := by
  intro f hf p hp hpb
  obtain ⟨k₀, hk₀, hsupport₀⟩ := forcingDirectLimit_common_support h hα hf.1
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hk₀
  let k := i ∪ k₀
  have hk : k ∈ θ := ordinal_union_mem hi hk₀
  let := IsOrdinal.of_mem hk
  have hik : i ⊆ k := fun z hz ↦ mem_union_iff.mpr (Or.inl hz)
  have hk₀k : k₀ ⊆ k := fun z hz ↦ mem_union_iff.mpr (Or.inr hz)
  have hfi (a : V) (ha : a ∈ α) := forcingDirectLimit_subset _ _ _ _ _ _ (function_value_mem hf.1 ha)
  have hcoord (a : V) (ha : a ∈ α) := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hfi a ha)).2.1
  have hsupport (a : V) (ha : a ∈ α) : IsThreadSupport θ E (f ‘ a) k :=
    (hsupport₀ a ha).raise (hcoord a ha) hk hk₀k (fun j hj hkj q hq ↦
      h.secComp k₀ hk₀ k hk j hj hk₀k hkj q hq)
  let b := definableGraph α (fun a ↦ (f ‘ a) ‘ k) (by definability)
  have hb (a : V) (ha : a ∈ α) : b ‘ a = (f ‘ a) ‘ k := value_definableGraph _ _ _ ha
  have hbdir : IsForcingDirectedFamily (P ‘ k) (R ‘ k) α b := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun a ha ↦ hcoord a ha k hk), ?_⟩
    intro a ha c hc
    obtain ⟨d, hd, hda, hdc⟩ := hf.2 a ha c hc
    refine ⟨d, hd, ?_, ?_⟩
    · rw [hb d hd, hb a ha]
      exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hda).2.2 k hk
    · rw [hb d hd, hb c hc]
      exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hdc).2.2 k hk
  have hpb' : ∀ a ∈ α, ⟨p, (π ‘ ⟨i, k⟩ₖ) ‘ (b ‘ a)⟩ₖ ∈ R ‘ i := by
    intro a ha
    rw [hb a ha, forcingInverseLimit_project_subset h (hfi a ha) hi hk hik]
    simpa only [forcingThreadCoordinate_value (function_value_mem hf.1 ha)] using hpb a ha
  obtain ⟨q, hq, hqb, hqp⟩ := hclosed k hk hik b hbdir p hp hpb'
  have hqD := forcingSectionThread_mem h hk hq hU
  refine ⟨forcingSectionThread θ π E k q, hqD, ?_, ?_⟩
  · intro a ha
    apply forcingThreadOrder_of_support (forcingDirectLimit_subset _ _ _ _ _ _ hqD) (hfi a ha)
      (forcingSectionThread_support h hk hq) (hsupport a ha)
      (fun j hj ↦ hπ j (IsOrdinal.toIsTransitive.mem_trans hj hk) k hk hj) (hE k hk)
    simpa only [forcingSectionThread_value hk, forcingSectionValue_self h hk hq, hb a ha] using hqb a ha
  · rw [forcingThreadCoordinate_value hqD, forcingSectionThread_value hi]
    rcases IsOrdinal.subset_iff.mp hik with he | hik
    · rw [he, forcingSectionValue_self h hk hq]
      rw [he, h.projId hk hq] at hqp
      exact hqp
    · simpa only [forcingSectionValue, ite_eq_left hik] using hqp

end ZFVP
