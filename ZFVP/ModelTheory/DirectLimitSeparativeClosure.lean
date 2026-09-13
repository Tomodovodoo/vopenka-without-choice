import ZFVP.ModelTheory.LimitSplitProjection
import ZFVP.ModelTheory.SplitSeparativeOrder
import ZFVP.SetTheory.DirectLimitClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Short sequences in a direct limit have a common support. Separative closure
at that stage gives a separative lower bound for the whole sequence. -/
theorem forcingDirectLimit_separative_closedAt {θ P R π E U α : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hα : α ∈ internalCofinality θ)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j)
        (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ))
    (hclosed : ∀ k ∈ θ,
      IsForcingClosedAt (P ‘ k) (forcingSeparativeOrder (P ‘ k) (R ‘ k)) α) :
    IsForcingClosedAt (forcingDirectLimit θ P π E U)
      (forcingSeparativeOrder (forcingDirectLimit θ P π E U)
        (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))) α := by
  intro f hf
  obtain ⟨k, hk, hs⟩ := forcingDirectLimit_common_support h hα hf.1
  have hkproj := forcingDirectLimit_splitProjection h hk hU hsplit
  have hfi (i : V) (hi : i ∈ α) := function_value_mem hf.1 hi
  have hcoord (i : V) (hi : i ∈ α) : (f ‘ i) ‘ k ∈ P ‘ k :=
    ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
      (forcingDirectLimit_subset _ _ _ _ _ _ (hfi i hi))).2.1 k hk
  let b := definableGraph α (fun i ↦ (f ‘ i) ‘ k) (by definability)
  have hb (i : V) (hi : i ∈ α) : b ‘ i = (f ‘ i) ‘ k := value_definableGraph _ _ _ hi
  let := IsOrdinal.of_mem hα
  have hdesc : IsForcingDescending (P ‘ k) (forcingSeparativeOrder (P ‘ k) (R ‘ k)) α b := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ hcoord, ?_⟩
    intro i hi j hj
    have hjα := IsOrdinal.toIsTransitive.mem_trans hj hi
    rw [hb i hi, hb j hjα]
    simpa only [forcingThreadCoordinate_value (hfi i hi),
      forcingThreadCoordinate_value (hfi j hjα)] using
      hkproj.projection.separative_monotone (hf.2 i hi j hj)
  obtain ⟨p, hp, hpbound⟩ := hclosed k hk b hdesc
  have hpD := function_value_mem hkproj.maps hp
  refine ⟨(forcingThreadSection θ P π E k) ‘ p, hpD, ?_⟩
  intro i hi
  have he : (forcingThreadSection θ P π E k) ‘ ((f ‘ i) ‘ k) = f ‘ i := by
    rw [forcingThreadSection_value (hcoord i hi)]
    apply forcingThread_eq_of_support
      (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk (hcoord i hi) hU))
      (forcingDirectLimit_subset _ _ _ _ _ _ (hfi i hi))
      (forcingSectionThread_support h hk (hcoord i hi)) (hs i hi)
    rw [forcingSectionThread_value hk, forcingSectionValue_self h hk (hcoord i hi)]
  rw [← he]
  apply (hkproj.separative_below hpD (hcoord i hi)).mpr
  rw [hkproj.right_inverse p hp]
  simpa only [hb i hi] using hpbound i hi

end ZFVP
