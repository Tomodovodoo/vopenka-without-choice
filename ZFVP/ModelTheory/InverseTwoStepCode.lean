import ZFVP.ModelTheory.TwoStepColumnCode
import ZFVP.ModelTheory.ForcingLimitBoundTables

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An inverse limit followed by a second forcing, inserted at the original limit index. -/
noncomputable def forcingInverseTwoStepCode (θ s Q S u : V) : V :=
  let C := forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s)
  forcingTwoStepColumnCode θ s C (forcingThreadOrder θ (forcingCodeR s) C)
    (forcingLimitProjectionColumn θ C)
    (forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s))
    (forcingLimitLiftColumn C θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s))
    (forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) ∅ ((forcingCodet s) ‘ ∅)) Q S u

theorem forcingInverseTwoStepCode_valid {θ s Q S u : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (hQ : IsForcingIterand
      (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadOrder θ (forcingCodeR s)
        (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))) Q S u) :
    IsForcingIterationCode (succ θ) (forcingInverseTwoStepCode θ s Q S u) :=
  forcingTwoStepColumnCode_valid h (h.system.inverseColumn h0 h.subset_universe) hQ

theorem forcingInverseTwoStepCode_extends {θ s : V} (h : IsForcingIterationCode θ s) (Q S u : V) :
    ForcingCodeExtends s (forcingInverseTwoStepCode θ s Q S u) :=
  forcingTwoStepColumnCode_extends h _ _ _ _ _ _ _ _ _

noncomputable def forcingInverseTwoStepBoundTable (θ s B i I Q u : V) : V :=
  let C := forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s)
  let T := forcingThreadOrder θ (forcingCodeR s) C
  forcingFamilyNext θ B (forcingSuccessorBound (twoStepConditions C T Q u) ((forcingCodeP s) ‘ i)
    (twoStepProjection C T Q u) (forcingLimitBound θ (forcingCodeP s) (forcingCodeπ s) B i I C) I)

theorem forcingInverseTwoStepCode_bound_table {θ s B i I Q S : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) (hi : i ∈ θ)
    (hb : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I)
    (hQ : IsForcingIterand
      (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadOrder θ (forcingCodeR s)
        (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))) Q S ∅)
    (hU : let C := forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s)
      let T := forcingThreadOrder θ (forcingCodeR s) C
      ∀ f, IsForcingDirectedFamily (twoStepConditions C T Q ∅) (twoStepOrder C T Q S ∅) I f →
        ∀ q ∈ C, (∀ a ∈ I, ⟨q, kpair.π₁ (f ‘ a)⟩ₖ ∈ T) →
        twoStepUnionBound I q f ∈ twoStepConditions C T Q ∅ ∧
          ∀ a ∈ I, ⟨twoStepUnionBound I q f, f ‘ a⟩ₖ ∈ twoStepOrder C T Q S ∅) :
    let z := forcingInverseTwoStepCode θ s Q S ∅
    let B' := forcingInverseTwoStepBoundTable θ s B i I Q ∅
    IsCoherentForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) B' i I ∧
      IsSectionCompatibleForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z)
        (forcingCodeE z) B' i I := by
  have b := inverse_coherentBoundColumn h.system.split h.system.order h.system.functions hb hi h.subset_universe
  have bc := limit_sectionCompatibleBoundColumn h.system.split h.system.functions hb hc hi
    h.subset_universe (forcingDirectLimit_subset _ _ _ _ _)
  exact forcingTwoStepColumnCode_bound_table (h.system.inverseColumn h0 h.subset_universe)
    hi hb hc b bc hQ hU

end ZFVP
