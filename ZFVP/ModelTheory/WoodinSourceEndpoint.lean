import ZFVP.ModelTheory.WoodinSourceCompletedInverse
import ZFVP.ModelTheory.WoodinEndpointDirect
import ZFVP.ModelTheory.ForcingIsomorphismModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceCode_quotient_iff {θ s i j η : V} [IsOrdinal θ]
    (hi : i ∈ θ) (hj : j ∈ θ) :
    IterationQuotientClosedBelow (woodinSourceCode θ s) (woodinSourceIndex i) (woodinSourceIndex j) η ↔
      IterationQuotientClosedBelow s i j η := by
  unfold IterationQuotientClosedBelow
  rw [woodinSourceCode_projection hi hj]
  simp only [woodinSourceCode, forcingCodeP_code, forcingCodeR_code, forcingCodet_code,
    woodinInsertSeed_at_sourceIndex hi, woodinInsertSeed_at_sourceIndex hj]

theorem woodinSourceCode_positive_quotient {θ s K i j : V} [IsOrdinal θ]
    (h : HasWoodinQuotientClosure θ s K) (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j) :
    IterationQuotientClosedBelow (woodinSourceCode θ s) (woodinSourceIndex i) (woodinSourceIndex j)
      ((woodinSourceCardinals θ K) ‘ (woodinSourceIndex i)) := by
  rw [woodinSourceCardinals_stage hi, woodinSourceCode_quotient_iff hi hj]
  exact h i hi j hj hij

theorem woodinSourceIndex_supercompact {δ : V} (hδ : IsWoodinSupercompact δ) :
    woodinSourceIndex δ = δ := by
  let := hδ.inaccessible.1
  exact woodinSourceIndex_limit δ
    (IsOrdinal.toIsTransitive.mem_trans (by simp) hδ.inaccessible.2.1)
    (fun i hi ↦ regularCardinal_succ_closed hδ.inaccessible.regular hi)

theorem woodinSourceCode_endpoint_isomorphism {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    IsForcingIsomorphism ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec δ))) ‘ δ)
      ((forcingCodeP (forcingDirectCode δ (woodinSourceCode δ (woodinIterationPrefix δ)))) ‘ δ)
      ((forcingCodeR (forcingDirectCode δ (woodinSourceCode δ (woodinIterationPrefix δ)))) ‘ δ)
      (woodinSeedThreadMap δ ((forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ)) := by
  let := hδ.inaccessible.1
  have hs := (woodinIterationExit hδ hAC).2.2.1.code
  have hh := woodinSourceCode_direct_isomorphism hs
    (IsOrdinal.toIsTransitive.mem_trans (by simp) hδ.inaccessible.2.1)
  rw [woodinSourceIndex_supercompact hδ] at hh
  simpa only [woodinIteration_endpoint_direct hδ hAC, kpair.π₁_kpair] using hh

theorem woodinSourceCode_actual_endpoint_quotient {δ i j : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hi : i ∈ succ δ) (hj : j ∈ succ δ) (hij : i ⊆ j) :
    IterationQuotientClosedBelow
      (woodinSourceCode (succ δ) (kpair.π₁ (woodinIterationRec δ)))
      (woodinSourceIndex i) (woodinSourceIndex j)
      ((woodinSourceCardinals (succ δ) (kpair.π₂ (woodinIterationRec δ))) ‘ (woodinSourceIndex i)) := by
  let := hδ.inaccessible.1
  exact woodinSourceCode_positive_quotient (woodinIteration_endpoint_valid hδ hAC).2 hi hj hij

end ZFVP
