import ZFVP.ModelTheory.SchmerlCodedCofinalSuccessor
import ZFVP.ModelTheory.InternalNamedFiniteOmission
import ZFVP.ModelTheory.InternalNamedSeparationOmission

/-! A single actual successor meeting both omission families and every cofinal
background demand. Only density of the two omission families is left as an
intermediate premise; the filter, theory, and model are all constructed. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_codedCofinalOmittingSuccessor_of_namedDensities
    (hAC : InternalChoice V) {D R F j k : V}
    (hM : IsCodedZFModel (binaryRelationStructureCode D R))
    (hcount : IsInternallyCountable D) (hFcount : IsInternallyCountable F)
    (hUW : ∀ U W, ⟨U, W⟩ₖ ∈ F → IsCodedInseparable (binaryRelationStructureCode D R) U W)
    (hj : j ∈ (ω : V) ^ structureDomain (binaryRelationStructureCode D R)) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex (binaryRelationStructureCode D R)) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k)
    (hfr : HasFreshBackgroundNames j (namedUpperBackground (binaryRelationStructureCode D R) j k))
    (hfiniteDense : let M := binaryRelationStructureCode D R
      let P := namedFiniteConditions membershipLanguageCode M j (namedUpperBackground M j k)
      ∀ U ∈ namedFiniteOmissionFamily P M j, ForcingDense P (reverseInclusionOrder P) U)
    (hseparationDense : let M := binaryRelationStructureCode D R
      let P := namedFiniteConditions membershipLanguageCode M j (namedUpperBackground M j k)
      ∀ U ∈ namedSeparationOmissionFamily P j F, ForcingDense P (reverseInclusionOrder P) U) :
    ∃ N e c : V, (∃ A S, N = binaryRelationStructureCode A S ∧ S ⊆ A ×ˢ A) ∧
      IsCodedZFModel N ∧ IsInternallyCountable (structureDomain N) ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R) N e ∧
      IsCodedCofinalBounds (binaryRelationStructureCode D R) N e c ∧
      IsCodedFiniteTraceEmbedding (binaryRelationStructureCode D R) N e ∧
      ∀ U W, ⟨U, W⟩ₖ ∈ F → IsCodedInseparable N (graphImage e U) (graphImage e W) := by
  let M := binaryRelationStructureCode D R
  let B := namedUpperBackground M j k
  let P := namedFiniteConditions membershipLanguageCode M j B
  let E := namedFiniteOmissionFamily P M j ∪ namedSeparationOmissionFamily P j F
  have hD : IsNonempty D := by
    simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  have hjD : j ∈ (ω : V) ^ D := by simpa only [binaryRelationStructureCode_domain] using hj
  have hB : FinitelySourceRealized membershipLanguageCode M j B :=
    namedUpperBackground_finitelySourceRealized hAC hM.valid hj hji hk hki hdis
  have hE : IsInternallyCountable E := internallyCountable_union
    (namedFiniteOmissionFamily_countable (by simpa only [M, binaryRelationStructureCode_domain] using hcount))
    (namedSeparationOmissionFamily_countable hAC hFcount)
  have hdE : ∀ U ∈ E, ForcingDense P (reverseInclusionOrder P) U := by
    intro U hU
    rcases mem_union_iff.mp hU with hf | hs
    · exact hfiniteDense U hf
    · exact hseparationDense U hs
  have hfun : IsInternallyCountable (functionSymbols (membershipLanguageCode : V)) := by
    simpa [membershipLanguageCode] using (internallyCountable_empty (V := V))
  have hrel : IsInternallyCountable (relationSymbols (membershipLanguageCode : V)) := by
    have hc : IsInternallyCountable (2 : V) := internallyCountable_subset internallyCountable_omega
      (IsOrdinal.toIsTransitive.transitive (2 : V) (by simp))
    simpa [membershipLanguageCode] using hc
  obtain ⟨G, _, hT, hmeet⟩ := exists_completeNamedTheory_filter_with_extra hAC
    membershipLanguageCode_valid hfun hrel hj hB hfr hE hdE
  have hmeetFinite : ∀ U ∈ namedFiniteOmissionFamily P M j, ∃ A ∈ G, A ∈ U :=
    fun U hU ↦ hmeet U (mem_union_iff.mpr (Or.inl hU))
  have hmeetSeparation : ∀ U ∈ namedSeparationOmissionFamily P j F, ∃ A ∈ G, A ∈ U :=
    fun U hU ↦ hmeet U (mem_union_iff.mpr (Or.inr hU))
  have hdiagram := namedUpperBackground_diagram M j k
  refine ⟨namedTheoryModel (⋃ˢ G), compose j (namedTheoryProjection (⋃ˢ G)),
    compose k (namedTheoryProjection (⋃ˢ G)), namedTheoryModel_binary _,
    hT.model_codedZF hM hjD hdiagram, namedTheoryModel_countable _,
    hT.model_elementary hD hjD hdiagram, namedUpper_complete_model_bounds hD hj hk hT,
    hT.model_finiteTraceEmbedding_of_omissionFamily hD hjD hmeetFinite, ?_⟩
  intro U W hpair
  exact hT.model_preserves_inseparable_of_family hAC hD hjD hmeetSeparation hpair (hUW U W hpair)

end ZFVP.Schmerl
