import ZFVP.ModelTheory.SchmerlCodedOmittingSuccessor
import ZFVP.ModelTheory.SchmerlNamedSeparationDensity
import ZFVP.ModelTheory.SchmerlNamedFiniteDensity
import ZFVP.ModelTheory.SchmerlCodedProperSuccessor

/-! The actual Rubin successor: both omission families are proved dense, then
one internal filter constructs the countable model with all required properties. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_codedRubinSuccessor (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {D R F : V} (hM : IsCodedZFModel (binaryRelationStructureCode D R)) (hR : R ⊆ D ×ˢ D)
    (hcount : IsInternallyCountable D) (hFcount : IsInternallyCountable F)
    (hF : F ⊆ power D ×ˢ power D)
    (hUW : ∀ U W, ⟨U, W⟩ₖ ∈ F → IsCodedInseparable (binaryRelationStructureCode D R) U W) :
    ∃ N e c : V, (∃ A S, N = binaryRelationStructureCode A S ∧ S ⊆ A ×ˢ A) ∧
      IsCodedZFModel N ∧ IsInternallyCountable (structureDomain N) ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R) N e ∧
      IsCodedCofinalBounds (binaryRelationStructureCode D R) N e c ∧
      IsCodedFiniteTraceEmbedding (binaryRelationStructureCode D R) N e ∧
      (∀ U W, ⟨U, W⟩ₖ ∈ F → IsCodedInseparable N (graphImage e U) (graphImage e W)) ∧
      ∃ y ∈ structureDomain N, y ∉ range e := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  obtain ⟨j, k, hj, hji, hk, hki, hdis, hfr, _⟩ := exists_namedUpperBackground hAC hM.valid
    (by simpa only [binaryRelationStructureCode_domain] using hcount)
  have hjD : j ∈ (ω : V) ^ D := by simpa only [binaryRelationStructureCode_domain] using hj
  have hfiniteDense : let M := binaryRelationStructureCode D R
      let P := namedFiniteConditions membershipLanguageCode M j (namedUpperBackground M j k)
      ∀ U ∈ namedFiniteOmissionFamily P M j, ForcingDense P (reverseInclusionOrder P) U := by
    intro M P U hU
    obtain ⟨q, hq, rfl⟩ := (repl_spec _).mp hU
    obtain ⟨a, ha, l, hl, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hq).1
    have hf := ((pair_mem_namedFiniteOmissionTasks M a l).mp hq).2
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      namedFiniteOmissionDense_dense hAC hω hM hR hjD hji hk hki hdis
        (by simpa only [M, binaryRelationStructureCode_domain] using ha) hf hl
  have hseparationDense : let M := binaryRelationStructureCode D R
      let P := namedFiniteConditions membershipLanguageCode M j (namedUpperBackground M j k)
      ∀ U ∈ namedSeparationOmissionFamily P j F, ForcingDense P (reverseInclusionOrder P) U := by
    intro M P U hU
    obtain ⟨q, hq, rfl⟩ := (repl_spec _).mp hU
    obtain ⟨pair, hpF, t, ht, rfl⟩ := mem_prod_iff.mp hq
    obtain ⟨X, _, Y, _, rfl⟩ := mem_prod_iff.mp (hF pair hpF)
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      namedSeparationOmissionDense_dense hAC hω hD hjD hji hk hki hdis (hUW X Y hpF) ht
  obtain ⟨N, e, c, hbin, hN, hNc, he, hc, hfinite, hpres⟩ :=
    exists_codedCofinalOmittingSuccessor_of_namedDensities hAC hM hcount hFcount hUW
      hj hji hk hki hdis hfr hfiniteDense hseparationDense
  exact ⟨N, e, c, hbin, hN, hNc, he, hc, hfinite, hpres, hc.exists_new hR hM he⟩

end ZFVP.Schmerl
