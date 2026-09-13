import ZFVP.ModelTheory.SchmerlNamedUpperBackground
import ZFVP.ModelTheory.SchmerlFiniteUpperBounds

/-! Every internally finite fragment of the actual cofinal background has an
actual source realization fixing all old names. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem namedUpperBackground_finitelySourceRealized (hAC : InternalChoice V) {M j k : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex M) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) :
    FinitelySourceRealized membershipLanguageCode M j (namedUpperBackground M j k) := by
  refine ⟨namedUpperBackground_valid hj hk, fun S hS hSB ↦ ?_⟩
  obtain ⟨c, hc, hmem, hupper⟩ := exists_finite_strict_upper_choice hAC (codedDirectedPosetDomains_mem M)
    (fun _ hi ↦ codedDirectedPosetFamily_poset hi) (fun _ hi ↦ codedDirectedPosetFamily_directed hi)
    (namedUpperFragmentDemands_finite hj hji hk hki hS)
    (namedUpperFragmentDemands_subset M j k S)
    (fun i x hp ↦ ((pair_mem_namedUpperFragmentDemands M j k S i x).mp hp).1.2)
  obtain ⟨f, hf, hfk⟩ := exists_jointSourceNaming hM.domain_nonempty hj hji hk hki hdis hc
  refine ⟨f, hf, fun p hp ↦ ?_⟩
  rcases (mem_namedUpperBackground M j k p).mp (hSB p hp) with
    hd | ⟨i, hi, rfl⟩ | ⟨i, hi, x, hx, rfl⟩
  · exact hf.diagram membershipLanguageCode_valid hj p hd
  · apply (SourceNaming.upperMember_iff hf (codedDirectedPosetIndex_spec hi).1 hj hk hi).mpr
    rw [hfk i hi, ← codedDirectedPosetDomains_value hi]
    exact hmem i hi
  · have hxD := mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) x hx
    apply (SourceNaming.upperOrder_iff hf (codedDirectedPosetIndex_spec hi).2.1 hj hk hi hxD).mpr
    rw [hfk i hi, ← codedDirectedPosetRelations_value hi]
    exact (hupper i x ((pair_mem_namedUpperFragmentDemands M j k S i x).mpr ⟨⟨hi, hx⟩, hp⟩)).1

theorem exists_namedUpperBackground (hAC : InternalChoice V) {M : V}
    (hM : IsStructureCode membershipLanguageCode M) (hcount : IsInternallyCountable (structureDomain M)) :
    ∃ j k, j ∈ (ω : V) ^ structureDomain M ∧ Injective j ∧
      k ∈ (ω : V) ^ codedDirectedPosetIndex M ∧ Injective k ∧
      (∀ n ∈ range j, n ∉ range k) ∧ HasFreshBackgroundNames j (namedUpperBackground M j k) ∧
      FinitelySourceRealized membershipLanguageCode M j (namedUpperBackground M j k) := by
  obtain ⟨j, k, hj, hji, hk, hki, hdis, hfresh⟩ :=
    exists_disjointSparseSourceNames hcount (codedDirectedPosetIndex_countable hAC hcount)
  exact ⟨j, k, hj, hji, hk, hki, hdis, hfresh _ (namedUpperBackground_support hj hk),
    namedUpperBackground_finitelySourceRealized hAC hM hj hji hk hki hdis⟩

end ZFVP.Schmerl
