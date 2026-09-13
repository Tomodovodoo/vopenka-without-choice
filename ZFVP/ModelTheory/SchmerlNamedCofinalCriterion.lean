import ZFVP.ModelTheory.SchmerlNamedUpperFragments

/-! Exact cofinal realizability criterion for a finite named condition over
the full Rubin upper-bound background. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

def HasCofinalNamedRealizations (M j k A : V) : Prop :=
  ∀ H, IsInternallyFinite H → H ⊆ namedUpperDemands M →
    ∃ c ∈ structureDomain M ^ codedDirectedPosetIndex M,
      (∀ i ∈ codedDirectedPosetIndex M, c ‘ i ∈ (codedDirectedPosetDomains M) ‘ i) ∧
      (∀ i x, ⟨i, x⟩ₖ ∈ H → ⟨x, c ‘ i⟩ₖ ∈ (codedDirectedPosetRelations M) ‘ i) ∧
      ∃ f, ZFVP.SourceNaming M j f ∧ (∀ i ∈ codedDirectedPosetIndex M, f ‘ (k ‘ i) = c ‘ i) ∧
        ∀ p ∈ A, NamedHolds membershipLanguageCode M f p

instance hasCofinalNamedRealizations_definable : ℒₛₑₜ-relation₄[V] HasCofinalNamedRealizations := by
  unfold HasCofinalNamedRealizations
  definability

theorem cofinalNamedRealizations_of_finiteSource (hAC : InternalChoice V) {M j k A : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex M) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) (hA : IsInternallyFinite A)
    (h : FinitelySourceRealized membershipLanguageCode M j (namedUpperBackground M j k ∪ A)) :
    HasCofinalNamedRealizations M j k A := by
  have hAv : A ⊆ namedFormulaSet membershipLanguageCode (ω : V) :=
    fun p hp ↦ h.1 p (mem_union_iff.mpr (Or.inr hp))
  obtain ⟨n, hn, _, χ, _, hχ⟩ := exists_internal_namedConjunction hA hAv
  have hnω : n ⊆ (ω : V) := IsTransitive.ω.transitive n hn
  intro H hH hHD
  let J := namedUpperRelevantIndices M k n ∪ domain H
  have hJf : IsInternallyFinite J := internallyFinite_union
    (namedUpperRelevantIndices_finite hk hki ⟨n, hn, CardEQ.refl n⟩) (internallyFinite_domain hH)
  have hJI : J ⊆ codedDirectedPosetIndex M := by
    intro i hi
    rcases mem_union_iff.mp hi with hi | hi
    · exact (mem_sep_iff.mp hi).1
    · obtain ⟨x, hix⟩ := mem_domain_iff.mp hi
      exact ((pair_mem_namedUpperDemands M i x).mp (hHD _ hix)).1
  obtain ⟨f, hf, hAf, hJfP, hHf⟩ := upper_fragment_realization hj hk h hA hJf hJI hH hHD
  obtain ⟨c, hc, hmem, hagree⟩ := exists_upperAssignment_agree hAC hJI hJfP
  have : IsFunction f := IsFunction.of_mem hf.1
  have hbn : f ↾ n ∈ structureDomain M ^ n := function_restrict_mem hf.1 hnω
  have hbj : ∀ x ∈ structureDomain M, j ‘ x ∈ n → (f ↾ n) ‘ (j ‘ x) = x := by
    intro x hx hxn
    rw [value_restrict (by rw [domain_eq_of_mem_function hf.1]; exact function_value_mem hj hx) hxn]
    exact hf.2 x hx
  have hbk : ∀ i ∈ codedDirectedPosetIndex M, k ‘ i ∈ n → (f ↾ n) ‘ (k ‘ i) = c ‘ i := by
    intro i hi hin
    rw [value_restrict (by rw [domain_eq_of_mem_function hf.1]; exact function_value_mem hk hi) hin]
    exact (hagree i (mem_union_iff.mpr (Or.inl (mem_sep_iff.mpr ⟨hi, hin⟩)))).symm
  obtain ⟨g, hg, hgj, hgk, hgn⟩ := exists_jointSourceAssignment_extending hM.domain_nonempty
    hj hji hk hki hdis hc hnω hbn hbj hbk
  refine ⟨c, hc, hmem, ?_, g, ⟨hg, hgj⟩, hgk, ?_⟩
  · intro i x hix
    rw [hagree i (mem_union_iff.mpr (Or.inr (mem_domain_of_kpair_mem hix)))]
    exact hHf i x hix
  · apply (hχ M hM g hg).mpr
    rw [hgn]
    exact (hχ M hM f hf.1).mp hAf

theorem finiteSource_of_cofinalNamedRealizations {M j k A : V}
    (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex M) (hki : Injective k)
    (hA : A ⊆ namedFormulaSet membershipLanguageCode (ω : V))
    (h : HasCofinalNamedRealizations M j k A) :
    FinitelySourceRealized membershipLanguageCode M j (namedUpperBackground M j k ∪ A) := by
  refine ⟨?_, fun S hS hSB ↦ ?_⟩
  · intro p hp
    rcases mem_union_iff.mp hp with hp | hp
    · exact namedUpperBackground_valid hj hk p hp
    · exact hA p hp
  · have hHD : namedUpperFragmentDemands M j k S ⊆ namedUpperDemands M := fun _ hp ↦ (mem_sep_iff.mp hp).1
    obtain ⟨c, _, hmem, hbound, f, hf, hfk, hAf⟩ := h _
      (namedUpperFragmentDemands_finite hj hji hk hki hS) hHD
    refine ⟨f, hf, fun p hp ↦ ?_⟩
    rcases mem_union_iff.mp (hSB p hp) with hpB | hpA
    · rcases (mem_namedUpperBackground M j k p).mp hpB with
        hd | ⟨i, hi, rfl⟩ | ⟨i, hi, x, hx, rfl⟩
      · exact hf.diagram membershipLanguageCode_valid hj p hd
      · apply (SourceNaming.upperMember_iff hf (codedDirectedPosetIndex_spec hi).1 hj hk hi).mpr
        rw [hfk i hi, ← codedDirectedPosetDomains_value hi]
        exact hmem i hi
      · have hxD := mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) x hx
        apply (SourceNaming.upperOrder_iff hf (codedDirectedPosetIndex_spec hi).2.1 hj hk hi hxD).mpr
        rw [hfk i hi, ← codedDirectedPosetRelations_value hi]
        exact hbound i x ((pair_mem_namedUpperFragmentDemands M j k S i x).mpr ⟨⟨hi, hx⟩, hp⟩)
    · exact hAf p hpA

theorem finiteSource_iff_cofinalNamedRealizations (hAC : InternalChoice V) {M j k A : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex M) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) (hA : IsInternallyFinite A)
    (hAv : A ⊆ namedFormulaSet membershipLanguageCode (ω : V)) :
    FinitelySourceRealized membershipLanguageCode M j (namedUpperBackground M j k ∪ A) ↔
      HasCofinalNamedRealizations M j k A :=
  ⟨cofinalNamedRealizations_of_finiteSource hAC hM hj hji hk hki hdis hA,
    finiteSource_of_cofinalNamedRealizations hj hji hk hki hAv⟩

end ZFVP.Schmerl
