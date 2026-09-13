import ZFVP.ModelTheory.SchmerlNamedCofinalCriterion
import ZFVP.ModelTheory.SchmerlFiniteCoordinateCofinality

/-! The exact finite-condition criterion on any fixed finite coordinate
list, using a body that represents joint source-name realization. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_upperTupleAssignment {D E I : V} {p : ℕ} (hD : IsNonempty D)
    (indices : Fin p → V) (hi : ∀ t, indices t ∈ I) (hinj : Function.Injective indices)
    (s : Fin p → BinaryRelationDomain D E) :
    ∃ (c : V) (hc : c ∈ D ^ I),
      (fun t ↦ (⟨c ‘ (indices t), function_value_mem hc (hi t)⟩ : BinaryRelationDomain D E)) = s := by
  obtain ⟨d, hd⟩ := hD
  let f := definableGraph I (fun _ ↦ d) (by definability)
  have hf : f ∈ D ^ I := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ hd)
  obtain ⟨c, hc, hcs, _⟩ := exists_internal_finiteCoordinateUpdate hf indices hi hinj
    (fun t ↦ (s t).val) (fun t ↦ (s t).property)
  refine ⟨c, hc, funext (fun t ↦ Subtype.ext (hcs t))⟩

theorem cofinalNamedRealizations_iff_coordinate (hAC : InternalChoice V)
    {D E j k A : V} {p : ℕ}
    (indices : Fin p → V)
    (hi : ∀ t, indices t ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E))
    (hinj : Function.Injective indices)
    (B : (Fin p → BinaryRelationDomain D E) → Prop)
    (hB : ∀ (c : V) (hc : c ∈ D ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)),
      B (fun t ↦ ⟨c ‘ (indices t), function_value_mem hc (hi t)⟩) ↔
        ∃ f, ZFVP.SourceNaming (binaryRelationStructureCode D E) j f ∧
          (∀ i ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E), f ‘ (k ‘ i) = c ‘ i) ∧
          ∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f q) :
    HasCofinalNamedRealizations (binaryRelationStructureCode D E) j k A ↔
      ∀ r : Fin p → BinaryRelationDomain D E,
        (∀ t, (r t).val ∈ (codedDirectedPosetDomains (binaryRelationStructureCode D E)) ‘ (indices t)) →
        ∃ s : Fin p → BinaryRelationDomain D E,
          (∀ t, (s t).val ∈ (codedDirectedPosetDomains (binaryRelationStructureCode D E)) ‘ (indices t)) ∧
          (∀ t, ⟨(r t).val, (s t).val⟩ₖ ∈ (codedDirectedPosetRelations (binaryRelationStructureCode D E)) ‘ (indices t) ∧
            (r t).val ≠ (s t).val) ∧ B s := by
  have hP : codedDirectedPosetDomains (binaryRelationStructureCode D E) ∈
      power D ^ codedDirectedPosetIndex (binaryRelationStructureCode D E) := by
    simpa only [binaryRelationStructureCode_domain] using codedDirectedPosetDomains_mem (binaryRelationStructureCode D E)
  rw [← finiteCoordinate_cofinal_iff hAC hP (fun _ hi ↦ codedDirectedPosetFamily_poset hi)
    (fun _ hi ↦ codedDirectedPosetFamily_directed hi) indices hi hinj B]
  constructor
  · intro h H hH hHD hvalid
    have hdem : H ⊆ namedUpperDemands (binaryRelationStructureCode D E) := by
      intro z hz
      obtain ⟨i, hiI, x, _, rfl⟩ := mem_prod_iff.mp (hHD z hz)
      exact (pair_mem_namedUpperDemands _ _ _).mpr ⟨hiI, hvalid i x hz⟩
    obtain ⟨c, hc, hmem, hbound, hf⟩ := h H hH hdem
    have hc' : c ∈ D ^ codedDirectedPosetIndex (binaryRelationStructureCode D E) := by simpa using hc
    exact ⟨c, hc', hmem, hbound, (hB c hc').mpr hf⟩
  · intro h H hH hHD
    have hsub : H ⊆ codedDirectedPosetIndex (binaryRelationStructureCode D E) ×ˢ D := by
      intro z hz
      simpa only [binaryRelationStructureCode_domain] using
        namedUpperDemands_subset _ z (hHD z hz)
    obtain ⟨c, hc, hmem, hbound, hBc⟩ := h H hH hsub
      (fun i x hx ↦ ((pair_mem_namedUpperDemands _ _ _).mp (hHD _ hx)).2)
    exact ⟨c, by simpa using hc, hmem, hbound, (hB c hc).mp hBc⟩

theorem finiteSource_iff_coordinate (hAC : InternalChoice V)
    {D E j k A : V} {p : ℕ} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) (hA : IsInternallyFinite A)
    (hAv : A ⊆ namedFormulaSet membershipLanguageCode (ω : V))
    (indices : Fin p → V)
    (hi : ∀ t, indices t ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E))
    (hinj : Function.Injective indices)
    (B : (Fin p → BinaryRelationDomain D E) → Prop)
    (hB : ∀ (c : V) (hc : c ∈ D ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)),
      B (fun t ↦ ⟨c ‘ (indices t), function_value_mem hc (hi t)⟩) ↔
        ∃ f, ZFVP.SourceNaming (binaryRelationStructureCode D E) j f ∧
          (∀ i ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E), f ‘ (k ‘ i) = c ‘ i) ∧
          ∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f q) :
    FinitelySourceRealized membershipLanguageCode (binaryRelationStructureCode D E) j
      (namedUpperBackground (binaryRelationStructureCode D E) j k ∪ A) ↔
      ∀ r : Fin p → BinaryRelationDomain D E,
        (∀ t, (r t).val ∈ (codedDirectedPosetDomains (binaryRelationStructureCode D E)) ‘ (indices t)) →
        ∃ s : Fin p → BinaryRelationDomain D E,
          (∀ t, (s t).val ∈ (codedDirectedPosetDomains (binaryRelationStructureCode D E)) ‘ (indices t)) ∧
          (∀ t, ⟨(r t).val, (s t).val⟩ₖ ∈ (codedDirectedPosetRelations (binaryRelationStructureCode D E)) ‘ (indices t) ∧
            (r t).val ≠ (s t).val) ∧ B s := by
  have hj' : j ∈ (ω : V) ^ structureDomain (binaryRelationStructureCode D E) := by simpa using hj
  exact (finiteSource_iff_cofinalNamedRealizations hAC (binaryRelationStructureCode_valid hD E)
    hj' hji hk hki hdis hA hAv).trans (cofinalNamedRealizations_iff_coordinate hAC indices hi hinj B hB)

end ZFVP.Schmerl
