import ZFVP.ModelTheory.SchmerlNamedCoordinateCriterion
import ZFVP.ModelTheory.SchmerlDirectedPosetFormulas
import ZFVP.ModelTheory.SchmerlFiniteUpperIndices
import ZFVP.ModelTheory.RubinFiniteIndexOmissionKernel

/-! First-order cofinal blocks exactly characterize finite source realizability
over the actual upper-bound background. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem coordinate_iff_finiteBlock {D E P R : V} {p : ℕ} (indices : Fin p → V)
    (δ : Fin p → SetTheorySemiformula (BinaryRelationDomain D E) 1)
    (ρ : Fin p → SetTheorySemiformula (BinaryRelationDomain D E) 2)
    (hδ : ∀ t (x : BinaryRelationDomain D E), (δ t).Eval ![x] id ↔ x.val ∈ P ‘ (indices t))
    (hρ : ∀ t (x y : BinaryRelationDomain D E), (ρ t).Eval ![x, y] id ↔
      ⟨x.val, y.val⟩ₖ ∈ R ‘ (indices t) ∧ x ≠ y)
    (B : (Fin p → BinaryRelationDomain D E) → Prop) :
    (∀ r : Fin p → BinaryRelationDomain D E, (∀ t, (r t).val ∈ P ‘ (indices t)) →
      ∃ s : Fin p → BinaryRelationDomain D E, (∀ t, (s t).val ∈ P ‘ (indices t)) ∧
        (∀ t, ⟨(r t).val, (s t).val⟩ₖ ∈ R ‘ (indices t) ∧ (r t).val ≠ (s t).val) ∧ B s) ↔
      FiniteBlockEx δ ρ B := by
  constructor
  · intro h r hr
    obtain ⟨s, hs, hrs, hBs⟩ := h r (fun t ↦ (hδ t _).mp (hr t))
    exact ⟨s, fun t ↦ (hδ t _).mpr (hs t), fun t ↦ (hρ t _ _).mpr
      ⟨(hrs t).1, fun he ↦ (hrs t).2 (congrArg Subtype.val he)⟩, hBs⟩
  · intro h r hr
    obtain ⟨s, hs, hrs, hBs⟩ := h r (fun t ↦ (hδ t _).mpr (hr t))
    exact ⟨s, fun t ↦ (hδ t _).mp (hs t), fun t ↦
      ⟨((hρ t _ _).mp (hrs t)).1, fun he ↦ ((hρ t _ _).mp (hrs t)).2 (Subtype.ext he)⟩, hBs⟩

theorem finiteSource_iff_finiteBlock (hAC : InternalChoice V)
    {D E j k A : V} {p : ℕ} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)) (hki : Injective k)
    (hdis : ∀ n ∈ range j, n ∉ range k) (hA : IsInternallyFinite A)
    (hAv : A ⊆ namedFormulaSet membershipLanguageCode (ω : V))
    (indices : Fin p → V)
    (hi : ∀ t, indices t ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E))
    (hinj : Function.Injective indices)
    (δ : Fin p → SetTheorySemiformula (BinaryRelationDomain D E) 1)
    (ρ : Fin p → SetTheorySemiformula (BinaryRelationDomain D E) 2)
    (hδ : ∀ t (x : BinaryRelationDomain D E), (δ t).Eval ![x] id ↔
      x.val ∈ (codedDirectedPosetDomains (binaryRelationStructureCode D E)) ‘ (indices t))
    (hρ : ∀ t (x y : BinaryRelationDomain D E), (ρ t).Eval ![x, y] id ↔
      ⟨x.val, y.val⟩ₖ ∈ (codedDirectedPosetRelations (binaryRelationStructureCode D E)) ‘ (indices t) ∧ x ≠ y)
    (B : (Fin p → BinaryRelationDomain D E) → Prop)
    (hB : ∀ (c : V) (hc : c ∈ D ^ codedDirectedPosetIndex (binaryRelationStructureCode D E)),
      B (fun t ↦ ⟨c ‘ (indices t), function_value_mem hc (hi t)⟩) ↔
        ∃ f, ZFVP.SourceNaming (binaryRelationStructureCode D E) j f ∧
          (∀ i ∈ codedDirectedPosetIndex (binaryRelationStructureCode D E), f ‘ (k ‘ i) = c ‘ i) ∧
          ∀ q ∈ A, NamedHolds membershipLanguageCode (binaryRelationStructureCode D E) f q) :
    FinitelySourceRealized membershipLanguageCode (binaryRelationStructureCode D E) j
      (namedUpperBackground (binaryRelationStructureCode D E) j k ∪ A) ↔ FiniteBlockEx δ ρ B :=
  (finiteSource_iff_coordinate hAC hD hj hji hk hki hdis hA hAv indices hi hinj B hB).trans
    (coordinate_iff_finiteBlock indices δ ρ hδ hρ B)

end ZFVP.Schmerl
