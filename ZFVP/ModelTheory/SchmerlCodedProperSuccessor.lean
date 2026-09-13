import ZFVP.ModelTheory.SchmerlCodedCofinalSuccessor
import ZFVP.ModelTheory.SchmerlCodedCofinalOrdinals

/-! Strict cofinal bounds produce an actual point outside the old embedding.
The ordinal poset supplies a concrete index in every coded ZF source. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedDirectedPosetIndex_nonempty {D E : V}
    (hD : IsNonempty D) (hE : E ⊆ D ×ˢ D)
    (hM : IsCodedZFModel (binaryRelationStructureCode D E)) :
    IsNonempty (codedDirectedPosetIndex (binaryRelationStructureCode D E)) := by
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let R : BinaryRelationRepresentation (V := V) (BinaryRelationDomain D E) :=
    ⟨D, E, hD, hE, Equiv.refl _, fun _ _ ↦ Iff.rfl⟩
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hM
  obtain ⟨i, hi, _, _⟩ := codedDirectedPosetFamily_complete
    (codedUnarySet_isCodedDefinable R.code ordinalNodeFormula)
    R.ordinalOrder_isCodedDefinable R.ordinalOrder_poset R.ordinals_directedNoMax
  exact ⟨i, hi⟩

theorem IsCodedCofinalBounds.outside_range {M N e c i : V}
    (h : IsCodedCofinalBounds M N e c)
    (he : IsCodedElementaryEmbedding membershipLanguageCode M N e)
    (hi : i ∈ codedDirectedPosetIndex M) : c ‘ i ∉ range e := by
  intro hc
  obtain ⟨x, hxc⟩ := mem_range_iff.mp hc
  have hx : x ∈ structureDomain M := by
    rw [← domain_eq_of_mem_function he.function]
    exact mem_domain_of_kpair_mem hxc
  let : IsFunction e := IsFunction.of_mem he.function
  have hval : e ‘ x = c ‘ i := value_eq_of_kpair_mem hxc
  have hcP := (h.2 i hi).1
  rw [← hval] at hcP
  have hxP := (elementary_unaryDefinition_iff he (codedDirectedPosetIndex_spec hi).1 hx).mpr hcP
  rw [← codedDirectedPosetDomains_value hi] at hxP
  exact (h.2 i hi).2 x hxP |>.2 hval

theorem IsCodedCofinalBounds.exists_new {D E N e c : V}
    (hE : E ⊆ D ×ˢ D) (hM : IsCodedZFModel (binaryRelationStructureCode D E))
    (he : IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E) N e)
    (h : IsCodedCofinalBounds (binaryRelationStructureCode D E) N e c) :
    ∃ y ∈ structureDomain N, y ∉ range e := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  obtain ⟨i, hi⟩ := codedDirectedPosetIndex_nonempty hD hE hM
  exact ⟨c ‘ i, function_value_mem h.1 hi, h.outside_range he hi⟩

end ZFVP.Schmerl
