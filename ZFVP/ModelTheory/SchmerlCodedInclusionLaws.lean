import ZFVP.ModelTheory.SchmerlBoundedBinaryModelCodes
import ZFVP.ModelTheory.SchmerlCodedSuccessorTransport
import ZFVP.ModelTheory.SchmerlInternalCodedUnionPreservation

/-! Literal coded elementary inclusions compose, preserve unary formulas,
and supply the relation coherence needed by actual binary chain unions. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isCodedFiniteEndExtension_definable : ℒₛₑₜ-relation[V] IsCodedFiniteEndExtension :=
  isCodedFiniteEndExtensionFormula_defined.to_definable

abbrev IsCodedElementaryInclusion (M N : V) : Prop :=
  IsCodedElementaryEmbedding membershipLanguageCode M N (SetTheory.identity (structureDomain M))

namespace IsCodedElementaryInclusion
variable {M N P : V}

theorem subset (h : IsCodedElementaryInclusion M N) : structureDomain M ⊆ structureDomain N := by
  intro x hx
  simpa only [identity_value hx] using function_value_mem h.function hx

theorem trans (h : IsCodedElementaryInclusion M N) (g : IsCodedElementaryInclusion N P) :
    IsCodedElementaryInclusion M P := by
  have hh := h.comp g
  rw [graph_compose_identity h.function] at hh
  exact hh

theorem unary_iff (h : IsCodedElementaryInclusion M N) {φ a : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (1 : V)) (ha : a ∈ structureDomain M) :
    codedUnary M φ a ↔ codedUnary N φ a := by
  have hb : standardTuple ![a] ∈ structureDomain M ^ (1 : V) :=
    standardTuple_mem_function _ (by simp [ha])
  have hh := h.satisfies_iff (by simp) hφ hb
  rw [graph_compose_identity hb] at hh
  exact hh

theorem member_iff (h : IsCodedElementaryInclusion M N) {x a : V}
    (hx : x ∈ structureDomain M) (ha : a ∈ structureDomain M) :
    codedMember M x a ↔ codedMember N x a := by
  simpa only [identity_value hx, identity_value ha] using elementary_codedMember_iff h hx ha

theorem binary_coherent {κ : V} (h : IsCodedElementaryInclusion M N)
    (hM : M ∈ boundedBinaryModelCodes κ) (hN : N ∈ boundedBinaryModelCodes κ)
    {r s : V} (hr : r ∈ relationSymbols (membershipLanguageCode : V))
    (hs : s ∈ structureDomain M ^ ((relationArities (membershipLanguageCode : V)) ‘ r)) :
    s ∈ (structureRelations M) ‘ r ↔ s ∈ (structureRelations N) ‘ r := by
  obtain ⟨D, E, _, _, rfl⟩ := mem_boundedBinaryModelCodes.mp hM
  obtain ⟨B, R, _, _, rfl⟩ := mem_boundedBinaryModelCodes.mp hN
  have hr2 : r ∈ (2 : V) := by simpa only [membershipLanguageCode, relationSymbols_code] using hr
  have hsD : s ∈ D ^ (2 : V) := by
    simpa only [binaryRelationStructureCode_domain, membershipLanguageCode,
      relationArities_code, value_constantGraph _ _ hr2] using hs
  have hDB : D ⊆ B := by simpa only [binaryRelationStructureCode_domain] using h.subset
  have hsB : s ∈ B ^ (2 : V) := mem_function_of_mem_function_of_subset hsD hDB
  rcases (mem_two_iff r).mp hr2 with rfl | rfl
  · change s ∈ (structureRelations (binaryRelationStructureCode D E)) ‘ (0 : V) ↔
      s ∈ (structureRelations (binaryRelationStructureCode B R)) ‘ (0 : V)
    simp only [binaryRelationStructureCode_equality, mem_equalityRelation_iff,
      and_iff_right hsD, and_iff_right hsB]
  · change s ∈ (structureRelations (binaryRelationStructureCode D E)) ‘ (1 : V) ↔
      s ∈ (structureRelations (binaryRelationStructureCode B R)) ‘ (1 : V)
    rw [binaryRelationStructureCode_relation, binaryRelationStructureCode_relation,
      mem_binaryTupleRelation, mem_binaryTupleRelation, and_iff_right hsD, and_iff_right hsB]
    have hx := function_value_mem hsD (by simp : (0 : V) ∈ (2 : V))
    have hy := function_value_mem hsD (by simp : (1 : V) ∈ (2 : V))
    have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using h.source.domain_nonempty
    have hB : IsNonempty B := by simpa only [binaryRelationStructureCode_domain] using h.target.domain_nonempty
    have hx' : s ‘ (0 : V) ∈ structureDomain (binaryRelationStructureCode D E) := by simpa using hx
    have hy' : s ‘ (1 : V) ∈ structureDomain (binaryRelationStructureCode D E) := by simpa using hy
    exact (codedMember_binary_iff hD hx hy).symm.trans
      (h.member_iff hx' hy' |>.trans (codedMember_binary_iff hB (hDB _ hx) (hDB _ hy)))

end IsCodedElementaryInclusion

theorem IsCodedFiniteEndExtension.refl (M : V) : IsCodedFiniteEndExtension M M :=
  fun _ _ _ _ hx _ ↦ hx

theorem IsCodedFiniteEndExtension.trans {M N P : V}
    (hMN : IsCodedElementaryInclusion M N) (hNP : IsCodedElementaryInclusion N P)
    (hf : IsCodedFiniteEndExtension M N) (hg : IsCodedFiniteEndExtension N P) :
    IsCodedFiniteEndExtension M P := by
  intro a ha hfin x hx hmem
  have haN := hMN.subset a ha
  have hfinN := (hMN.unary_iff (encodeMembershipFormula_mem _) ha).mp hfin
  have hxN := hg a haN hfinN x hx hmem
  exact hf a ha hfin x hxN ((hNP.member_iff hxN haN).mpr hmem)

end ZFVP.Schmerl
