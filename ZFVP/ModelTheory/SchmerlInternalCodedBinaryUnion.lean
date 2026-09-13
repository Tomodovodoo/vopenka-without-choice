import ZFVP.ModelTheory.SchmerlInternalCodedChainElementarity
import ZFVP.ModelTheory.BinaryRelationStructure

/-! The relational chain union is an actual binary-relation structure code.
Its edge set is constructed internally from the union relation interpretation. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def codedChainEdges (θ C : V) : V :=
  repl (fun s ↦ ⟨s ‘ (0 : V), s ‘ (1 : V)⟩ₖ) (by definability) (codedChainRelation θ C 1)

theorem mem_codedChainEdges (θ C p : V) :
    p ∈ codedChainEdges θ C ↔ ∃ s ∈ codedChainRelation θ C 1,
      p = ⟨s ‘ (0 : V), s ‘ (1 : V)⟩ₖ := by
  simp only [codedChainEdges, repl_spec]

instance codedChainEdges_definable : ℒₛₑₜ-function₂[V] codedChainEdges := by
  have h : ℒₛₑₜ-relation₃[V] (fun E θ C ↦ ∀ p, p ∈ E ↔
      ∃ s, (∃ i ∈ θ, s ∈ (structureRelations (C ‘ i)) ‘ (1 : V)) ∧
        p = ⟨s ‘ (0 : V), s ‘ (1 : V)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedChainEdges, mem_codedChainRelation]
  rfl

namespace IsInternalRelationalChain

variable {θ C : V} (h : IsInternalRelationalChain membershipLanguageCode θ C)

include h

theorem membership_tuple_mem {r s : V} (hr : r ∈ (2 : V))
    (hs : s ∈ codedChainRelation θ C r) : s ∈ codedChainCarrier θ C ^ (2 : V) := by
  have hr' : r ∈ relationSymbols (membershipLanguageCode : V) := by
    simpa only [membershipLanguageCode, relationSymbols_code] using hr
  have hs' : s ∈ (structureRelations (codedChainUnion membershipLanguageCode θ C)) ‘ r := by
    rwa [codedChainUnion_relation hr']
  have ht := h.union_valid.relation_tuple_mem hr' hs'
  simpa only [structureDomain_codedChainUnion, membershipLanguageCode,
    relationArities_code, value_constantGraph _ _ hr] using ht

theorem edges_subset : codedChainEdges θ C ⊆ codedChainCarrier θ C ×ˢ codedChainCarrier θ C := by
  intro p hp
  obtain ⟨s, hs, rfl⟩ := (mem_codedChainEdges _ _ _).mp hp
  have ht := h.membership_tuple_mem (by simp : (1 : V) ∈ (2 : V)) hs
  exact kpair_mem_iff.mpr ⟨function_value_mem ht (by simp), function_value_mem ht (by simp)⟩

theorem union_equality
    (heq : ∀ i ∈ θ, (structureRelations (C ‘ i)) ‘ (0 : V) = equalityRelation (structureDomain (C ‘ i))) :
    codedChainRelation θ C 0 = equalityRelation (codedChainCarrier θ C) := by
  apply mem_ext
  intro s
  constructor
  · intro hs
    obtain ⟨i, hi, hsi⟩ := (mem_codedChainRelation _ _ _ _).mp hs
    rw [heq i hi, mem_equalityRelation_iff] at hsi
    exact (mem_equalityRelation_iff _ _).mpr
      ⟨mem_function_of_mem_function_of_subset hsi.1 (codedChainCarrier_includes hi), hsi.2⟩
  · intro hs
    obtain ⟨hs, he⟩ := (mem_equalityRelation_iff _ _).mp hs
    obtain ⟨i, hi, hsi⟩ := h.assignment_stage (by simp) hs
    apply (mem_codedChainRelation _ _ _ _).mpr
    exact ⟨i, hi, (heq i hi).symm ▸ (mem_equalityRelation_iff _ _).mpr ⟨hsi, he⟩⟩

theorem union_binaryRelation :
    codedChainRelation θ C 1 = binaryTupleRelation (codedChainCarrier θ C) (codedChainEdges θ C) := by
  apply mem_ext
  intro s
  constructor
  · intro hs
    exact (mem_binaryTupleRelation _ _ _).mpr
      ⟨h.membership_tuple_mem (by simp) hs, (mem_codedChainEdges _ _ _).mpr ⟨s, hs, rfl⟩⟩
  · intro hs
    obtain ⟨hs, he⟩ := (mem_binaryTupleRelation _ _ _).mp hs
    obtain ⟨t, ht, he⟩ := (mem_codedChainEdges _ _ _).mp he
    have htf := h.membership_tuple_mem (by simp) ht
    let : IsFunction s := IsFunction.of_mem hs
    let : IsFunction t := IsFunction.of_mem htf
    have hst : s = t := by
      apply function_ext hs htf
      intro i hi y _ hiy
      have hv : s ‘ i = t ‘ i := by
        rcases (mem_two_iff i).mp hi with rfl | rfl
        · exact (kpair_inj he).1
        · exact (kpair_inj he).2
      exact kpair_mem_iff_value.mpr
        ⟨by simpa only [domain_eq_of_mem_function htf] using hi, hv.symm.trans (value_eq_of_kpair_mem hiy)⟩
    exact hst ▸ ht

theorem union_eq_binaryRelationStructureCode
    (heq : ∀ i ∈ θ, (structureRelations (C ‘ i)) ‘ (0 : V) = equalityRelation (structureDomain (C ‘ i))) :
    codedChainUnion membershipLanguageCode θ C =
      binaryRelationStructureCode (codedChainCarrier θ C) (codedChainEdges θ C) := by
  have hv : ∀ r ∈ (2 : V), codedChainRelation θ C r =
      binaryRelationInterpretation (codedChainCarrier θ C) (codedChainEdges θ C) r := by
    intro r hr
    rcases (mem_two_iff r).mp hr with rfl | rfl
    · simpa only [binaryRelationInterpretation, ite_true] using h.union_equality heq
    · simpa only [binaryRelationInterpretation, SetTheory.one_ne_zero, ite_false] using h.union_binaryRelation
  unfold codedChainUnion binaryRelationStructureCode
  simp only [membershipLanguageCode, relationSymbols_code]
  congr 1
  apply mem_ext
  intro p
  simp only [mem_definableGraph_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, congrArg (fun R ↦ ⟨r, R⟩ₖ) (hv r hr)⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, congrArg (fun R ↦ ⟨r, R⟩ₖ) (hv r hr).symm⟩

theorem stage_elementary_binaryUnion
    (heq : ∀ i ∈ θ, (structureRelations (C ‘ i)) ‘ (0 : V) = equalityRelation (structureDomain (C ‘ i)))
    {i : V} (hi : i ∈ θ) :
    IsCodedElementaryEmbedding membershipLanguageCode (C ‘ i)
      (binaryRelationStructureCode (codedChainCarrier θ C) (codedChainEdges θ C))
      (SetTheory.identity (structureDomain (C ‘ i))) := by
  rw [← h.union_eq_binaryRelationStructureCode heq]
  exact h.stage_elementary hi

theorem stage_elementary_binaryUnion_of_binary_stages
    (hbinary : ∀ i ∈ θ, ∃ D E, C ‘ i = binaryRelationStructureCode D E)
    {i : V} (hi : i ∈ θ) :
    IsCodedElementaryEmbedding membershipLanguageCode (C ‘ i)
      (binaryRelationStructureCode (codedChainCarrier θ C) (codedChainEdges θ C))
      (SetTheory.identity (structureDomain (C ‘ i))) := by
  apply h.stage_elementary_binaryUnion ?_ hi
  intro j hj
  obtain ⟨D, E, he⟩ := hbinary j hj
  simp only [he, binaryRelationStructureCode_equality, binaryRelationStructureCode_domain]

end IsInternalRelationalChain
end ZFVP.Schmerl
