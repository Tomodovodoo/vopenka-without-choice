import ZFVP.ModelTheory.SchmerlInternalCodedSkolem

/-! Internal countable downward Löwenheim–Skolem for arbitrary language
and structure codes, with elementarity for every internally finite formula. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_countable_coded_elementary_substructure (hAC : InternalChoice V) {L M A : V}
    (hM : IsStructureCode L M) (hF : IsInternallyCountable (functionSymbols L))
    (hR : IsInternallyCountable (relationSymbols L))
    (hA : A ⊆ structureDomain M) (hAc : IsInternallyCountable A) :
    ∃ B, A ⊆ B ∧ B ⊆ structureDomain M ∧ IsInternallyCountable B ∧
      IsCodedElementaryEmbedding L (codedRestriction L M B) M (SetTheory.identity B) := by
  obtain ⟨a, ha⟩ := hM.domain_nonempty.nonempty
  obtain ⟨g, _, _, hg⟩ := exists_codedSkolemOperator hAC hM
  let F : V → V → V := fun i s ↦ g ‘ ⟨i, s⟩ₖ
  have hFd : ℒₛₑₜ-function₂[V] F := by unfold F; definability
  let B := finiteOperationHull (codedSkolemIndices L) F hFd (insert a A)
  have hstart : insert a A ⊆ structureDomain M := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ha
    · exact hA x hx
  have hBD : B ⊆ structureDomain M :=
    finiteOperationHull_subset _ F hFd hstart (fun i hi s hs ↦ (hg i hi s hs).1)
  have hAB : A ⊆ B := subset_trans
    (fun _ hx ↦ mem_insert.mpr (Or.inr hx)) (subset_finiteOperationHull _ _ _ _)
  have hBc : IsInternallyCountable B := finiteOperationHull_countable hAC
    (codedSkolemIndices_countable hAC hM.language hF hR) (internallyCountable_insert hAc a) F hFd
  have hBne : IsNonempty B :=
    ⟨a, subset_finiteOperationHull _ _ _ _ a (mem_insert.mpr (Or.inl rfl))⟩
  have hclosed {i s : V} (hi : i ∈ codedSkolemIndices L) (hs : s ∈ finiteSequences B) : F i s ∈ B :=
    finiteOperationHull_closed _ _ _ _ hi hs
  have hfunction : IsCodedFunctionClosed L M B := by
    intro f hf s hs
    have hi := codedSkolemIndices_function hf
    have hsf : s ∈ finiteSequences B :=
      (mem_finiteSequences_iff _ _).mpr ⟨_, hM.language.function_arity_natural hf, hs⟩
    have hsD := mem_function_of_mem_function_of_subset hs hBD
    have hsDf : s ∈ finiteSequences (structureDomain M) :=
      (mem_finiteSequences_iff _ _).mpr ⟨_, hM.language.function_arity_natural hf, hsD⟩
    have hr := (hg ⟨0, f⟩ₖ hi s hsDf).2
      ⟨((structureFunctions M) ‘ f) ‘ s, hM.function_value_mem hf hsD,
        (codedSkolemRequest_function L M f s _).mpr rfl⟩
    have he : F ⟨0, f⟩ₖ s = ((structureFunctions M) ‘ f) ‘ s :=
      (codedSkolemRequest_function L M f s _).mp hr
    exact he ▸ hclosed hi hsf
  have hwitness : IsCodedWitnessClosed L M B := by
    intro n hn φ hφ b hb
    have hbf : b ∈ finiteSequences B := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hb⟩
    have hbD := mem_function_of_mem_function_of_subset hb hBD
    have hbDf : b ∈ finiteSequences (structureDomain M) := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hbD⟩
    constructor
    · intro hex
      have hi := codedSkolemIndices_formula hn hφ (show (1 : V) ∈ (ω : V) from by simp)
      have hr := (hg ⟨1, ⟨n, φ⟩ₖ⟩ₖ hi b hbDf).2 (by
        obtain ⟨x, hx, hxs⟩ := hex
        exact ⟨x, hx, (codedSkolemRequest_positive L M n φ b x).mpr hxs⟩)
      exact ⟨F ⟨1, ⟨n, φ⟩ₖ⟩ₖ b, hclosed hi hbf,
        (codedSkolemRequest_positive L M n φ b _).mp hr⟩
    · intro hex
      have hi := codedSkolemIndices_formula hn hφ (show (2 : V) ∈ (ω : V) from by simp)
      have hr := (hg ⟨2, ⟨n, φ⟩ₖ⟩ₖ hi b hbDf).2 (by
        obtain ⟨x, hx, hxs⟩ := hex
        exact ⟨x, hx, (codedSkolemRequest_negative L M n φ b x).mpr hxs⟩)
      exact ⟨F ⟨2, ⟨n, φ⟩ₖ⟩ₖ b, hclosed hi hbf,
        (codedSkolemRequest_negative L M n φ b _).mp hr⟩
  exact ⟨B, hAB, hBD, hBc, codedRestriction_elementary hM hBD hBne hfunction hwitness⟩

theorem exists_countable_coded_elementary_embedding (hAC : InternalChoice V) {L M : V}
    (hM : IsStructureCode L M) (hF : IsInternallyCountable (functionSymbols L))
    (hR : IsInternallyCountable (relationSymbols L)) :
    ∃ N f, IsInternallyCountable (structureDomain N) ∧ IsCodedElementaryEmbedding L N M f := by
  obtain ⟨B, _, _, hB, he⟩ := exists_countable_coded_elementary_substructure hAC hM hF hR
    (empty_subset _) internallyCountable_empty
  exact ⟨codedRestriction L M B, SetTheory.identity B,
    by simpa only [structureDomain_codedRestriction] using hB, he⟩

end ZFVP.Schmerl
