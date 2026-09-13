import ZFVP.ModelTheory.SchmerlInternalCodedFiniteTraces
import ZFVP.ModelTheory.InternalNamedSeparationOmission

/-! Inseparability and finite end-extension at actual internal chain unions.
The separator argument moves its full internal finite parameter tuple into
one stage; it makes no standardness assumption on its syntax or length. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedChainUnion_countable (hAC : InternalChoice V) {L θ C : V}
    (hθ : IsInternallyCountable θ)
    (hstage : ∀ i ∈ θ, IsInternallyCountable (structureDomain (C ‘ i))) :
    IsInternallyCountable (structureDomain (codedChainUnion L θ C)) := by
  rw [structureDomain_codedChainUnion]
  exact codedChainCarrier_countable hAC hθ hstage

namespace IsInternalRelationalChain
variable {θ C : V} (h : IsInternalRelationalChain membershipLanguageCode θ C)
include h

/-- A pair inseparable throughout a tail remains inseparable in the union. -/
theorem union_inseparable {i U W : V} (hi : i ∈ θ)
    (htail : ∀ j ∈ θ, i ⊆ j → IsCodedInseparable (C ‘ j) U W) :
    IsCodedInseparable (codedChainUnion membershipLanguageCode θ C) U W := by
  have hiUW := htail i hi (subset_refl _)
  have hU : U ⊆ structureDomain (codedChainUnion membershipLanguageCode θ C) := by
    rw [structureDomain_codedChainUnion]
    exact subset_trans hiUW.1 (codedChainCarrier_includes hi)
  have hW : W ⊆ structureDomain (codedChainUnion membershipLanguageCode θ C) := by
    rw [structureDomain_codedChainUnion]
    exact subset_trans hiUW.2.1 (codedChainCarrier_includes hi)
  refine ⟨hU, hW, ?_⟩
  rintro ⟨A, ⟨_, n, hn, φ, hφ, b, hb, hdef⟩, hUA, hWA⟩
  obtain ⟨j, hj, hbj⟩ := h.assignment_stage hn (by
    simpa only [structureDomain_codedChainUnion] using hb)
  obtain ⟨k, hk, hik, hjk⟩ := h.common hi hj
  have hbk : b ∈ structureDomain (C ‘ k) ^ n :=
    mem_function_of_mem_function_of_subset hbj (h.increasing j hj k hk hjk)
  have hkUW := htail k hk hik
  let S := {x ∈ structureDomain (C ‘ k) ; codedSatisfies (C ‘ k) (succ n) φ (assignmentPrepend n b x)}
  have hS : IsCodedDefinableSet (C ‘ k) S := by
    refine ⟨fun _ hx ↦ (mem_sep_iff.mp hx).1, n, hn, φ, hφ, b, hbk, ?_⟩
    intro x hx
    exact ⟨fun hs ↦ (mem_sep_iff.mp hs).2, fun hs ↦ mem_sep_iff.mpr ⟨hx, hs⟩⟩
  have he (x : V) (hx : x ∈ structureDomain (C ‘ k)) :
      codedSatisfies (C ‘ k) (succ n) φ (assignmentPrepend n b x) ↔
        codedSatisfies (codedChainUnion membershipLanguageCode θ C) (succ n) φ (assignmentPrepend n b x) :=
    h.satisfies_union_iff hk (ω_succ_closed hn) hφ (assignmentPrepend_mem_function hn hbk hx)
  apply hkUW.2.2
  refine ⟨S, hS, ?_, ?_⟩
  · intro x hx
    have hxk := hkUW.1 x hx
    exact mem_sep_iff.mpr ⟨hxk, (he x hxk).mpr ((hdef x (hU x hx)).mp (hUA x hx))⟩
  · intro x hx hxS
    have hxk := hkUW.2.1 x hx
    exact hWA x hx ((hdef x (hW x hx)).mpr ((he x hxk).mp (mem_sep_iff.mp hxS).2))

/-- Pairwise finite end-extension gives finite end-extension from every
stage to the actual union. -/
theorem stage_finiteEndExtension
    (hfreeze : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → IsCodedFiniteEndExtension (C ‘ i) (C ‘ j))
    {i : V} (hi : i ∈ θ) :
    IsCodedFiniteEndExtension (C ‘ i) (codedChainUnion membershipLanguageCode θ C) := by
  intro a ha hfin x hx hmem
  have hfinU := (h.codedUnary_union_iff hi ha (encodeMembershipFormula_mem _)).mp hfin
  exact h.finite_trace_subset_stage hfreeze hi ha hfinU x
    ((mem_codedMemberTrace _ _ _).mpr ⟨hx, hmem⟩)

theorem union_inseparable_binary {i U W : V} (hi : i ∈ θ)
    (htail : ∀ j ∈ θ, i ⊆ j → IsCodedInseparable (C ‘ j) U W)
    (heq : ∀ j ∈ θ, (structureRelations (C ‘ j)) ‘ (0 : V) = equalityRelation (structureDomain (C ‘ j))) :
    IsCodedInseparable (binaryRelationStructureCode (codedChainCarrier θ C) (codedChainEdges θ C)) U W := by
  rw [← h.union_eq_binaryRelationStructureCode heq]
  exact h.union_inseparable hi htail

theorem stage_finiteEndExtension_binary
    (hfreeze : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → IsCodedFiniteEndExtension (C ‘ i) (C ‘ j))
    (heq : ∀ j ∈ θ, (structureRelations (C ‘ j)) ‘ (0 : V) = equalityRelation (structureDomain (C ‘ j)))
    {i : V} (hi : i ∈ θ) :
    IsCodedFiniteEndExtension (C ‘ i)
      (binaryRelationStructureCode (codedChainCarrier θ C) (codedChainEdges θ C)) := by
  rw [← h.union_eq_binaryRelationStructureCode heq]
  exact h.stage_finiteEndExtension hfreeze hi

end IsInternalRelationalChain
end ZFVP.Schmerl
