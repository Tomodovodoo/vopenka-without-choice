import ZFVP.ModelTheory.SchmerlCodedRubinSuccessor
import ZFVP.ModelTheory.SchmerlCodedSuccessorTransport
import ZFVP.ModelTheory.InternalBinaryGraphRelabeling
import ZFVP.SetTheory.HartogsCountableRelabeling
import ZFVP.SetTheory.GraphImageComposition

/-! Normalize the constructed successor inside a fixed Hartogs carrier,
fixing every old point and including the current ordinal label. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_bounded_codedRubinSuccessor (hAC : InternalChoice V) (hω : HasStandardOmega V)
    {D R F α : V} (hM : IsCodedZFModel (binaryRelationStructureCode D R)) (hR : R ⊆ D ×ˢ D)
    (hDκ : D ⊆ hartogsNumber (ω : V)) (hα : α ∈ hartogsNumber (ω : V))
    (hcount : IsInternallyCountable D) (hFcount : IsInternallyCountable F)
    (hF : F ⊆ power D ×ˢ power D)
    (hUW : ∀ U W, ⟨U, W⟩ₖ ∈ F → IsCodedInseparable (binaryRelationStructureCode D R) U W) :
    ∃ B S c : V, D ⊆ B ∧ B ⊆ hartogsNumber (ω : V) ∧ α ∈ B ∧ S ⊆ B ×ˢ B ∧
      IsInternallyCountable B ∧ IsCodedZFModel (binaryRelationStructureCode B S) ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R)
        (binaryRelationStructureCode B S) (SetTheory.identity D) ∧
      IsCodedCofinalBounds (binaryRelationStructureCode D R) (binaryRelationStructureCode B S) (SetTheory.identity D) c ∧
      IsCodedFiniteEndExtension (binaryRelationStructureCode D R) (binaryRelationStructureCode B S) ∧
      ∀ U W, ⟨U, W⟩ₖ ∈ F → IsCodedInseparable (binaryRelationStructureCode B S) U W := by
  obtain ⟨N, e, c, ⟨A, E, rfl, _⟩, hN, hNc, he, hbound, htrace, hpres, hnew⟩ :=
    exists_codedRubinSuccessor hAC hω hM hR hcount hFcount hF hUW
  have hAc : IsInternallyCountable A := by simpa only [binaryRelationStructureCode_domain] using hNc
  have heA : e ∈ A ^ D := by simpa only [binaryRelationStructureCode_domain] using he.function
  obtain ⟨h, hh, hhi, hfix, hαh, hhc⟩ := exists_hartogsOmega_relabeling hAC hcount hDκ hAc heA he.injective hα
    (fun _ ↦ by simpa only [binaryRelationStructureCode_domain] using hnew)
  have hAh : IsNonempty A := by simpa only [binaryRelationStructureCode_domain] using hN.valid.domain_nonempty
  have hiso := binaryRelabel_elementary (E := E) hAh hh hhi
  have hrange : range h = structureDomain (binaryRelabelStructure E h) := by rw [binaryRelabelStructure_domain]
  have hDB : D ⊆ range h := by
    intro x hx
    rw [← hfix x hx]
    exact function_value_mem (function_mem_range_codomain hh) (function_value_mem heA hx)
  have hcomp : compose e h = SetTheory.identity D := by
    apply function_eq_of_values (compose_function heA (function_mem_range_codomain hh))
      (mem_function_of_mem_function_of_subset (identity_mem_function D) hDB)
    intro x hx
    rw [value_compose_of_mem_function heA (function_mem_range_codomain hh) hx, hfix x hx, identity_value hx]
  have hinc := he.comp hiso
  rw [hcomp] at hinc
  have hb := hbound.transport he.function hiso
  rw [hcomp] at hb
  have ht := htrace.transport he.function hiso hrange
  rw [hcomp] at ht
  refine ⟨range h, binaryRelabelEdges E h, compose c h, hDB, range_subset_of_mem_function hh, hαh,
    binaryRelabelEdges_subset E h, hhc, binaryRelabel_codedZF hN hh hhi, hinc, hb, ?_, ?_⟩
  · intro a ha hfin x hx hmem
    have haD : a ∈ D := by simpa only [binaryRelationStructureCode_domain] using ha
    have hmem' : codedMember (binaryRelabelStructure E h) x ((SetTheory.identity D) ‘ a) := by
      simpa only [identity_value haD, binaryRelabelStructure] using hmem
    have hhx := ht a ha hfin x hx hmem'
    simpa only [binaryRelationStructureCode_domain] using
      range_subset_of_mem_function (identity_mem_function D) x hhx
  · intro U W hpair
    have hp := (hpres U W hpair).transport hiso hrange
    rw [graphImage_compose, graphImage_compose, hcomp,
      graphImage_identity (by simpa only [binaryRelationStructureCode_domain] using (hUW U W hpair).1),
      graphImage_identity (by simpa only [binaryRelationStructureCode_domain] using (hUW U W hpair).2.1)] at hp
    exact hp

end ZFVP.Schmerl
