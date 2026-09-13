import ZFVP.ModelTheory.InternalTheoryProofProgram
import ZFVP.Syntax.ClosedFormulaFreeDomain

/-! Soundness of complete internally coded proofs from the generated ZF+VP axioms. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem satisfies_closedNatural_free (U e : V) {c : V} (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement false).evalSet c) 0) :
    Satisfies membershipLanguageCode ω (membershipStructureCode U) e 0 (decodedNaturalFormula c) ∅ ↔
      MembershipSatisfies U 0 (decodedNaturalFormula c) ∅ := by
  have hφ := decodedNaturalFormula_valid false hc (n := (0 : V)) (by simp [zero_def]) hv
  have hs := (closedFormula_free ω (membershipStructureCode U) e ∅ hφ).2 ∅
    (by simp [mem_function_iff, zero_def])
  simpa only [MembershipSatisfies, membershipSatisfactionGraph, Satisfies] using hs

theorem not_satisfies_negated_trueSentence {U c : V} (hc : c ∈ (ω : V))
    (ht : NaturalSentenceTrue U c) (e : V) :
    ¬Satisfies membershipLanguageCode ω (membershipStructureCode U) e 0
      (decodedNaturalFormula (negateCode.evalSet c)) ∅ := by
  rw [satisfies_closedNatural_free U e (evalSet_natural negateCode hc)
    ((requirementFits_negateCode false hc).mpr ht.1),
    decodedNaturalFormula_negateCode false hc (by simp [zero_def]) ht.1]
  have hφ := decodedNaturalFormula_valid false hc (n := (0 : V)) (by simp [zero_def]) ht.1
  have hs := satisfies_negateFormula (M := membershipStructureCode U) (e := (∅ : V))
    membershipLanguageCode_valid hφ (b := ∅) (by simp [mem_function_iff, zero_def])
  change ¬Satisfies membershipLanguageCode ∅ (membershipStructureCode U) ∅ 0
    (negateFormula membershipLanguageCode ∅ 0 (decodedNaturalFormula c)) ∅
  exact fun hn ↦ hs.mp hn ht.2

theorem generatedAxiomRowsCheck_sound {U rows : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) (hr : rows ∈ (ω : V))
    (hcheck : generatedAxiomRowsCheck.evalSet (naturalSquarePair 0 rows) = 1) :
    ∀ row ∈ range (decodedNaturalList rows), NaturalSentenceTrue U (naturalSquareLeft row) := by
  intro row hrow
  have h := (evalSet_generatedAxiomRowsCheck (by simp [zero_def]) hr).mp hcheck row hrow
  obtain ⟨φ, hφ, w, hw, rfl⟩ := naturalSquarePair_surjective (mem_decodedNaturalList_range_natural hr hrow)
  rw [show naturalSquareLeft (naturalSquarePair φ w) = φ from
    congrArg Prod.fst (naturalSquareUnpair_pair hφ hw)]
  exact generatedAxiomCheck_sound hU hφ hw h

theorem generatedTheoryProofCheck_sound {U φ rows p : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes)
    (hφ : φ ∈ (ω : V)) (hr : rows ∈ (ω : V)) (hp : p ∈ (ω : V))
    (hcheck : generatedTheoryProofCheck.evalSet (naturalSquarePair φ (naturalSquarePair rows p)) = 1) :
    NaturalSentenceTrue U φ := by
  obtain ⟨hv, hax, hproof⟩ := (evalSet_generatedTheoryProofCheck hφ hr hp).mp hcheck
  have hall := generatedAxiomRowsCheck_sound hU hr hax
  have hseq := evalSet_lkProofCheck_sound (membershipStructureCode_valid hU.1)
    (evalSet_natural generatedTheorySequent (naturalSquarePair_natural hφ hr)) hp hproof
  obtain ⟨a, ha⟩ := hU.1.nonempty
  let e := constantGraph (ω : V) a
  have he : e ∈ structureDomain (membershipStructureCode U) ^ (ω : V) := by
    simpa only [membershipStructureCode_domain] using constantGraph_mem_function (ω : V) U a ha
  have hs := hseq e he
  rw [evalSet_generatedTheorySequent hφ hr,
    naturalSequentHolds_cons _ _ hφ (evalSet_natural _ (naturalSquarePair_natural (by simp [zero_def]) hr))] at hs
  refine ⟨hv, ?_⟩
  rcases hs with hs | ⟨c, hc, hs⟩
  · exact (satisfies_closedNatural_free U e hφ hv).mp hs
  · obtain ⟨row, hrow, rfl⟩ := (mem_range_decodedNaturalList_map negatedAxiomRow
      (by simp [zero_def]) hr c).mp hc
    rw [evalSet_negatedAxiomRow (by simp [zero_def]) (mem_decodedNaturalList_range_natural hr hrow)] at hs
    exact (not_satisfies_negated_trueSentence (naturalSquareLeft_natural row) (hall row hrow) e hs).elim

theorem generatedTheoryProofCheck_sound_raw {U φ p : V}
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) (hφ : φ ∈ (ω : V)) (hp : p ∈ (ω : V))
    (hcheck : generatedTheoryProofCheck.evalSet (naturalSquarePair φ p) = 1) : NaturalSentenceTrue U φ := by
  obtain ⟨rows, hr, cert, hc, rfl⟩ := naturalSquarePair_surjective hp
  exact generatedTheoryProofCheck_sound hU hφ hr hc hcheck

end ZFVP
