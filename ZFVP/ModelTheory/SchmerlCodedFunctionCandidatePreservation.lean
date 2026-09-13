import ZFVP.ModelTheory.SchmerlCodedFunctionCandidates
import ZFVP.ModelTheory.SchmerlCodedFunctionTransport
import ZFVP.SetTheory.EndExtensionHierarchyAgreement

/-! Preserved selected branches recover original-language definitions of
the exact full function candidates appearing in the uniform sentence. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation
open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V U : Type*} [SetStructure V] [SetStructure U]
  [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) (j : MembershipEndExtension V U) (s : W)
variable {κ c : V} [IsOrdinal κ]
variable (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val)
  (codedFiniteDomainOrder R.code (R.equiv s).val) c)
variable (hRubin : IsCodedRubin R.code κ)
variable (hpres : ∀ B : U,
  IsInternalCofinalBranch (j (codedSelectedFunctionNodes R.code (R.equiv s).val κ c))
    (j (codedSelectedFunctionOrder R.code (R.equiv s).val κ c)) (j κ)
    (j (codedSelectedFunctionRank R.code (R.equiv s).val κ c)) B →
  ∃ C : V, IsInternalCofinalBranch (codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
    (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) κ
    (codedSelectedFunctionRank R.code (R.equiv s).val κ c) C ∧ j C = B)

include hc hRubin hpres

theorem codedFunctionCandidate_eq_ground_definition {g b : U}
    (hb : b ∈ codedSelectedFunctionNodes (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c))
    (hweak : InternallyWeakSpecialization
      (codedSelectedFunctionNodes (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c))
      (codedSelectedFunctionOrder (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c)) g)
    (hcof : ∀ i ∈ j κ, ∃ x ∈ codedFunctionCandidate (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c) g b,
      ⟨(j c) ‘ i, (codedFunctionDomains (R.endExtension j).code (j (R.equiv s).val)) ‘ x⟩ₖ ∈
        codedFiniteDomainOrder (R.endExtension j).code (j (R.equiv s).val)) :
    ∃ A : V, IsCodedDefinableSet R.code A ∧
      j A = codedFunctionCandidate (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c) g b := by
  let : IsOrdinal (j κ) := (j.ordinal_iff κ).mpr inferInstance
  let B := codedFunctionCandidate (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c) g b ∩
    codedSelectedFunctionNodes (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c)
  have hc' := R.endExtension_finiteDomainChain j (R.equiv s).val (R.equiv s).property hc
  have hB := (R.endExtension j).codedFunctionCandidate_selected_branch s hc' hb hweak hcof
  have hBj : IsInternalCofinalBranch (j (codedSelectedFunctionNodes R.code (R.equiv s).val κ c))
      (j (codedSelectedFunctionOrder R.code (R.equiv s).val κ c)) (j κ)
      (j (codedSelectedFunctionRank R.code (R.equiv s).val κ c)) B := by
    simpa only [B, R.endExtension_equiv_val,
      R.endExtension_codedSelectedFunctionNodes j (R.equiv s).val (R.equiv s).property,
      R.endExtension_codedSelectedFunctionOrder j (R.equiv s).val (R.equiv s).property,
      R.endExtension_codedSelectedFunctionRank j (R.equiv s).val (R.equiv s).property] using hB
  obtain ⟨C, hC, he⟩ := hpres B hBj
  refine ⟨codedFunctionBranchFilter R.code (R.equiv s).val C,
    R.codedFunctionBranchFilter_isCodedDefinable s hc hC hRubin, ?_⟩
  rw [R.endExtension_codedFunctionBranchFilter j (R.equiv s).val (R.equiv s).property, he]
  exact ((R.endExtension j).codedFunctionCandidate_eq_filter s).symm

theorem codedFunctionCandidate_predicate (hω : HasStandardOmega V) {g b : U}
    (hb : b ∈ codedSelectedFunctionNodes (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c))
    (hweak : InternallyWeakSpecialization
      (codedSelectedFunctionNodes (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c))
      (codedSelectedFunctionOrder (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c)) g)
    (hcof : ∀ i ∈ j κ, ∃ x ∈ codedFunctionCandidate (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c) g b,
      ⟨(j c) ‘ i, (codedFunctionDomains (R.endExtension j).code (j (R.equiv s).val)) ‘ x⟩ₖ ∈
        codedFiniteDomainOrder (R.endExtension j).code (j (R.equiv s).val)) :
    ℒₛₑₜ-predicate[W] (fun x ↦ ((R.endExtension j).equiv x).val ∈
      codedFunctionCandidate (R.endExtension j).code (j (R.equiv s).val) (j κ) (j c) g b) := by
  obtain ⟨A, hA, he⟩ := R.codedFunctionCandidate_eq_ground_definition j s hc hRubin hpres hb hweak hcof
  apply Language.DefinablePred.of_iff (R.predicate_of_isCodedDefinableSet hω hA)
  intro x
  rw [← he, R.endExtension_equiv_val, j.mem_iff]

end ZFVP.BinaryRelationRepresentation
