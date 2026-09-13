import ZFVP.ModelTheory.SchmerlCodedClassCandidates
import ZFVP.ModelTheory.SchmerlCodedTreeTransport
import ZFVP.SetTheory.EndExtensionHierarchyAgreement

/-! A cofinal candidate in the specializing extension has a full original
definition: preserve its selected branch, reconstruct the ground full filter,
then apply the actual Rubin clause and decode its original-language formula. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V U : Type*} [SetStructure V] [SetStructure U]
  [Nonempty V] [Nonempty U] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [U↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) (j : MembershipEndExtension V U)
variable {κ c : V} [IsOrdinal κ]
variable (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
variable (hRubin : IsCodedRubin R.code κ)
variable (hpres : ∀ B : U,
  IsInternalCofinalBranch (j (codedSelectedClassNodes R.code κ c)) (j (codedSelectedClassOrder R.code κ c))
    (j κ) (j (codedSelectedClassRank R.code κ c)) B →
  ∃ C : V, IsInternalCofinalBranch (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c)
    κ (codedSelectedClassRank R.code κ c) C ∧ j C = B)

include hc hRubin hpres

theorem codedClassCandidate_eq_ground_definition {g b : U}
    (hb : b ∈ codedSelectedClassNodes (R.endExtension j).code (j κ) (j c))
    (hweak : InternallyWeakSpecialization (codedSelectedClassNodes (R.endExtension j).code (j κ) (j c))
      (codedSelectedClassOrder (R.endExtension j).code (j κ) (j c)) g)
    (hcof : ∀ i ∈ j κ, ∃ x ∈ codedClassCandidate (R.endExtension j).code (j κ) (j c) g b,
      ⟨(j c) ‘ i, (codedClassLevels (R.endExtension j).code) ‘ x⟩ₖ ∈ codedOrdinalOrder (R.endExtension j).code) :
    ∃ A : V, IsCodedDefinableSet R.code A ∧ j A = codedClassCandidate (R.endExtension j).code (j κ) (j c) g b := by
  let : IsOrdinal (j κ) := (j.ordinal_iff κ).mpr inferInstance
  let B := codedClassCandidate (R.endExtension j).code (j κ) (j c) g b ∩
    codedSelectedClassNodes (R.endExtension j).code (j κ) (j c)
  have hB := (R.endExtension j).codedClassCandidate_selected_branch (R.endExtension_cofinalChain j hc) hb hweak hcof
  have hBj : IsInternalCofinalBranch (j (codedSelectedClassNodes R.code κ c)) (j (codedSelectedClassOrder R.code κ c))
      (j κ) (j (codedSelectedClassRank R.code κ c)) B := by
    simpa only [R.endExtension_codedSelectedClassNodes j, R.endExtension_codedSelectedClassOrder j,
      R.endExtension_codedSelectedClassRank j] using hB
  obtain ⟨C, hC, he⟩ := hpres B hBj
  refine ⟨codedBranchFilter R.code C, R.codedBranchFilter_isCodedDefinable hc hC hRubin, ?_⟩
  rw [R.endExtension_codedBranchFilter j, he]
  exact (R.endExtension j).codedClassCandidate_eq_filter.symm

theorem codedClassCandidate_predicate (hω : HasStandardOmega V) {g b : U}
    (hb : b ∈ codedSelectedClassNodes (R.endExtension j).code (j κ) (j c))
    (hweak : InternallyWeakSpecialization (codedSelectedClassNodes (R.endExtension j).code (j κ) (j c))
      (codedSelectedClassOrder (R.endExtension j).code (j κ) (j c)) g)
    (hcof : ∀ i ∈ j κ, ∃ x ∈ codedClassCandidate (R.endExtension j).code (j κ) (j c) g b,
      ⟨(j c) ‘ i, (codedClassLevels (R.endExtension j).code) ‘ x⟩ₖ ∈ codedOrdinalOrder (R.endExtension j).code) :
    ℒₛₑₜ-predicate[W] (fun x ↦ ((R.endExtension j).equiv x).val ∈
      codedClassCandidate (R.endExtension j).code (j κ) (j c) g b) := by
  obtain ⟨A, hA, he⟩ := R.codedClassCandidate_eq_ground_definition j hc hRubin hpres hb hweak hcof
  apply Language.DefinablePred.of_iff (R.predicate_of_isCodedDefinableSet hω hA)
  intro x
  rw [← he, R.endExtension_equiv_val, j.mem_iff]

end ZFVP.BinaryRelationRepresentation
