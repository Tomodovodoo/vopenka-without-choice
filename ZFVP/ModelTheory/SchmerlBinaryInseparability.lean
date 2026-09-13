import ZFVP.ModelTheory.InternalNamedSeparationOmission
import ZFVP.ModelTheory.SchmerlInfinitaryDefinitions
import ZFVP.ModelTheory.RubinStage

/-! External definable predicates have actual internal codes. Consequently,
coded inseparability implies inseparability of the represented binary model. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedInseparable.domain_nonempty {M U W : V} (h : IsCodedInseparable M U W) :
    IsNonempty (structureDomain M) := by
  by_contra hne
  have hempty : ∀ x, x ∉ structureDomain M := fun x hx ↦ hne ⟨x, hx⟩
  apply h.2.2
  refine ⟨∅, ?_, ?_, fun _ _ hh ↦ not_mem_empty hh⟩
  · refine ⟨fun _ hh ↦ False.elim (not_mem_empty hh), ∅, empty_mem_ω, truthCode,
      (formulaSet_constants membershipLanguageCode_valid (ω_succ_closed empty_mem_ω) ∅).1,
      ∅, by simp [mem_function_iff], fun x hx ↦ False.elim (hempty x hx)⟩
  · intro x hx
    exact False.elim (hempty x (h.1 x hx))

theorem exists_codedDefinition_of_binary_predicate {D R : V} (hD : IsNonempty D)
    (P : BinaryRelationDomain D R → Prop) (hP : ℒₛₑₜ-predicate[BinaryRelationDomain D R] P) :
    ∃ A, IsCodedDefinableSet (binaryRelationStructureCode D R) A ∧
      ∀ x : BinaryRelationDomain D R, x.val ∈ A ↔ P x := by
  let : Nonempty (BinaryRelationDomain D R) := binaryRelationDomain_nonempty hD
  obtain ⟨k, ψ, a, hψ⟩ := (finite_parameter_definition_iff P).mp hP
  let b : V := standardTuple (fun z ↦ (a z).val)
  let d : V := ⟨⟨(k : V), encodeMembershipFormula ψ⟩ₖ, b⟩ₖ
  have hφ : encodeMembershipFormula ψ ∈ formulaSet membershipLanguageCode ∅ (succ (k : V)) := by
    simpa only [num_succ_def] using encodeMembershipFormula_mem (V := V) ψ
  have hb : b ∈ structureDomain (binaryRelationStructureCode D R) ^ (k : V) := by
    simpa only [binaryRelationStructureCode_domain] using
      standardTuple_mem_function (fun z ↦ (a z).val) (fun z ↦ (a z).property)
  have hd : d ∈ unaryDefinitionParameters (binaryRelationStructureCode D R) :=
    pair_mem_unaryDefinitionParameters.mpr ⟨by simp, hφ, hb⟩
  refine ⟨unaryDefinitionSet (binaryRelationStructureCode D R) d,
    unaryDefinitionSet_isCodedDefinable hd, fun x ↦ ?_⟩
  rw [mem_unaryDefinitionSet, binaryRelationStructureCode_domain, and_iff_right x.property]
  simp only [d, definitionParameterCount_pair, definitionFormula_pair, definitionTuple_pair]
  have htuple : standardTuple (fun z ↦ ((x :> a) z).val) = assignmentPrepend (k : V) b x.val := by
    simp only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ, b]
  have hs : codedSatisfies (binaryRelationStructureCode D R) (succ (k : V))
      (encodeMembershipFormula ψ) (assignmentPrepend (k : V) b x.val) ↔ ψ.Evalb (x :> a) := by
    simpa only [codedSatisfies, num_succ_def, htuple] using satisfies_encodeBinaryRelationFormula hD ψ (x :> a)
  exact hs.trans (hψ x)

theorem IsCodedInseparable.binary_inseparable {D R U W : V}
    (h : IsCodedInseparable (binaryRelationStructureCode D R) U W) :
    Inseparable (BinaryRelationDomain D R) (fun x ↦ x.val ∈ U) (fun x ↦ x.val ∈ W) := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using h.domain_nonempty
  rintro ⟨P, hP, hUP, hWP⟩
  obtain ⟨A, hA, heq⟩ := exists_codedDefinition_of_binary_predicate hD P hP
  apply h.2.2
  refine ⟨A, hA, ?_, ?_⟩
  · intro x hx
    let x' : BinaryRelationDomain D R := ⟨x, by simpa only [binaryRelationStructureCode_domain] using h.1 x hx⟩
    exact (heq x').mpr (hUP x' hx)
  · intro x hx hxA
    let x' : BinaryRelationDomain D R := ⟨x, by simpa only [binaryRelationStructureCode_domain] using h.2.1 x hx⟩
    exact hWP x' hx ((heq x').mp hxA)

end ZFVP.Schmerl
