import ZFVP.ModelTheory.BinaryRelationZFModel
import ZFVP.ModelTheory.GeneratedZFVPTheoryEquivalence

/-! The converse from external ZF truth requires control of the entire internal
syntax. These hypotheses are external and are not inferred from ZF alone. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every internal context length and every membership formula in a standard
context has an external finite representative. No definability is claimed. -/
structure StandardMembershipSyntax : Prop where
  naturals : ∀ n ∈ (ω : V), ∃ k : ℕ, n = (k : V)
  formulas : ∀ (k : ℕ) (φ : V), IsMembershipFormulaCode (k : V) φ →
    ∃ ψ : SetTheorySemisentence k, encodeMembershipFormula ψ = φ

variable {V}

namespace BinaryRelationRepresentation

variable {M : Type*} [SetStructure M] (R : BinaryRelationRepresentation (V := V) M)

theorem exists_standard_assignment {k : ℕ} {b : V}
    (hb : b ∈ structureDomain R.code ^ (k : V)) :
    ∃ v : Fin k → M, standardTuple (fun i ↦ (R.equiv (v i)).val) = b := by
  have hb' : b ∈ R.carrier ^ (k : V) := by
    simpa only [code, binaryRelationStructureCode_domain] using hb
  let v : Fin k → M := fun i ↦ R.equiv.symm ⟨b ‘ (i.val : V),
    function_value_mem hb' (natCast_mem_of_lt i.isLt)⟩
  have hv (i : Fin k) : (R.equiv (v i)).val = b ‘ (i.val : V) :=
    congrArg Subtype.val (R.equiv.apply_symm_apply _)
  refine ⟨v, function_eq_of_values
    (standardTuple_mem_function _ (fun i ↦ (R.equiv (v i)).property)) hb' ?_⟩
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_natCast_iff _ _).mp hx
  simpa only [value_standardTuple] using hv i

variable [Nonempty M]

theorem isCodedZFModel_of_standardSyntax (hstd : StandardMembershipSyntax V)
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : IsCodedZFModel R.code := by
  refine ⟨R.code_valid, fun n φ hφ ↦ ?_⟩
  have hax := (mem_zfOpenAxiomCodes_iff n φ).mp hφ
  refine ⟨hax.valid.valid, fun b hb ↦ ?_⟩
  rcases hax with ⟨rfl, hfixed⟩ | ⟨hn, ψ, hψ, rfl⟩ | ⟨hn, ψ, hψ, rfl⟩
  · have hbzero : b = ∅ := by simpa [mem_function_iff, zero_def] using hb
    subst b
    rcases (mem_fixedZFSentenceCodes_iff φ).mp hfixed with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (R.satisfies_sentence_iff _).mpr (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_empty_set)
    · exact (R.satisfies_sentence_iff _).mpr (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_extentionality)
    · exact (R.satisfies_sentence_iff _).mpr (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_pairing)
    · exact (R.satisfies_sentence_iff _).mpr (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_union)
    · exact (R.satisfies_sentence_iff _).mpr (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_power_set)
    · exact (R.satisfies_sentence_iff _).mpr (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_infinity)
    · exact (R.satisfies_sentence_iff _).mpr (Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_foundation)
    · apply (R.satisfies_sentence_iff _).mpr
      exact eval_equalityBasisSentence
  · obtain ⟨k, rfl⟩ := hstd.naturals n hn
    obtain ⟨χ, rfl⟩ := hstd.formulas (k + 1) ψ (by
      simpa only [IsMembershipFormulaCode, num_succ_def] using hψ)
    obtain ⟨v, rfl⟩ := R.exists_standard_assignment hb
    rw [separationCode, MembershipTemplate.compileTail_encode]
    apply (R.satisfies_iff _ v).mpr
    have h : ∀ v : Fin k → M, (separationTemplate.instantiateTail k χ).Evalb v := by
      simpa [models_iff, Semiformula.Evalb] using zf_models_generated_separation (M := M) k χ
    exact h v
  · obtain ⟨k, rfl⟩ := hstd.naturals n hn
    obtain ⟨χ, rfl⟩ := hstd.formulas (k + 2) ψ (by
      simpa only [IsMembershipFormulaCode, num_succ_def] using hψ)
    obtain ⟨v, rfl⟩ := R.exists_standard_assignment hb
    rw [replacementCode, MembershipTemplate.compileTail_encode]
    apply (R.satisfies_iff _ v).mpr
    have h : ∀ v : Fin k → M, (replacementTemplate.instantiateTail k χ).Evalb v := by
      simpa [models_iff, Semiformula.Evalb] using zf_models_generated_replacement (M := M) k χ
    exact h v

theorem isCodedZFModel_iff_of_standardSyntax (hstd : StandardMembershipSyntax V) :
    IsCodedZFModel R.code ↔ M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  constructor
  · exact R.models_zf_of_isCodedZFModel
  · intro h
    let := h
    exact R.isCodedZFModel_of_standardSyntax hstd

end BinaryRelationRepresentation

end ZFVP
