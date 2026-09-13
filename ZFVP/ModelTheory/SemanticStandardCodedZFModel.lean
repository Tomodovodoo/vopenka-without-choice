import ZFVP.Syntax.BinaryRelationSemanticStandardness
import ZFVP.ModelTheory.StandardSyntaxCodedZFModel
import ZFVP.ModelTheory.CountableStructureUniverse

/-! Reifying full internal ZF from semantic standardness. This criterion is
proved for Universe and allows the two internal encodings of equality. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem BinaryFormulaRepresents.compileTail_closed {a k : ℕ} {φ : V}
    {ψ : SetTheorySemisentence (k + a)} (hψ : BinaryFormulaRepresents φ ψ)
    (hφ : IsMembershipFormulaCode ((k + a : ℕ) : V) φ) (t : MembershipTemplate a 0) :
    BinaryFormulaRepresents (t.compileTail (k : V) φ) (t.instantiateTail k ψ) := by
  intro D E hD b
  have hb : standardTuple (fun i ↦ (b i).val) ∈ D ^ (k : V) :=
    standardTuple_mem_function _ (fun i ↦ (b i).property)
  have hc : φ ∈ formulaSet membershipLanguageCode ∅ (prefixSize a (k : V)) := by
    simpa only [prefixSize_natCast] using hφ.valid
  have hpred :
      (fun w : Fin a → BinaryRelationDomain D E ↦
        Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ (prefixSize a (k : V)) φ
          (prependTuple (k : V) (standardTuple (fun i ↦ (b i).val)) (fun i ↦ (w i).val))) =
      (fun w ↦ ψ.Evalb (prefixVector w b)) := by
    funext w
    apply propext
    have he := hψ D E hD (prefixVector w b)
    have htup : standardTuple (fun i ↦ (prefixVector w b i).val) =
        prependTuple (k : V) (standardTuple (fun i ↦ (b i).val)) (fun i ↦ (w i).val) :=
      (congrArg (fun z : Fin (k + a) → V ↦ standardTuple z)
        (prefixVector_map (fun x : BinaryRelationDomain D E ↦ x.val) w b)).trans
          (standardTuple_prefixVector _ _)
    have hh := (Iff.of_eq (congrArg (fun c ↦
      Satisfies membershipLanguageCode ∅ (binaryRelationStructureCode D E) ∅ ((k + a : ℕ) : V) φ c)
        htup)).symm.trans he
    simpa only [prefixSize_natCast] using hh
  have ht := t.compileTail_binarySatisfies hD (by simp) hc hb (![] : Fin 0 → BinaryRelationDomain D E)
  rw [hpred] at ht
  exact ht.trans (MembershipTemplate.eval_instantiateTail ψ t (![] : Fin 0 → BinaryRelationDomain D E) b).symm

namespace BinaryRelationRepresentation

variable {M : Type*} [SetStructure M] (R : BinaryRelationRepresentation (V := V) M)

theorem satisfies_represented_iff {k : ℕ} {φ : V} {ψ : SetTheorySemisentence k}
    (hψ : BinaryFormulaRepresents φ ψ) (b : Fin k → M) :
    Satisfies membershipLanguageCode ∅ R.code ∅ (k : V) φ
      (standardTuple (fun i ↦ (R.equiv (b i)).val)) ↔ ψ.Evalb b :=
  (hψ R.carrier R.relation R.carrier_nonempty (R.equiv ∘ b)).trans (R.evalb_iff ψ b).symm

variable [Nonempty M]

theorem isCodedZFModel_of_semanticStandardSyntax (hstd : SemanticStandardMembershipSyntax V)
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : IsCodedZFModel R.code := by
  refine ⟨R.code_valid, fun n φ hφ ↦ ?_⟩
  have hax := (mem_zfOpenAxiomCodes_iff n φ).mp hφ
  refine ⟨hax.valid.valid, fun b hb ↦ ?_⟩
  rcases hax with ⟨rfl, hfixed⟩ | ⟨hn, χ, hχ, rfl⟩ | ⟨hn, χ, hχ, rfl⟩
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
    · exact (R.satisfies_sentence_iff _).mpr eval_equalityBasisSentence
  · obtain ⟨k, rfl⟩ := hstd.naturals n hn
    have hc : IsMembershipFormulaCode ((k + 1 : ℕ) : V) χ := by
      simpa only [IsMembershipFormulaCode, num_succ_def] using hχ
    obtain ⟨ψ, hψ⟩ := hstd.formulas (k + 1) χ hc
    obtain ⟨v, rfl⟩ := R.exists_standard_assignment hb
    apply (R.satisfies_represented_iff (hψ.compileTail_closed hc separationTemplate) v).mpr
    have ht : ∀ v : Fin k → M, (separationTemplate.instantiateTail k ψ).Evalb v := by
      simpa [models_iff, Semiformula.Evalb] using zf_models_generated_separation (M := M) k ψ
    exact ht v
  · obtain ⟨k, rfl⟩ := hstd.naturals n hn
    have hc : IsMembershipFormulaCode ((k + 2 : ℕ) : V) χ := by
      simpa only [IsMembershipFormulaCode, num_succ_def] using hχ
    obtain ⟨ψ, hψ⟩ := hstd.formulas (k + 2) χ hc
    obtain ⟨v, rfl⟩ := R.exists_standard_assignment hb
    apply (R.satisfies_represented_iff (hψ.compileTail_closed hc replacementTemplate) v).mpr
    have ht : ∀ v : Fin k → M, (replacementTemplate.instantiateTail k ψ).Evalb v := by
      simpa [models_iff, Semiformula.Evalb] using zf_models_generated_replacement (M := M) k ψ
    exact ht v

theorem isCodedZFModel_iff_of_semanticStandardSyntax (hstd : SemanticStandardMembershipSyntax V) :
    IsCodedZFModel R.code ↔ M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  constructor
  · exact R.models_zf_of_isCodedZFModel
  · intro h
    let := h
    exact R.isCodedZFModel_of_semanticStandardSyntax hstd

end BinaryRelationRepresentation

/-- A countable external ZF model, with arbitrary and possibly ill-founded
membership, has an actual full internal ZF structure code in Universe. -/
theorem countableStructureRepresentation_isCodedZFModel (M : Type*) [SetStructure M] [Nonempty M]
    [Countable M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    IsCodedZFModel (countableStructureRepresentation M).code :=
  (countableStructureRepresentation M).isCodedZFModel_of_semanticStandardSyntax
    universe_semanticStandardMembershipSyntax

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem semanticStandardMembershipSyntax_of_wellFounded_target (j : ElementaryMap V W)
    (hW : WellFounded (fun x y : W ↦ x ∈ y)) : SemanticStandardMembershipSyntax V := by
  apply semanticStandardMembershipSyntax_of_wellFounded
  exact (InvImage.wf j hW).mono (fun _ _ h ↦ (j.map_mem_iff _ _).mpr h)

end ElementaryMap

end ZFVP
