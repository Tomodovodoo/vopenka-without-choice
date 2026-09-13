import ZFVP.ModelTheory.RelativeSigmaCorrectness

/-! Preservation of one fixed partial-truth predicate gives correctness for
all internally coded formulas at its level. The code and assignment residency
needed for the converse is derived from the transitive ZF model. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)]
  [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedSigmaCorrect_iff_domainTruth (k : ℕ) :
    CodedSigmaCorrect k U ↔
      ∀ n φ b : SetDomain U, IsLevyFormulaCode .sigma (k + 1) n φ →
        (IsFunction b ∧ domain b = n) →
        (DomainTruth .sigma k n φ b ↔ DomainTruth .sigma k n.val φ.val b.val) := by
  constructor
  · intro h n φ b hφ hb
    have hφV := (levyCode_iff U .sigma (k + 1) n φ).mp hφ
    let := sequenceSupport U
    have hbU := (function_on_support_iff b.property n.val).mpr
      ((function_on_iff U b n).mp hb)
    exact (domainTruth_iff U n φ b hφ hb).trans (h n.val φ.val hφV b.val hbU).symm
  · intro h n φ hφ b hb
    let := sequenceSupport U
    let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hφ.context⟩
    let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
      (levyFormulaFamily_subset_support (k + 1) .sigma U _ hφ)).2⟩
    let b' : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hφ.context hb⟩
    have hφ' := (levyCode_iff U .sigma (k + 1) n' φ').mpr hφ
    have hb' := (function_on_iff U b' n').mpr
      ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
    exact (h n' φ' b' hφ' hb').symm.trans (domainTruth_iff U n' φ' b' hφ' hb')

theorem codedSigmaCorrect_of_domainTruthFormula (k : ℕ)
    (h : ∀ v : Fin 3 → SetDomain U,
      (domainTruthFormula .sigma k).Evalb v ↔
        (domainTruthFormula .sigma k).Evalb (fun i ↦ (v i).val)) :
    CodedSigmaCorrect k U := by
  apply (codedSigmaCorrect_iff_domainTruth U k).mpr
  intro n φ b _ _
  have he := h ![n, φ, b]
  have hv : (fun i : Fin 3 ↦ (![n, φ, b] i).val) = ![n.val, φ.val, b.val] := by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i
  rw [hv, eval_domainTruthFormula, eval_domainTruthFormula] at he
  exact he

end TransitiveZF

theorem relativeSigmaCorrect_of_domainTruthFormula (U W : V)
    [IsTransitive U] [IsTransitive W]
    [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hUW : U ⊆ W) (k : ℕ)
    (h : ∀ v : Fin 3 → SetDomain U,
      (domainTruthFormula .sigma k).Evalb v ↔
        (domainTruthFormula .sigma k).Evalb (M := SetDomain W)
          (fun i ↦ (⟨(v i).val, hUW _ (v i).property⟩ : SetDomain W))) :
    RelativeSigmaCorrect (k + 1) U W := by
  intro n φ hφ b hb
  let := TransitiveZF.sequenceSupport U
  let nU : SetDomain U := ⟨n, IsCodingSupport.natural_mem hφ.context⟩
  let φU : SetDomain U := ⟨φ, (kpair_components_mem_transitive
    (levyFormulaFamily_subset_support (k + 1) .sigma U _ hφ)).2⟩
  let bU : SetDomain U := ⟨b, function_mem_sequenceSupport (subset_refl U) hφ.context hb⟩
  let j : SetDomain U → SetDomain W := fun x ↦ ⟨x.val, hUW _ x.property⟩
  have hφU := (TransitiveZF.levyCode_iff U .sigma (k + 1) nU φU).mpr hφ
  have hbU := (TransitiveZF.function_on_iff U bU nU).mpr
    ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
  have hφW := (TransitiveZF.levyCode_iff W .sigma (k + 1) (j nU) (j φU)).mpr hφ
  have hbW := (TransitiveZF.function_on_iff W (j bU) (j nU)).mpr
    ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
  have he := h ![nU, φU, bU]
  have hjv : (fun i : Fin 3 ↦
      (⟨(![nU, φU, bU] i).val, hUW _ (![nU, φU, bU] i).property⟩ : SetDomain W)) =
      ![j nU, j φU, j bU] := by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i
  rw [hjv] at he
  rw [eval_domainTruthFormula, eval_domainTruthFormula] at he
  exact (TransitiveZF.domainTruth_iff U nU φU bU hφU hbU).symm.trans
    (he.trans (TransitiveZF.domainTruth_iff W (j nU) (j φU) (j bU) hφW hbW))

theorem cn_of_domainTruthFormula {α : V} [IsOrdinal α]
    [Nonempty (SetDomain (hierarchy α))] [(SetDomain (hierarchy α))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (k : ℕ) (h : ∀ v : Fin 3 → SetDomain (hierarchy α),
      (domainTruthFormula .sigma k).Evalb v ↔
        (domainTruthFormula .sigma k).Evalb (fun i ↦ (v i).val)) : Cn (k + 1) α := by
  let := hierarchy_transitive α
  exact ⟨inferInstance, TransitiveZF.codedSigmaCorrect_of_domainTruthFormula (hierarchy α) k h⟩

end ZFVP
