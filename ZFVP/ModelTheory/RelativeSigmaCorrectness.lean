import ZFVP.ModelTheory.LocalPartialTruthCorrectness

/-! Relative Sigma elementarity and the C(n) classes computed inside transitive ZF models. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def relativeSigmaCorrectFormula (k : ℕ) : SetTheorySemisentence 2 :=
  “A B. ∀ n φ b, !(sigmaOneLevyCodeFormula .sigma k) n φ → !boundedFunctionFormula b n A →
    ((!(sigmaOneMembershipModelTruthFormula true) A n φ b → !piOneMembershipTruthFormula B n φ b) ∧
      (!(sigmaOneMembershipModelTruthFormula true) B n φ b → !piOneMembershipTruthFormula A n φ b))”

theorem relativeSigmaCorrectFormula_piOne (k : ℕ) : IsPiFormula 1 (relativeSigmaCorrectFormula k) :=
  .all (.all (.all (.or ((sigmaOneLevyCodeFormula_sigmaOne .sigma k).subst _).neg
    (.or (.bounded (boundedFunctionFormula_bounded.subst _).neg) (.and
      (.or ((sigmaOneMembershipModelTruthFormula_sigmaOne true).subst _).neg (piOneMembershipTruthFormula_piOne.subst _))
      (.or ((sigmaOneMembershipModelTruthFormula_sigmaOne true).subst _).neg (piOneMembershipTruthFormula_piOne.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def RelativeSigmaCorrect (k : ℕ) (A B : V) : Prop :=
  ∀ n φ, IsLevyFormulaCode .sigma k n φ → ∀ b ∈ A ^ n,
    MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ b

instance relativeSigmaCorrectFormula_defined (k : ℕ) :
    ℒₛₑₜ-relation[V] (RelativeSigmaCorrect k) via relativeSigmaCorrectFormula k := by
  refine ⟨fun v ↦ ?_⟩
  simp [relativeSigmaCorrectFormula, RelativeSigmaCorrect, iff_def]
  aesop

instance relativeSigmaCorrect_definable (k : ℕ) : ℒₛₑₜ-relation[V] (RelativeSigmaCorrect k) :=
  (relativeSigmaCorrectFormula_defined k).to_definable

theorem IsElementaryInclusion.relativeSigmaCorrect {A B : V} (h : IsElementaryInclusion A B) (k : ℕ) :
    RelativeSigmaCorrect k A B := by
  intro n φ hφ b hb
  exact h.satisfaction_iff hφ.context ((mem_formulaSet_iff _ _ _ _).mp hφ.valid) hb

theorem relativeSigmaCorrect_elementary_target {k : ℕ} {A B C : V}
    (hAB : A ⊆ B) (hBC : IsElementaryInclusion B C) :
    RelativeSigmaCorrect k A B ↔ RelativeSigmaCorrect k A C := by
  constructor
  · intro h n φ hφ b hb
    exact (h n φ hφ b hb).trans (hBC.satisfaction_iff hφ.context
      ((mem_formulaSet_iff _ _ _ _).mp hφ.valid) (mem_function_of_mem_function_of_subset hb hAB))
  · intro h n φ hφ b hb
    exact (h n φ hφ b hb).trans (hBC.satisfaction_iff hφ.context
      ((mem_formulaSet_iff _ _ _ _).mp hφ.valid) (mem_function_of_mem_function_of_subset hb hAB)).symm

theorem rankEmbedding_relativeSigmaCorrect_iff {k l : ℕ} {δ ε f A B : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (m : ℕ) (hA : A ∈ hierarchy δ) (hB : B ∈ hierarchy δ) :
    RelativeSigmaCorrect m A B ↔ RelativeSigmaCorrect m (f ‘ A) (f ‘ B) := by
  let a : SetDomain (hierarchy δ) := ⟨A, hA⟩
  let b : SetDomain (hierarchy δ) := ⟨B, hB⟩
  have hs := hδ.defined_correct ((relativeSigmaCorrectFormula_piOne m).mono (by omega))
    (fun v ↦ RelativeSigmaCorrect m (v 0) (v 1)) ![a, b]
  have ht := hε.defined_correct ((relativeSigmaCorrectFormula_piOne m).mono (by omega))
    (fun v ↦ RelativeSigmaCorrect m (v 0) (v 1)) (h.toFunction ∘ ![a, b])
  exact hs.symm.trans ((h.eval_semisentence (relativeSigmaCorrectFormula m) ![a, b]).trans ht)

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem relativeSigmaCorrect_iff (k : ℕ) (A B : SetDomain U) :
    RelativeSigmaCorrect k A B ↔ RelativeSigmaCorrect k A.val B.val := by
  let := sequenceSupport U
  have hAU : A.val ⊆ U := (inferInstance : IsTransitive U).transitive A.val A.property
  constructor
  · intro hc n φ hφ b hb
    let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hφ.context⟩
    let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
      (levyFormulaFamily_subset_support k .sigma U _ hφ)).2⟩
    let b' : SetDomain U := ⟨b, function_mem_sequenceSupport hAU hφ.context hb⟩
    have he := hc n' φ' ((levyCode_iff U .sigma k n' φ').mpr hφ) b' ((function_iff U b' n' A).mpr hb)
    exact (satisfies_iff U A n' φ' b').symm.trans (he.trans (satisfies_iff U B n' φ' b'))
  · intro hc n φ hφ b hb
    have he := hc n.val φ.val ((levyCode_iff U .sigma k n φ).mp hφ) b.val ((function_iff U b n A).mp hb)
    exact (satisfies_iff U A n φ b).trans (he.trans (satisfies_iff U B n φ b).symm)

theorem codedSigmaCorrect_iff (k : ℕ) (A : SetDomain U) :
    CodedSigmaCorrect k A ↔ RelativeSigmaCorrect (k + 1) A.val U := by
  let := sequenceSupport U
  have hAU : A.val ⊆ U := (inferInstance : IsTransitive U).transitive A.val A.property
  constructor
  · intro hc n φ hφ b hb
    let n' : SetDomain U := ⟨n, IsCodingSupport.natural_mem hφ.context⟩
    let φ' : SetDomain U := ⟨φ, (kpair_components_mem_transitive
      (levyFormulaFamily_subset_support (k + 1) .sigma U _ hφ)).2⟩
    let b' : SetDomain U := ⟨b, function_mem_sequenceSupport hAU hφ.context hb⟩
    have hφ' := (levyCode_iff U .sigma (k + 1) n' φ').mpr hφ
    have hb' := (function_iff U b' n' A).mpr hb
    have he := hc n' φ' hφ' b' hb'
    have hd := domainTruth_iff U n' φ' b' hφ' ⟨IsFunction.of_mem hb', domain_eq_of_mem_function hb'⟩
    exact (satisfies_iff U A n' φ' b').symm.trans (he.symm.trans hd)
  · intro hc n φ hφ b hb
    have hφV := (levyCode_iff U .sigma (k + 1) n φ).mp hφ
    have hbV := (function_iff U b n A).mp hb
    have hd := domainTruth_iff U n φ b hφ ⟨IsFunction.of_mem hb, domain_eq_of_mem_function hb⟩
    exact hd.trans ((hc n.val φ.val hφV b.val hbV).symm.trans (satisfies_iff U A n φ b).symm)

theorem cn_iff_relative (k : ℕ) (α : SetDomain U) (hα : IsOrdinal α.val)
    (hsub : hierarchy α.val ⊆ U) :
    Cn (k + 1) α ↔ RelativeSigmaCorrect (k + 1) (hierarchy α.val) U := by
  have hα' := (ordinal_iff U α).mpr hα
  change (IsOrdinal α ∧ CodedSigmaCorrect k (hierarchy α)) ↔ _
  rw [and_iff_right hα', codedSigmaCorrect_iff U k (hierarchy α), hierarchy_val U α hα' hsub]

end TransitiveZF

theorem modelEmbedding_relativeSigmaCorrect_iff {U W f A B : V}
    [IsTransitive U] [IsTransitive W] [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (h : IsCodedMembershipEmbedding U W f) (m : ℕ) (hA : A ∈ U) (hB : B ∈ U) :
    RelativeSigmaCorrect m A B ↔ RelativeSigmaCorrect m (f ‘ A) (f ‘ B) := by
  let a : SetDomain U := ⟨A, hA⟩
  let b : SetDomain U := ⟨B, hB⟩
  have hsource : (relativeSigmaCorrectFormula m).Evalb ![a, b] ↔ RelativeSigmaCorrect m A B :=
    (Defined.eval_iff _).trans (TransitiveZF.relativeSigmaCorrect_iff U m a b)
  have htarget : (relativeSigmaCorrectFormula m).Evalb (h.toFunction ∘ ![a, b]) ↔
      RelativeSigmaCorrect m (f ‘ A) (f ‘ B) :=
    (Defined.eval_iff _).trans (TransitiveZF.relativeSigmaCorrect_iff W m (h.toFunction a) (h.toFunction b))
  exact hsource.symm.trans ((h.eval_semisentence (relativeSigmaCorrectFormula m) ![a, b]).trans htarget)

end ZFVP
