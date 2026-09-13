import ZFVP.SetTheory.CnAbsoluteness

/-! Correctness between an inner domain and a surrounding correct rank.
Evaluation in the surrounding rank does not assume that rank is a ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem eval_correctDomainFormula_successor {W : Type*} [SetStructure W] (k : ℕ) (A : W) :
    (correctDomainFormula (k + 1)).Evalb ![A] ↔
      (correctDomainFormula k).Evalb ![A] ∧ ∀ n ∈ A, ∀ φ ∈ A, ∀ b ∈ A,
        (sigmaOneLevyCodeFormula .sigma (k + 1)).Evalb ![n, φ] →
        boundedFunctionFormula.Evalb ![b, n, A] →
        (domainSigmaTruthFormula (correctDomainFormula k)).Evalb ![n, φ, b] →
        piOneMembershipTruthFormula.Evalb ![A, n, φ, b] := by
  simp [correctDomainFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

theorem eval_domainSigmaTruthFormula_witness {W : Type*} [SetStructure W]
    (D : SetTheorySemisentence 1) (n φ b : W) :
    (domainSigmaTruthFormula D).Evalb ![n, φ, b] ↔
      ∃ A : W, D.Evalb ![A] ∧ boundedFunctionFormula.Evalb ![b, n, A] ∧
        (sigmaOneMembershipModelTruthFormula true).Evalb ![A, n, φ, b] := by
  simp [domainSigmaTruthFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem correctDomain_sandwich {k : ℕ} {δ A B : V}
    (hδ : Cn (k + 1) δ) (hA : A ∈ hierarchy δ) (hB : B ∈ hierarchy δ)
    (hAB : A ⊆ B) (hBC : CorrectDomain (k + 2) B)
    (hAC : (correctDomainFormula (k + 2)).Evalb (M := SetDomain (hierarchy δ)) ![⟨A, hA⟩]) :
    CorrectDomain (k + 2) A := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  let a : SetDomain (hierarchy δ) := ⟨A, hA⟩
  let d : SetDomain (hierarchy δ) := ⟨B, hB⟩
  obtain ⟨halower, hac⟩ := (eval_correctDomainFormula_successor (k + 1) a).mp hAC
  have haC : CorrectDomain (k + 1) A :=
    (hδ.defined_correct (correctDomainFormula_pi (k + 1)) (fun v ↦ CorrectDomain (k + 1) (v 0)) ![a]).mp halower
  refine ⟨haC, ?_⟩
  intro n hn φ hφA b hbA hφ hb ht
  let nn : SetDomain (hierarchy δ) := ⟨n, (hierarchy_transitive δ).mem_trans hn hA⟩
  let pp : SetDomain (hierarchy δ) := ⟨φ, (hierarchy_transitive δ).mem_trans hφA hA⟩
  let bb : SetDomain (hierarchy δ) := ⟨b, (hierarchy_transitive δ).mem_trans hbA hA⟩
  have hcode : (sigmaOneLevyCodeFormula .sigma (k + 2)).Evalb ![nn, pp] :=
    (hδ.defined_correct ((sigmaOneLevyCodeFormula_sigmaOne .sigma (k + 2)).mono (by omega))
      (fun v ↦ IsLevyFormulaCode .sigma (k + 2) (v 0) (v 1)) ![nn, pp]).mpr hφ
  have hfunc : boundedFunctionFormula.Evalb ![bb, nn, a] :=
    (hδ.defined_correct (p := .pi) (.bounded boundedFunctionFormula_bounded)
      (fun v ↦ v 0 ∈ v 2 ^ v 1) ![bb, nn, a]).mpr hb
  have hbB : b ∈ B ^ n := mem_function_of_mem_function_of_subset hb hAB
  have htruthB := (hBC.sigmaTruth_iff hφ hbB).mp ht
  have hDC : (correctDomainFormula (k + 1)).Evalb ![d] :=
    (hδ.defined_correct (correctDomainFormula_pi (k + 1))
      (fun v ↦ CorrectDomain (k + 1) (v 0)) ![d]).mpr hBC.lower
  have hfuncB : boundedFunctionFormula.Evalb ![bb, nn, d] :=
    (hδ.defined_correct (p := .pi) (.bounded boundedFunctionFormula_bounded)
      (fun v ↦ v 0 ∈ v 2 ^ v 1) ![bb, nn, d]).mpr hbB
  have hsB : (sigmaOneMembershipModelTruthFormula true).Evalb ![d, nn, pp, bb] :=
    (hδ.defined_correct ((sigmaOneMembershipModelTruthFormula_sigmaOne true).mono (by omega))
      (fun v ↦ MembershipSatisfies (v 0) (v 1) (v 2) (v 3)) ![d, nn, pp, bb]).mpr htruthB
  have hdt : (domainSigmaTruthFormula (correctDomainFormula (k + 1))).Evalb ![nn, pp, bb] :=
    (eval_domainSigmaTruthFormula_witness _ nn pp bb).mpr ⟨d, hDC, hfuncB, hsB⟩
  exact (hδ.setSatisfaction_absolute a nn pp bb).mp
    (hac nn hn pp hφA bb hbA hcode hfunc hdt)

theorem correctDomain_into_rank {k : ℕ} {δ A : V}
    (hδ : Cn (k + 1) δ) (hA : A ∈ hierarchy δ) (hAC : CorrectDomain (k + 2) A) :
    (correctDomainFormula (k + 2)).Evalb (M := SetDomain (hierarchy δ)) ![⟨A, hA⟩] := by
  let a : SetDomain (hierarchy δ) := ⟨A, hA⟩
  apply (eval_correctDomainFormula_successor (k + 1) a).mpr
  refine ⟨?_, ?_⟩
  · exact (hδ.defined_correct (correctDomainFormula_pi (k + 1))
      (fun v ↦ CorrectDomain (k + 1) (v 0)) ![a]).mpr hAC.lower
  · intro nn hn pp hp bb hb hcode hfunc htruth
    have hc : IsLevyFormulaCode .sigma (k + 2) nn.val pp.val :=
      (hδ.defined_correct ((sigmaOneLevyCodeFormula_sigmaOne .sigma (k + 2)).mono (by omega))
        (fun v ↦ IsLevyFormulaCode .sigma (k + 2) (v 0) (v 1)) ![nn, pp]).mp hcode
    have hf : bb.val ∈ A ^ nn.val :=
      (hδ.defined_correct (p := .pi) (.bounded boundedFunctionFormula_bounded)
        (fun v ↦ v 0 ∈ v 2 ^ v 1) ![bb, nn, a]).mp hfunc
    obtain ⟨d, hd, hbd, hsd⟩ := (eval_domainSigmaTruthFormula_witness _ nn pp bb).mp htruth
    have hDC : CorrectDomain (k + 1) d.val :=
      (hδ.defined_correct (correctDomainFormula_pi (k + 1))
        (fun v ↦ CorrectDomain (k + 1) (v 0)) ![d]).mp hd
    have hfD : bb.val ∈ d.val ^ nn.val :=
      (hδ.defined_correct (p := .pi) (.bounded boundedFunctionFormula_bounded)
        (fun v ↦ v 0 ∈ v 2 ^ v 1) ![bb, nn, d]).mp hbd
    have hsD : MembershipSatisfies d.val nn.val pp.val bb.val :=
      (hδ.defined_correct ((sigmaOneMembershipModelTruthFormula_sigmaOne true).mono (by omega))
        (fun v ↦ MembershipSatisfies (v 0) (v 1) (v 2) (v 3)) ![d, nn, pp, bb]).mp hsd
    exact (hδ.setSatisfaction_absolute a nn pp bb).mpr
      (hAC.2 nn.val hn pp.val hp bb.val hb hc hf ⟨d.val, hDC, hfD, hsD⟩)

end ZFVP
