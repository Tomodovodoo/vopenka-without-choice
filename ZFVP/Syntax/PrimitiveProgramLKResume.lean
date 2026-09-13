import ZFVP.Syntax.PrimitiveProgramLKMonotonicity

/-! Resuming the explicit LK certificate fold from an existing checked state. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def lkCertificateResume : PrimitiveProgram := listFold identity lkCertificateStep

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_lkCertificateResume_zero (st : M) :
    lkCertificateResume.evalArithmetic (Arithmetic.pair st 0) = st := by
  simp [lkCertificateResume]

theorem evalArithmetic_lkCertificateResume_cons (st C w p : M) :
    lkCertificateResume.evalArithmetic (Arithmetic.pair st (Arithmetic.pair (Arithmetic.pair C w) p + 1)) =
      Arithmetic.pair (Arithmetic.pair C (Arithmetic.pi₁ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p))) + 1)
        (if Arithmetic.pi₂ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p)) = 1 ∧
          lkRuleCheck.evalArithmetic (Arithmetic.pair
            (Arithmetic.pi₁ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p)))
            (Arithmetic.pair C w)) = 1 then 1 else 0) := by
  rw [lkCertificateResume, evalArithmetic_listFold_cons]
  change lkCertificateStep.evalArithmetic (Arithmetic.pair st (Arithmetic.pair (Arithmetic.pair C w)
    (lkCertificateResume.evalArithmetic (Arithmetic.pair st p)))) = _
  conv_lhs => rw [← Arithmetic.pair_unpair (lkCertificateResume.evalArithmetic (Arithmetic.pair st p))]
  exact evalArithmetic_lkCertificateStep _ _ _ _ _

theorem evalArithmetic_lkCertificateResume_cons_left (st C w p : M) :
    Arithmetic.pi₁ (lkCertificateResume.evalArithmetic
      (Arithmetic.pair st (Arithmetic.pair (Arithmetic.pair C w) p + 1))) =
      Arithmetic.pair C (Arithmetic.pi₁ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p))) + 1 := by
  rw [evalArithmetic_lkCertificateResume_cons]
  simp

theorem evalArithmetic_lkCertificateResume_cons_right (st C w p : M) :
    Arithmetic.pi₂ (lkCertificateResume.evalArithmetic
      (Arithmetic.pair st (Arithmetic.pair (Arithmetic.pair C w) p + 1))) = 1 ↔
      Arithmetic.pi₂ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p)) = 1 ∧
        lkRuleCheck.evalArithmetic (Arithmetic.pair
          (Arithmetic.pi₁ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p))) (Arithmetic.pair C w)) = 1 := by
  rw [evalArithmetic_lkCertificateResume_cons]
  simp

theorem evalArithmetic_lkCertificateResume_initial (z p : M) :
    lkCertificateResume.evalArithmetic (Arithmetic.pair (Arithmetic.pair 0 1) p) =
      lkCertificateRun.evalArithmetic (Arithmetic.pair z p) := by
  induction p using ISigma1.sigma1_order_induction
  · definability
  case ind p ih =>
    rcases listCode_cases p with rfl | ⟨row, tail, rfl⟩
    · simp
    · obtain ⟨C, w, rfl⟩ := arithmeticPair_cases row
      rw [evalArithmetic_lkCertificateResume_cons, evalArithmetic_lkCertificateRun_cons,
        ih tail (lt_succ_iff_le.mpr (le_pair_right (Arithmetic.pair C w) tail))]

theorem evalArithmetic_lkCertificateResume_left (st p : M) :
    Arithmetic.pi₁ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p)) =
      listAppend.evalArithmetic (Arithmetic.pair (Arithmetic.pi₁ st)
        (Arithmetic.pi₁ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)))) := by
  induction p using ISigma1.sigma1_order_induction
  · definability
  case ind p ih =>
    rcases listCode_cases p with rfl | ⟨row, tail, rfl⟩
    · simp
    · obtain ⟨C, w, rfl⟩ := arithmeticPair_cases row
      rw [evalArithmetic_lkCertificateResume_cons_left, evalArithmetic_lkCertificateRun_cons_left,
        evalArithmetic_listAppend_cons, ih tail (lt_succ_iff_le.mpr (le_pair_right (Arithmetic.pair C w) tail))]

theorem evalArithmetic_lkCertificateResume_append (st p q : M) :
    lkCertificateResume.evalArithmetic (Arithmetic.pair st (listAppend.evalArithmetic (Arithmetic.pair q p))) =
      lkCertificateResume.evalArithmetic (Arithmetic.pair
        (lkCertificateResume.evalArithmetic (Arithmetic.pair st q)) p) := by
  induction p using ISigma1.sigma1_order_induction
  · definability
  case ind p ih =>
    rcases listCode_cases p with rfl | ⟨row, tail, rfl⟩
    · simp
    · obtain ⟨C, w, rfl⟩ := arithmeticPair_cases row
      rw [evalArithmetic_listAppend_cons, evalArithmetic_lkCertificateResume_cons,
        evalArithmetic_lkCertificateResume_cons, ih tail (lt_succ_iff_le.mpr (le_pair_right (Arithmetic.pair C w) tail))]

theorem lkCertificateResume_valid (st p : M) (hst : arithmeticLKSequentsValid (Arithmetic.pi₁ st))
    (hcheck : Arithmetic.pi₂ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p)) = 1) :
    arithmeticLKSequentsValid (Arithmetic.pi₁ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p))) := by
  induction p using ISigma1.sigma1_order_induction
  · unfold arithmeticLKSequentsValid
    definability
  case ind p ih =>
    rcases listCode_cases p with rfl | ⟨row, tail, rfl⟩
    · simpa using hst
    · obtain ⟨C, w, rfl⟩ := arithmeticPair_cases row
      obtain ⟨hprev, hrule⟩ := (evalArithmetic_lkCertificateResume_cons_right st C w tail).mp hcheck
      rw [evalArithmetic_lkCertificateResume_cons_left, arithmeticLKSequentsValid_cons]
      exact ⟨lkRuleCheck_conclusion hrule,
        ih tail (lt_succ_iff_le.mpr (le_pair_right (Arithmetic.pair C w) tail)) hprev⟩

theorem lkCertificateResume_accept (st p : M) (hst : arithmeticLKSequentsValid (Arithmetic.pi₁ st))
    (hok : Arithmetic.pi₂ st = 1)
    (hcheck : Arithmetic.pi₂ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)) = 1) :
    Arithmetic.pi₂ (lkCertificateResume.evalArithmetic (Arithmetic.pair st p)) = 1 := by
  induction p using ISigma1.sigma1_order_induction
  · definability
  case ind p ih =>
    rcases listCode_cases p with rfl | ⟨row, tail, rfl⟩
    · simpa using hok
    · obtain ⟨C, w, rfl⟩ := arithmeticPair_cases row
      obtain ⟨hprev, hrule⟩ := (evalArithmetic_lkCertificateRun_cons_right_eq_one 0 C w tail).mp hcheck
      have hresume := ih tail (lt_succ_iff_le.mpr (le_pair_right (Arithmetic.pair C w) tail)) hprev
      apply (evalArithmetic_lkCertificateResume_cons_right st C w tail).mpr
      refine ⟨hresume, lkRuleCheck_mono ?_ (lkCertificateResume_valid st tail hst hresume) hrule⟩
      intro x hx
      rw [evalArithmetic_lkCertificateResume_left, evalArithmetic_listMember_append_iff]
      exact Or.inl hx

end PrimitiveProgram
end ZFVP
