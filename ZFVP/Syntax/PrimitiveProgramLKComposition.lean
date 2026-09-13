import ZFVP.Syntax.PrimitiveProgramLKResume
import ZFVP.Syntax.PrimitiveProgramListAllEquations

/-! Concatenating and extending internally finite accepted LK certificates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem lkCertificateRun_valid (p : M)
    (hcheck : Arithmetic.pi₂ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)) = 1) :
    arithmeticLKSequentsValid (Arithmetic.pi₁ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p))) := by
  rw [← evalArithmetic_lkCertificateResume_initial 0 p] at hcheck ⊢
  exact lkCertificateResume_valid (Arithmetic.pair 0 1) p (by simp) hcheck

theorem lkCertificateRun_append_left (p q : M) :
    Arithmetic.pi₁ (lkCertificateRun.evalArithmetic
      (Arithmetic.pair 0 (listAppend.evalArithmetic (Arithmetic.pair q p)))) =
      listAppend.evalArithmetic (Arithmetic.pair
        (Arithmetic.pi₁ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 q)))
        (Arithmetic.pi₁ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)))) := by
  rw [← evalArithmetic_lkCertificateResume_initial 0,
    evalArithmetic_lkCertificateResume_append, evalArithmetic_lkCertificateResume_initial 0,
    evalArithmetic_lkCertificateResume_left]

theorem lkCertificateRun_append_right {p q : M}
    (hp : Arithmetic.pi₂ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)) = 1)
    (hq : Arithmetic.pi₂ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 q)) = 1) :
    Arithmetic.pi₂ (lkCertificateRun.evalArithmetic
      (Arithmetic.pair 0 (listAppend.evalArithmetic (Arithmetic.pair q p)))) = 1 := by
  rw [← evalArithmetic_lkCertificateResume_initial 0,
    evalArithmetic_lkCertificateResume_append, evalArithmetic_lkCertificateResume_initial 0]
  exact lkCertificateResume_accept _ p (lkCertificateRun_valid q hq) hq hp

theorem lkProofCheck_append {C D p q : M}
    (hp : lkProofCheck.evalArithmetic (Arithmetic.pair C p) = 1)
    (hq : lkProofCheck.evalArithmetic (Arithmetic.pair D q) = 1) :
    lkProofCheck.evalArithmetic (Arithmetic.pair C (listAppend.evalArithmetic (Arithmetic.pair q p))) = 1 ∧
      lkProofCheck.evalArithmetic (Arithmetic.pair D (listAppend.evalArithmetic (Arithmetic.pair q p))) = 1 := by
  rw [evalArithmetic_lkProofCheck_eq_one] at hp hq
  have hacc := lkCertificateRun_append_right hp.1 hq.1
  constructor
  · apply (evalArithmetic_lkProofCheck_eq_one _ _).mpr
    refine ⟨hacc, ?_⟩
    rw [lkCertificateRun_append_left, evalArithmetic_listMember_append_iff]
    exact Or.inl hp.2
  · apply (evalArithmetic_lkProofCheck_eq_one _ _).mpr
    refine ⟨hacc, ?_⟩
    rw [lkCertificateRun_append_left, evalArithmetic_listMember_append_iff]
    exact Or.inr hq.2

theorem lkProofCheck_extend {C w p : M}
    (hp : Arithmetic.pi₂ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)) = 1)
    (hr : lkRuleCheck.evalArithmetic (Arithmetic.pair
      (Arithmetic.pi₁ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p))) (Arithmetic.pair C w)) = 1) :
    lkProofCheck.evalArithmetic (Arithmetic.pair C (Arithmetic.pair (Arithmetic.pair C w) p + 1)) = 1 := by
  rw [evalArithmetic_lkProofCheck_eq_one]
  constructor
  · exact (evalArithmetic_lkCertificateRun_cons_right_eq_one 0 C w p).mpr ⟨hp, hr⟩
  · rw [evalArithmetic_lkCertificateRun_cons_left, evalArithmetic_listMember_cons_iff]
    exact Or.inl rfl

def ProgramLKProvable (C : M) : Prop := ∃ p, lkProofCheck.evalArithmetic (Arithmetic.pair C p) = 1

instance programLKProvable_definable : 𝚺₁-Predicate (ProgramLKProvable : M → Prop) := by
  unfold ProgramLKProvable
  definability

theorem ProgramLKProvable.valid {C : M} (h : ProgramLKProvable C) :
    (sequentCheck true).evalArithmetic (Arithmetic.pair 0 C) = 1 := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨hacc, hmem⟩ := (evalArithmetic_lkProofCheck_eq_one C p).mp hp
  exact (arithmeticLKSequentsValid_iff _).mp (lkCertificateRun_valid p hacc) C hmem

noncomputable def arithmeticLKWitness (tag φ ψ θ k Γ Δ : M) : M :=
  Arithmetic.pair tag (Arithmetic.pair φ (Arithmetic.pair ψ (Arithmetic.pair θ
    (Arithmetic.pair k (Arithmetic.pair Γ Δ)))))

theorem formulaCheck_verum (n : M) :
    (formulaCheck true).evalArithmetic (Arithmetic.pair n (Arithmetic.pair 2 0 + 1)) = 1 := by
  simp [evalArithmetic_formulaRequirement_verum]

theorem ProgramLKProvable.weaken {C D : M} (hD : ProgramLKProvable D)
    (hC : (sequentCheck true).evalArithmetic (Arithmetic.pair 0 C) = 1)
    (hsub : listSubset.evalArithmetic (Arithmetic.pair D C) = 1) : ProgramLKProvable C := by
  have hDv := hD.valid
  obtain ⟨p, hp⟩ := hD
  obtain ⟨hacc, hmem⟩ := (evalArithmetic_lkProofCheck_eq_one D p).mp hp
  let v := Arithmetic.pair (2 : M) 0 + 1
  let w := arithmeticLKWitness 2 v v v 0 0 D
  refine ⟨Arithmetic.pair (Arithmetic.pair C w) p + 1, lkProofCheck_extend hacc ?_⟩
  change lkRuleCheck.evalArithmetic (Arithmetic.pair
    (Arithmetic.pi₁ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 p)))
    (Arithmetic.pair C (arithmeticLKWitness 2 v v v 0 0 D))) = 1
  rw [arithmeticLKWitness, evalArithmetic_lkRuleCheck_eq_one]
  refine ⟨⟨hC, lkCertificateRun_valid p hacc, formulaCheck_verum _, formulaCheck_verum _,
    formulaCheck_verum _, by simp, hDv⟩, ?_⟩
  simpa [arithmeticLKRuleCore] using And.intro hmem hsub

theorem ProgramLKProvable.cut {φ Γ Δ : M}
    (hφ : ProgramLKProvable (Arithmetic.pair φ Γ + 1))
    (hnφ : ProgramLKProvable (Arithmetic.pair (negateCode.evalArithmetic φ) Δ + 1)) :
    ProgramLKProvable (listAppend.evalArithmetic (Arithmetic.pair Δ Γ)) := by
  have hΓ := (evalArithmetic_sequentCheck_cons_iff true 0 φ Γ).mp hφ.valid
  have hΔ := (evalArithmetic_sequentCheck_cons_iff true 0 (negateCode.evalArithmetic φ) Δ).mp hnφ.valid
  obtain ⟨p, hp⟩ := hφ
  obtain ⟨q, hq⟩ := hnφ
  obtain ⟨hpm, hqm⟩ := lkProofCheck_append hp hq
  obtain ⟨hacc, hmemφ⟩ := (evalArithmetic_lkProofCheck_eq_one _ _).mp hpm
  have hmemnφ := ((evalArithmetic_lkProofCheck_eq_one _ _).mp hqm).2
  let cert := listAppend.evalArithmetic (Arithmetic.pair q p)
  let C := listAppend.evalArithmetic (Arithmetic.pair Δ Γ)
  let v := Arithmetic.pair (2 : M) 0 + 1
  let w := arithmeticLKWitness 1 φ v v 0 Γ Δ
  refine ⟨Arithmetic.pair (Arithmetic.pair C w) cert + 1, lkProofCheck_extend hacc ?_⟩
  change lkRuleCheck.evalArithmetic (Arithmetic.pair
    (Arithmetic.pi₁ (lkCertificateRun.evalArithmetic (Arithmetic.pair 0 cert)))
    (Arithmetic.pair C (arithmeticLKWitness 1 φ v v 0 Γ Δ))) = 1
  rw [arithmeticLKWitness, evalArithmetic_lkRuleCheck_eq_one]
  refine ⟨⟨(evalArithmetic_sequentCheck_append_iff true 0 Γ Δ).mpr ⟨hΓ.2, hΔ.2⟩,
    lkCertificateRun_valid _ hacc, hΓ.1, formulaCheck_verum _, formulaCheck_verum _, hΓ.2, hΔ.2⟩, ?_⟩
  simpa [arithmeticLKRuleCore, C, cert] using And.intro hmemφ hmemnφ

end PrimitiveProgram
end ZFVP
