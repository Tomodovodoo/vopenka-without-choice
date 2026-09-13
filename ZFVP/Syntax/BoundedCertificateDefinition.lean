import ZFVP.Syntax.BoundedCertificateStep

/-! Bounded verification of a complete internally finite certificate. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedCertificateFormula : SetTheorySemisentence 4 :=
  “U O s m. !boundedFunctionFormula s m U ∧ ∀ i ∈ m, ∃ q ∈ U,
    !boundedPairMemberFormula s i q ∧ !boundedCertificateStepFormula U O s i q”

theorem boundedCertificateFormula_bounded : IsBoundedSetFormula boundedCertificateFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (.all (.bvar 3) (.exs (.bvar 1)
    (.and (boundedPairMemberFormula_bounded.subst _) (boundedCertificateStepFormula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedCertificateFormula {U s : V} [IsCodingSupport U] (hs : s ∈ U) (m : V) :
    boundedCertificateFormula.Evalb ![U, ω, s, m] ↔
      s ∈ U ^ m ∧ ∀ i ∈ m, BoundedDerivationStep (range (s ↾ i)) (s ‘ i) := by
  simp [boundedCertificateFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  intro hf
  have : IsFunction s := IsFunction.of_mem hf
  refine forall_congr' fun i ↦ imp_congr_right fun hi ↦ ?_
  constructor
  · rintro ⟨q, hq, hp, hstep⟩
    have he := value_eq_of_kpair_mem hp
    rw [← he] at hstep
    exact (eval_boundedCertificateStepFormula hs (he ▸ hq) i).mp hstep
  · intro hstep
    have hval : s ‘ i ∈ U := function_value_mem hf hi
    exact ⟨s ‘ i, hval, kpair_value_mem (domain_eq_of_mem_function hf ▸ hi),
      (eval_boundedCertificateStepFormula hs hval i).mpr hstep⟩

theorem boundedCertificateFormula_iff {U s m : V} [IsCodingSupport U]
    (hs : s ∈ U) (hm : m ∈ (ω : V)) :
    boundedCertificateFormula.Evalb ![U, ω, s, m] ↔ IsBoundedCertificate s ∧ domain s = m := by
  rw [eval_boundedCertificateFormula hs]
  constructor
  · rintro ⟨hf, hstep⟩
    have hd := domain_eq_of_mem_function hf
    exact ⟨⟨IsFunction.of_mem hf, hd ▸ hm, hd ▸ hstep⟩, hd⟩
  · rintro ⟨⟨hf, _, hstep⟩, rfl⟩
    let := hf
    refine ⟨?_, hstep⟩
    exact mem_function_of_mem_function_of_subset (IsFunction.mem_function s) (range_subset_codingSupport hs)

end ZFVP
