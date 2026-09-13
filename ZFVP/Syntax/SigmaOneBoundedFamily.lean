import ZFVP.Syntax.BoundedFixedPoints
import ZFVP.Syntax.CodingSupportSyntax

/-! The entire internal bounded-syntax family has a Sigma-one set definition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedFixedPointFormula : SetTheorySemisentence 4 :=
  “U O Q s. ∀ q ∈ U, q ∈ Q ↔ !boundedCertificateStepFormula U O s Q q”

def boundedFamilyWitnessFormula : SetTheorySemisentence 2 :=
  “U Q. !codingSupportFormula U ∧ Q ∈ U ∧ ∃ O ∈ U, !boundedOmegaFormula O ∧
    ∃ s ∈ U, !boundedIdentityFormula s Q ∧ !boundedFixedPointFormula U O Q s”

def sigmaOneBoundedFamilyFormula : SetTheorySemisentence 1 := .exs boundedFamilyWitnessFormula

theorem boundedFixedPointFormula_bounded : IsBoundedSetFormula boundedFixedPointFormula :=
  .all (.bvar 0) (.and (.or (.nrel _ _) (boundedCertificateStepFormula_bounded.subst _))
    (.or (boundedCertificateStepFormula_bounded.subst _).neg (.rel _ _)))

theorem boundedFamilyWitnessFormula_bounded : IsBoundedSetFormula boundedFamilyWitnessFormula :=
  .and (codingSupportFormula_bounded.subst _) (.and (.rel _ _) (.exs (.bvar 0)
    (.and (boundedOmegaFormula_bounded.subst _) (.exs (.bvar 1)
      (.and (boundedIdentityFormula_bounded.subst _) (boundedFixedPointFormula_bounded.subst _))))))

theorem sigmaOneBoundedFamilyFormula_sigmaOne : IsLevyFormula .sigma 1 sigmaOneBoundedFamilyFormula :=
  .exs (.bounded boundedFamilyWitnessFormula_bounded)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedFixedPointFormula {U Q : V} [hU : IsCodingSupport U]
    (hQ : Q ∈ U) (hs : identity Q ∈ U) :
    boundedFixedPointFormula.Evalb ![U, ω, Q, identity Q] ↔ Q = (boundedFormulaFamily : V) := by
  have he : boundedFixedPointFormula.Evalb ![U, ω, Q, identity Q] ↔
      ∀ q ∈ U, q ∈ Q ↔ BoundedDerivationStep Q q := by
    simp [boundedFixedPointFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    refine forall_congr' fun q ↦ imp_congr_right fun hq ↦ ?_
    rw [eval_boundedCertificateStepFormula hs hq, range_identity_restrict]
  rw [he]
  constructor
  · intro h
    apply SetTheory.subset_antisymm
    · exact bounded_postfixed_subset (fun q hq ↦ (h q (hU.mem_trans hq hQ)).mp hq)
    · exact fun q hq ↦ boundedFormulaFamily_local_minimal (fun x hx hh ↦ (h x hx).mpr hh)
        q hq (boundedFormulaFamily_subset_support U q hq)
  · rintro rfl
    intro q _
    exact ⟨boundedFormulaFamily_step q,
      fun h ↦ boundedDerivationStep_closed boundedFormulaFamily_closed (fun _ h ↦ h) h⟩

theorem eval_sigmaOneBoundedFamilyFormula (Q : V) :
    sigmaOneBoundedFamilyFormula.Evalb ![Q] ↔ Q = (boundedFormulaFamily : V) := by
  change (∃ U : V, boundedFamilyWitnessFormula.Evalb ![U, Q]) ↔ _
  have he (U : V) : boundedFamilyWitnessFormula.Evalb ![U, Q] ↔
      IsCodingSupport U ∧ Q ∈ U ∧ identity Q ∈ U ∧ Q = (boundedFormulaFamily : V) := by
    simp [boundedFamilyWitnessFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    intro hU
    let := hU
    intro hQ
    rw [and_iff_right hU.omega_mem]
    apply and_congr_right
    intro hs
    exact eval_boundedFixedPointFormula hQ hs
  simp only [he]
  constructor
  · rintro ⟨_, _, _, _, h⟩
    exact h
  · intro h
    obtain ⟨U, hU, hpair⟩ := codingSupport_containing ⟨Q, identity Q⟩ₖ
    let := hU
    obtain ⟨hQ, hs⟩ := kpair_components_mem_transitive hpair
    exact ⟨U, hU, hQ, hs, h⟩

instance sigmaOneBoundedFamilyFormula_defined :
    ℒₛₑₜ-function₀[V] (boundedFormulaFamily : V) via sigmaOneBoundedFamilyFormula :=
  ⟨fun (v : Fin 1 → V) ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change sigmaOneBoundedFamilyFormula.Evalb v ↔ v 0 = boundedFormulaFamily
    rw [← hv]
    exact eval_sigmaOneBoundedFamilyFormula (v 0)⟩

end ZFVP
