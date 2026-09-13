import ZFVP.Syntax.BoundedLevySteps

/-! A Levy extension of a valid base family has a Sigma-one set definition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def levyFixedPointFormula (p : LevyPolarity) : SetTheorySemisentence 5 :=
  “U O B Q s. ∀ q ∈ U, q ∈ Q ↔ !(boundedLevyStepFormula p) U O B s Q q”

def levyExtensionWitnessFormula (p : LevyPolarity) : SetTheorySemisentence 3 :=
  “U Q B. !codingSupportFormula U ∧ Q ∈ U ∧ ∃ O ∈ U, !boundedOmegaFormula O ∧
    ∃ s ∈ U, !boundedIdentityFormula s Q ∧ !(levyFixedPointFormula p) U O B Q s”

def sigmaOneLevyExtensionFormula (p : LevyPolarity) : SetTheorySemisentence 2 :=
  .exs (levyExtensionWitnessFormula p)

theorem levyFixedPointFormula_bounded (p : LevyPolarity) : IsBoundedSetFormula (levyFixedPointFormula p) :=
  .all (.bvar 0) (.and (.or (.nrel _ _) ((boundedLevyStepFormula_bounded p).subst _))
    (.or ((boundedLevyStepFormula_bounded p).subst _).neg (.rel _ _)))

theorem levyExtensionWitnessFormula_bounded (p : LevyPolarity) : IsBoundedSetFormula (levyExtensionWitnessFormula p) :=
  .and (codingSupportFormula_bounded.subst _) (.and (.rel _ _) (.exs (.bvar 0)
    (.and (boundedOmegaFormula_bounded.subst _) (.exs (.bvar 1)
      (.and (boundedIdentityFormula_bounded.subst _) ((levyFixedPointFormula_bounded p).subst _))))))

theorem sigmaOneLevyExtensionFormula_sigmaOne (p : LevyPolarity) :
    IsLevyFormula .sigma 1 (sigmaOneLevyExtensionFormula p) :=
  .exs (.bounded (levyExtensionWitnessFormula_bounded p))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_levyFixedPointFormula (p : LevyPolarity) {U B Q : V} [hU : IsCodingSupport U]
    (hB : B ⊆ formulaFamily membershipLanguageCode ∅) (hQ : Q ∈ U) (hs : identity Q ∈ U) :
    (levyFixedPointFormula p).Evalb ![U, ω, B, Q, identity Q] ↔ Q = levyExtensionFamily p B := by
  have he : (levyFixedPointFormula p).Evalb ![U, ω, B, Q, identity Q] ↔
      ∀ q ∈ U, q ∈ Q ↔ LevyDerivationStep p B Q q := by
    simp [levyFixedPointFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    refine forall_congr' fun q ↦ imp_congr_right fun hq ↦ ?_
    rw [eval_boundedLevyStepFormula p hs hq, range_identity_restrict]
  rw [he]
  constructor
  · intro h
    apply SetTheory.subset_antisymm
    · exact levy_postfixed_subset hB (fun q hq ↦ (h q (hU.mem_trans hq hQ)).mp hq)
    · exact levyExtensionFamily_local_minimal hB (fun q hq hh ↦ (h q hq).mpr hh)
  · rintro rfl
    intro q _
    exact ⟨levyExtensionFamily_step p hB q, levyDerivationStep_closed (levyExtensionFamily_closed p hB)⟩

theorem eval_sigmaOneLevyExtensionFormula (p : LevyPolarity) {B : V}
    (hB : B ⊆ formulaFamily membershipLanguageCode ∅) (Q : V) :
    (sigmaOneLevyExtensionFormula p).Evalb ![Q, B] ↔ Q = levyExtensionFamily p B := by
  change (∃ U : V, (levyExtensionWitnessFormula p).Evalb ![U, Q, B]) ↔ _
  have he (U : V) : (levyExtensionWitnessFormula p).Evalb ![U, Q, B] ↔
      IsCodingSupport U ∧ Q ∈ U ∧ identity Q ∈ U ∧ Q = levyExtensionFamily p B := by
    simp [levyExtensionWitnessFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    intro hU
    let := hU
    intro hQ
    rw [and_iff_right hU.omega_mem]
    apply and_congr_right
    intro hs
    exact eval_levyFixedPointFormula p hB hQ hs
  simp only [he]
  constructor
  · rintro ⟨_, _, _, _, h⟩
    exact h
  · intro h
    obtain ⟨U, hU, hpair⟩ := codingSupport_containing ⟨Q, identity Q⟩ₖ
    let := hU
    obtain ⟨hQ, hs⟩ := kpair_components_mem_transitive hpair
    exact ⟨U, hU, hQ, hs, h⟩

end ZFVP
