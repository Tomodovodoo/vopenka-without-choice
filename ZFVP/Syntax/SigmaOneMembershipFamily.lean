import ZFVP.Syntax.BoundedMembershipStep

/-! The entire internal pure membership syntax family has a Sigma-one set definition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def membershipFixedPointFormula : SetTheorySemisentence 4 :=
  “U O Q s. ∀ q ∈ U, q ∈ Q ↔ !boundedMembershipStepFormula U O s Q q”

def membershipFamilyWitnessFormula : SetTheorySemisentence 2 :=
  “U Q. !codingSupportFormula U ∧ Q ∈ U ∧ ∃ O ∈ U, !boundedOmegaFormula O ∧
    ∃ s ∈ U, !boundedIdentityFormula s Q ∧ !membershipFixedPointFormula U O Q s”

def sigmaOneMembershipFamilyFormula : SetTheorySemisentence 1 := .exs membershipFamilyWitnessFormula

theorem membershipFixedPointFormula_bounded : IsBoundedSetFormula membershipFixedPointFormula :=
  .all (.bvar 0) (.and (.or (.nrel _ _) (boundedMembershipStepFormula_bounded.subst _))
    (.or (boundedMembershipStepFormula_bounded.subst _).neg (.rel _ _)))

theorem membershipFamilyWitnessFormula_bounded : IsBoundedSetFormula membershipFamilyWitnessFormula :=
  .and (codingSupportFormula_bounded.subst _) (.and (.rel _ _) (.exs (.bvar 0)
    (.and (boundedOmegaFormula_bounded.subst _) (.exs (.bvar 1)
      (.and (boundedIdentityFormula_bounded.subst _) (membershipFixedPointFormula_bounded.subst _))))))

theorem sigmaOneMembershipFamilyFormula_sigmaOne : IsLevyFormula .sigma 1 sigmaOneMembershipFamilyFormula :=
  .exs (.bounded membershipFamilyWitnessFormula_bounded)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_membershipFixedPointFormula {U Q : V} [hU : IsCodingSupport U]
    (hQ : Q ∈ U) (hs : identity Q ∈ U) :
    membershipFixedPointFormula.Evalb ![U, ω, Q, identity Q] ↔ Q = (formulaFamily membershipLanguageCode ∅ : V) := by
  have he : membershipFixedPointFormula.Evalb ![U, ω, Q, identity Q] ↔
      ∀ q ∈ U, q ∈ Q ↔ MembershipDerivationStep Q q := by
    simp [membershipFixedPointFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    refine forall_congr' fun q ↦ imp_congr_right fun hq ↦ ?_
    rw [eval_boundedMembershipStepFormula hs hq, range_identity_restrict]
  rw [he]
  constructor
  · intro h
    apply SetTheory.subset_antisymm
    · exact membership_postfixed_subset (fun q hq ↦ (h q (hU.mem_trans hq hQ)).mp hq)
    · exact fun q hq ↦ membershipFormulaFamily_local_minimal (fun x hx hh ↦ (h x hx).mpr hh) q hq
  · rintro rfl
    intro q _
    exact ⟨membershipFormulaFamily_step q,
      fun h ↦ membershipDerivationStep_closed (formulaFamily_closed membershipLanguageCode_valid ∅) h⟩

theorem eval_sigmaOneMembershipFamilyFormula (Q : V) :
    sigmaOneMembershipFamilyFormula.Evalb ![Q] ↔ Q = (formulaFamily membershipLanguageCode ∅ : V) := by
  change (∃ U : V, membershipFamilyWitnessFormula.Evalb ![U, Q]) ↔ _
  have he (U : V) : membershipFamilyWitnessFormula.Evalb ![U, Q] ↔
      IsCodingSupport U ∧ Q ∈ U ∧ identity Q ∈ U ∧ Q = (formulaFamily membershipLanguageCode ∅ : V) := by
    simp [membershipFamilyWitnessFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    intro hU
    let := hU
    intro hQ
    rw [and_iff_right hU.omega_mem]
    apply and_congr_right
    intro hs
    exact eval_membershipFixedPointFormula hQ hs
  simp only [he]
  constructor
  · rintro ⟨_, _, _, _, h⟩
    exact h
  · intro h
    obtain ⟨U, hU, hpair⟩ := codingSupport_containing ⟨Q, identity Q⟩ₖ
    let := hU
    obtain ⟨hQ, hs⟩ := kpair_components_mem_transitive hpair
    exact ⟨U, hU, hQ, hs, h⟩

instance sigmaOneMembershipFamilyFormula_defined :
    ℒₛₑₜ-function₀[V] (formulaFamily membershipLanguageCode ∅ : V) via sigmaOneMembershipFamilyFormula :=
  ⟨fun (v : Fin 1 → V) ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change sigmaOneMembershipFamilyFormula.Evalb v ↔ v 0 = formulaFamily membershipLanguageCode ∅
    rw [← hv]
    exact eval_sigmaOneMembershipFamilyFormula (v 0)⟩

end ZFVP
