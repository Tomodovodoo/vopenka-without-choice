import ZFVP.SetTheory.PiTwoDependentChoice
import ZFVP.SetTheory.SigmaThreeLeastPrefixCutoff
import ZFVP.SetTheory.WoodinSeedCardinal
import ZFVP.SetTheory.BoundedNaturals

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def leastDCFailureCertificate : SetTheorySemisentence 1 :=
  “κ. !IsOrdinal.dfn κ ∧ ¬!piTwoOrdinalDependentChoiceFormula κ ∧
    ∀ β ∈ κ, !piTwoOrdinalDependentChoiceFormula β”

theorem leastDCFailureCertificate_levy (pol : LevyPolarity) : IsLevyFormula pol 3 leastDCFailureCertificate :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.raise (piTwoOrdinalDependentChoiceFormula_piTwo.subst _).neg)
      (.raise (.boundedAll _ (piTwoOrdinalDependentChoiceFormula_piTwo.subst _))))

def totalLeastDCFailureCertificate : SetTheorySemisentence 1 :=
  “κ. !leastDCFailureCertificate κ ∨
    (!boundedEmptyFormula κ ∧ ∀ γ, !IsOrdinal.dfn γ → !piTwoOrdinalDependentChoiceFormula γ)”

theorem totalLeastDCFailureCertificate_levy (pol : LevyPolarity) :
    IsLevyFormula pol 3 totalLeastDCFailureCertificate :=
  .or ((leastDCFailureCertificate_levy pol).subst _)
    (.and (.bounded (boundedEmptyFormula_bounded.subst _))
      (.raise (.all (.or (.bounded (isOrdinalFormula_bounded.subst _).neg)
        (piTwoOrdinalDependentChoiceFormula_piTwo.subst _)))))

def sigmaThreeWoodinSeedCardinalFormula : SetTheorySemisentence 1 :=
  “z. ∃ κ, !totalLeastDCFailureCertificate κ ∧
    ((!boundedEmptyFormula κ ∧ !boundedOmegaFormula z) ∨ (¬!boundedEmptyFormula κ ∧ z = κ))”

theorem sigmaThreeWoodinSeedCardinalFormula_sigmaThree : IsSigmaFormula 3 sigmaThreeWoodinSeedCardinalFormula :=
  .exs (.and ((totalLeastDCFailureCertificate_levy .sigma).subst _)
    (.bounded (.or (.and (boundedEmptyFormula_bounded.subst _) (boundedOmegaFormula_bounded.subst _))
      (.and (boundedEmptyFormula_bounded.subst _).neg (.rel _ _)))))

def piThreeWoodinSeedCardinalFormula : SetTheorySemisentence 1 :=
  “z. ∀ w, !sigmaThreeWoodinSeedCardinalFormula w → z = w”

theorem piThreeWoodinSeedCardinalFormula_piThree : IsPiFormula 3 piThreeWoodinSeedCardinalFormula :=
  .all (.or (sigmaThreeWoodinSeedCardinalFormula_sigmaThree.subst _).neg (.bounded (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_leastDCFailureCertificate (κ : V) :
    leastDCFailureCertificate.Evalb ![κ] ↔ IsLeastDependentChoiceFailure κ := by
  rw [IsLeastDependentChoiceFailure, isLeastOrdinal_iff_no_smaller]
  simp [leastDCFailureCertificate]
  intro hk
  let := hk
  constructor
  · rintro ⟨hn, hb⟩
    exact ⟨hn hk, fun β hβ ↦ (hb β hβ).2⟩
  · rintro ⟨hn, hb⟩
    exact ⟨fun _ ↦ hn, fun β hβ ↦ ⟨IsOrdinal.of_mem hβ, hb β hβ⟩⟩

instance leastDCFailureCertificate_defined :
    ℒₛₑₜ-predicate[V] IsLeastDependentChoiceFailure via leastDCFailureCertificate :=
  ⟨fun v ↦ by
    have hv : v = ![v 0] := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change leastDCFailureCertificate.Evalb v ↔ _
    rw [hv]
    exact eval_leastDCFailureCertificate _⟩

instance totalLeastDCFailureCertificate_defined :
    ℒₛₑₜ-function₀[V] woodinLeastDCFailure via totalLeastDCFailureCertificate := by
  refine ⟨fun v ↦ ?_⟩
  change totalLeastDCFailureCertificate.Evalb v ↔ v 0 = woodinLeastDCFailure
  rw [woodinLeastDCFailure, leastOrdinalOrZero_eq_iff]
  simp [totalLeastDCFailureCertificate, IsLeastDependentChoiceFailure, zero_def]
  apply or_congr Iff.rfl
  exact ⟨fun h ↦ ⟨fun x hx ↦ (h.2 x hx).2, h.1⟩,
    fun h ↦ ⟨h.2, fun x hx ↦ ⟨hx, h.1 x hx⟩⟩⟩

instance sigmaThreeWoodinSeedCardinalFormula_defined :
    ℒₛₑₜ-function₀[V] woodinSeedCardinal via sigmaThreeWoodinSeedCardinalFormula := by
  refine ⟨fun v ↦ ?_⟩
  classical
  by_cases h : (woodinLeastDCFailure : V) = ∅ <;>
    simp [sigmaThreeWoodinSeedCardinalFormula, woodinSeedCardinal, h]
  intro _
  exact not_isEmpty_iff_isNonempty.mp (fun he ↦ h (isEmpty_iff_eq_empty.mp he))

instance piThreeWoodinSeedCardinalFormula_defined :
    ℒₛₑₜ-function₀[V] woodinSeedCardinal via piThreeWoodinSeedCardinalFormula :=
  ⟨fun v ↦ by simp [piThreeWoodinSeedCardinalFormula]⟩

end ZFVP
