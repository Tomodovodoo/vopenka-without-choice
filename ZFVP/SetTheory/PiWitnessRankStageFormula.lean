import ZFVP.SetTheory.PiWitnessRankStages
import ZFVP.SetTheory.PiOneWitnessRankBound

/-! The outer rank and its leastness certificate preserve the witness formula's Pi level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneWitnessRankStageBaseFormula : SetTheorySemisentence 6 :=
  “A ρ α e θ d. !piOneOrdinalOmegaHierarchyFormula A θ ∧ ∃ b ∈ A,
    !piOneWitnessRankBoundFormula b ρ α e ∧ !leastRankCriterionCertificateFormula θ d b”

def piWitnessRankStageFormula {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 2)) :
    SetTheorySemisentence (n + 6) :=
  (piOneWitnessRankStageBaseFormula.subst ![.bvar 0, .bvar 1, .bvar 2, .bvar 3, .bvar 4, .bvar 5]).and
    ((piWitnessFamilyCodeFormula k ψ).subst (.bvar 3 :> .bvar 2 :>
      fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ.succ))

theorem piOneWitnessRankStageBaseFormula_piOne : IsPiFormula 1 piOneWitnessRankStageBaseFormula :=
  .and (piOneOrdinalOmegaHierarchyFormula_piOne.subst _) (.boundedExs (.bvar 0)
    (.and (piOneWitnessRankBoundFormula_piOne.subst _) (leastRankCriterionCertificateFormula_piOne.subst _)))

theorem piWitnessRankStageFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ) : IsPiFormula (k + 1) (piWitnessRankStageFormula k ψ) :=
  .and ((piOneWitnessRankStageBaseFormula_piOne.mono (by omega)).subst _)
    ((piWitnessFamilyCodeFormula_pi hψ).subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_piOneWitnessRankStageBaseFormula (A ρ α e θ d : V) [IsOrdinal ρ] :
    piOneWitnessRankStageBaseFormula.Evalb ![A, ρ, α, e, θ, d] ↔
      A = hierarchy (ordinalAdd θ ω) ∧ IsOrdinal α ∧
        leastRankCriterionCertificateFormula.Evalb ![θ, d, witnessRankBound ρ α e] := by
  simp only [piOneWitnessRankStageBaseFormula]
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_piOneOrdinalOmegaHierarchyFormula, eval_piOneWitnessRankBoundFormula,
    show IsOrdinal ρ from inferInstance]
  constructor
  · rintro ⟨⟨_, hA⟩, _, hα, hd⟩
    exact ⟨hA, hα, hd⟩
  · rintro ⟨hA, hα, hd⟩
    let := hα
    have ht := ((eval_leastRankCriterionCertificateFormula _ _ _).mp hd).1
    let := ht.1
    have hb := ((eval_leastRankCriterionCertificateFormula _ _ _).mp hd).2.1
    have hbA : witnessRankBound ρ α e ∈ A := by
      rw [hA]
      exact ordinal_subset_hierarchy _ _ (IsOrdinal.toIsTransitive.mem_trans hb (ordinalAdd_omega_gt θ))
    exact ⟨⟨ht.1, hA⟩, hbA, hα, hd⟩

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_stage_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

theorem eval_piWitnessRankStageFormula {n k : ℕ} (ψ : SetTheorySemisentence (n + 2))
    (A ρ α e θ d : V) [IsOrdinal ρ] (v : Fin n → V) :
    (piWitnessRankStageFormula k ψ).Evalb (A :> ρ :> α :> e :> θ :> d :> v) ↔
      A = hierarchy (ordinalAdd θ ω) ∧ IsPiWitnessRankStage k ψ ρ α e θ d v := by
  simp [piWitnessRankStageFormula, eval_stage_and, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_piOneWitnessRankStageBaseFormula, IsPiWitnessRankStage, and_left_comm, and_comm]

end ZFVP
