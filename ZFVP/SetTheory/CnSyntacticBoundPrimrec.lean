import ZFVP.SetTheory.CnExtendible
import ZFVP.SetTheory.LevyComplexityBound
import Mathlib.Computability.Primrec.Basic

/-! Primitive recursive scalar bounds for the correctness and extendibility formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

private theorem levySyntacticBound_ballMem {n : ℕ}
    (t : SetTheorySemiterm Empty n) (φ : SetTheorySemisentence (n + 1)) :
    levySyntacticBound (Semiformula.ballMem t φ) = levySyntacticBound φ + 2 := by
  change max 0 (levySyntacticBound φ) + 2 = _
  rw [Nat.zero_max]

private def levyFamilyBoundStep (p : LevyPolarity) (a b : ℕ) : ℕ :=
  max a (max b (max (levySyntacticBound boundedUnionFormula)
    (levySyntacticBound (sigmaOneLevyExtensionFormula p)) + 2) + 2) + 2

private def levyFamilyBoundPair : ℕ → ℕ × ℕ :=
  Nat.rec (levySyntacticBound sigmaOneBoundedFamilyFormula,
    levySyntacticBound sigmaOneBoundedFamilyFormula)
    (fun _ b ↦ (levyFamilyBoundStep .sigma b.1 b.2, levyFamilyBoundStep .pi b.1 b.2))

private theorem levyFamilyBoundPair_eq (k : ℕ) :
    levyFamilyBoundPair k = (levySyntacticBound (sigmaOneLevyFamilyFormula k .sigma),
      levySyntacticBound (sigmaOneLevyFamilyFormula k .pi)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (levyFamilyBoundStep .sigma (levyFamilyBoundPair k).1 (levyFamilyBoundPair k).2,
      levyFamilyBoundStep .pi (levyFamilyBoundPair k).1 (levyFamilyBoundPair k).2) = _
    rw [ih]
    simp only [levyFamilyBoundStep, sigmaOneLevyFamilyFormula, levySyntacticBound,
      levySyntacticBound_rew]

private theorem levyFamilyBoundStep_primrec (p : LevyPolarity) :
    Primrec₂ (levyFamilyBoundStep p) :=
  Primrec.nat_add.comp
    (Primrec.nat_max.comp Primrec.fst
      (Primrec.nat_add.comp
        (Primrec.nat_max.comp Primrec.snd (Primrec.const _)) (Primrec.const 2)))
    (Primrec.const 2)

private theorem levyFamilyBoundPair_primrec : Primrec levyFamilyBoundPair :=
  Primrec.nat_rec₁ _
    (Primrec₂.pair.comp
      ((levyFamilyBoundStep_primrec .sigma).comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      ((levyFamilyBoundStep_primrec .pi).comp
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))

theorem sigmaOneLevyFamilyFormula_syntacticBound_primrec (p : LevyPolarity) :
    Primrec (fun k ↦ levySyntacticBound (sigmaOneLevyFamilyFormula k p)) := by
  cases p with
  | sigma =>
    exact (Primrec.fst.comp levyFamilyBoundPair_primrec).of_eq
      (fun k ↦ congrArg Prod.fst (levyFamilyBoundPair_eq k))
  | pi =>
    exact (Primrec.snd.comp levyFamilyBoundPair_primrec).of_eq
      (fun k ↦ congrArg Prod.snd (levyFamilyBoundPair_eq k))

theorem sigmaOneLevyCodeFormula_syntacticBound_primrec (p : LevyPolarity) :
    Primrec (fun k ↦ levySyntacticBound (sigmaOneLevyCodeFormula p k)) := by
  refine (Primrec.nat_add.comp
    (Primrec.nat_max.comp (sigmaOneLevyFamilyFormula_syntacticBound_primrec p)
      (Primrec.const (levySyntacticBound boundedPairMemberFormula))) (Primrec.const 2)).of_eq ?_
  intro k
  simp only [sigmaOneLevyCodeFormula, levySyntacticBound, levySyntacticBound_rew]

private def correctDomainBoundStep (k b : ℕ) : ℕ :=
  max b (max (levySyntacticBound (sigmaOneLevyCodeFormula .sigma (k + 1)))
    (max (levySyntacticBound boundedFunctionFormula)
      (max (max b (max (levySyntacticBound boundedFunctionFormula)
        (levySyntacticBound (sigmaOneMembershipModelTruthFormula true))) + 2)
        (levySyntacticBound piOneMembershipTruthFormula))) + 2 + 2 + 2)

private theorem correctDomainBoundStep_eq (k : ℕ) :
    correctDomainBoundStep k (levySyntacticBound (correctDomainFormula k)) =
      levySyntacticBound (correctDomainFormula (k + 1)) := by
  unfold correctDomainBoundStep
  simp only [correctDomainFormula, domainSigmaTruthFormula, levySyntacticBound_ballMem,
    levySyntacticBound, Semiformula.imp_eq, levySyntacticBound_neg, levySyntacticBound_rew]

private theorem correctDomainBoundStep_primrec : Primrec₂ correctDomainBoundStep := by
  have hc := sigmaOneLevyCodeFormula_syntacticBound_primrec .sigma
  exact Primrec.nat_max.comp Primrec.snd
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_max.comp (hc.comp (Primrec.succ.comp Primrec.fst))
        (Primrec.nat_max.comp (Primrec.const _)
          (Primrec.nat_max.comp
            (Primrec.nat_add.comp (Primrec.nat_max.comp Primrec.snd (Primrec.const _))
              (Primrec.const 2)) (Primrec.const _))))
      (Primrec.const 2)) (Primrec.const 2)) (Primrec.const 2))

theorem correctDomainFormula_syntacticBound_primrec :
    Primrec (fun k ↦ levySyntacticBound (correctDomainFormula k)) := by
  refine (Primrec.nat_rec₁ (levySyntacticBound sequenceSupportFormula)
    correctDomainBoundStep_primrec).of_eq ?_
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change correctDomainBoundStep k _ = _
    rw [ih]
    exact correctDomainBoundStep_eq k

theorem piCorrectRankStageFormula_syntacticBound_primrec :
    Primrec (fun k ↦ levySyntacticBound (piCorrectRankStageFormula k)) := by
  refine (Primrec.nat_max.comp (Primrec.const (levySyntacticBound IsOrdinal.dfn))
    (Primrec.nat_add.comp
      (Primrec.nat_max.comp (Primrec.const (levySyntacticBound piOneHierarchyFormula))
        correctDomainFormula_syntacticBound_primrec) (Primrec.const 2))).of_eq ?_
  intro k
  simp only [piCorrectRankStageFormula, levySyntacticBound, Semiformula.imp_eq,
    levySyntacticBound_neg, levySyntacticBound_rew]

theorem cnFormula_syntacticBound_primrec :
    Primrec (fun k ↦ levySyntacticBound (cnFormula k)) := by
  refine (Primrec.nat_casesOn₁ (levySyntacticBound IsOrdinal.dfn)
    (piCorrectRankStageFormula_syntacticBound_primrec.comp Primrec.succ)).of_eq ?_
  intro k
  cases k <;> rfl

private theorem levySyntacticBound_nestFormulae_one {m : ℕ}
    (φ : SetTheorySemisentence 1) (ψ : SetTheorySemisentence (m + 1)) :
    levySyntacticBound (Semiformula.nestFormulae φ ![ψ]) =
      max (levySyntacticBound ψ) (levySyntacticBound φ) + 2 := by
  unfold Semiformula.nestFormulae
  simp only [allItr_succ, allItr_zero, Matrix.conj, Semiformula.imp_eq, levySyntacticBound,
    levySyntacticBound_neg, levySyntacticBound_rew, Nat.max_zero, Matrix.cons_val_zero]

private def cnExtendibleSyntacticTemplate (D : SetTheorySemisentence 1) :
    SetTheorySemisentence 1 :=
  f“κ. !initialOrdinalFormula κ ∧ ∀ μ, !D μ → κ ∈ μ →
    ∃ ν e, μ ∈ ν ∧ !D ν ∧
      !piOneMembershipEmbeddingFormula (!hierarchyFormula μ) (!hierarchyFormula ν) e ∧
      !boundedCriticalPointFormula (!hierarchyFormula μ) e κ ∧ μ ∈ !value.dfn e κ”

private theorem extendibleBoundScalar_eq (b A B C D E F : ℕ) :
    max A (max (max B b + 2) (max C (max D (max (max E b + 2) F) + 2 + 2)) + 2) =
      max (max A (max (max B 0 + 2) (max C (max D (max (max E 0 + 2) F) + 2 + 2)) + 2))
        (b + 8) := by
  simp only [Nat.max_zero, ← Nat.add_max_add_right, Nat.add_assoc, Nat.reduceAdd]
  calc
    _ = max (max A (max (B + 4) (max (C + 2) (max (D + 6) (max (E + 8) (F + 6))))))
        (max (b + 4) (b + 8)) := by ac_rfl
    _ = _ := by
      rw [Nat.max_eq_right (show b + 4 ≤ b + 8 by omega)]

private theorem cnExtendibleSyntacticTemplate_bound (D : SetTheorySemisentence 1) :
    levySyntacticBound (cnExtendibleSyntacticTemplate D) =
      max (levySyntacticBound (cnExtendibleSyntacticTemplate ⊥)) (levySyntacticBound D + 8) := by
  simp only [cnExtendibleSyntacticTemplate, levySyntacticBound_nestFormulae_one, levySyntacticBound,
    Semiformula.imp_eq, levySyntacticBound_neg]
  exact extendibleBoundScalar_eq _ _ _ _ _ _ _

theorem cnExtendibleFormula_syntacticBound_primrec :
    Primrec (fun k ↦ levySyntacticBound (cnExtendibleFormula k)) := by
  refine (Primrec.nat_max.comp
    (Primrec.const (levySyntacticBound (cnExtendibleSyntacticTemplate ⊥)))
    (Primrec.nat_add.comp cnFormula_syntacticBound_primrec (Primrec.const 8))).of_eq ?_
  intro k
  exact (cnExtendibleSyntacticTemplate_bound (cnFormula k)).symm

private def unboundedSyntacticTemplate (D : SetTheorySemisentence 1) : SetTheorySentence :=
  “∀ α, !IsOrdinal.dfn α → ∃ κ, α ∈ κ ∧ !D κ”

private theorem unboundedSyntacticTemplate_bound (D : SetTheorySemisentence 1) :
    levySyntacticBound (unboundedSyntacticTemplate D) =
      max (levySyntacticBound (unboundedSyntacticTemplate ⊥)) (levySyntacticBound D + 4) := by
  simp only [unboundedSyntacticTemplate, levySyntacticBound,
    Semiformula.imp_eq, levySyntacticBound_neg, levySyntacticBound_rew]
  omega

theorem unboundedExtendibilitySentence_syntacticBound_primrec :
    Primrec (fun k ↦ levySyntacticBound (unboundedExtendibilitySentence k)) := by
  refine (Primrec.nat_max.comp
    (Primrec.const (levySyntacticBound (unboundedSyntacticTemplate ⊥)))
    (Primrec.nat_add.comp cnExtendibleFormula_syntacticBound_primrec (Primrec.const 4))).of_eq ?_
  intro k
  exact (unboundedSyntacticTemplate_bound (cnExtendibleFormula k)).symm

theorem unboundedCnFormula_syntacticBound_primrec :
    Primrec (fun k ↦ levySyntacticBound
      (“∀ α, !IsOrdinal.dfn α → ∃ κ, α ∈ κ ∧ !(cnFormula k) κ” : SetTheorySentence)) := by
  refine (Primrec.nat_max.comp
    (Primrec.const (levySyntacticBound (unboundedSyntacticTemplate ⊥)))
    (Primrec.nat_add.comp cnFormula_syntacticBound_primrec (Primrec.const 4))).of_eq ?_
  intro k
  exact (unboundedSyntacticTemplate_bound (cnFormula k)).symm

end ZFVP
