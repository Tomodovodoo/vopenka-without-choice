import ZFVP.SetTheory.ForcingUniqueName
import ZFVP.SetTheory.PiOneHierarchy
import ZFVP.SetTheory.DeltaOneForcingNames
import ZFVP.SetTheory.SigmaThreeLeastPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingWitnessEntryFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 5 :=
  “P R a ν p. !sigmaOneForcingNameFormula P ν ∧ !θ P R a ν p”

def forcingWitnessExistsFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 4 :=
  “P R a p. ∃ ν, !(forcingWitnessEntryFormula θ) P R a ν p”

def forcingWitnessBelowFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 5 :=
  “P R a p α. ∃ ν, !sigmaOneRankLtFormula ν α ∧ !(forcingWitnessEntryFormula θ) P R a ν p”

def forcingWitnessBoundBody (θ : SetTheorySemisentence 5) : SetTheorySemisentence 4 :=
  “P R a α. ∀ p ∈ P, !(forcingWitnessExistsFormula θ) P R a p →
    !(forcingWitnessBelowFormula θ) P R a p α”

def leastForcingWitnessBoundBody (θ : SetTheorySemisentence 5) : SetTheorySemisentence 4 :=
  “α P R a. !IsOrdinal.dfn α ∧ !(forcingWitnessBoundBody θ) P R a α ∧
    ∀ β ∈ α, ¬!(forcingWitnessBoundBody θ) P R a β”

theorem forcingWitnessEntryFormula_sigma {k : ℕ} {θ : SetTheorySemisentence 5}
    (hθ : IsSigmaFormula (k + 1) θ) : IsSigmaFormula (k + 1) (forcingWitnessEntryFormula θ) :=
  .and ((sigmaOneForcingNameFormula_sigmaOne.mono (by omega)).subst _) (hθ.subst _)

theorem forcingWitnessExistsFormula_sigma {k : ℕ} {θ : SetTheorySemisentence 5}
    (hθ : IsSigmaFormula (k + 1) θ) : IsSigmaFormula (k + 1) (forcingWitnessExistsFormula θ) :=
  .exs ((forcingWitnessEntryFormula_sigma hθ).subst _)

theorem forcingWitnessBelowFormula_sigma {k : ℕ} {θ : SetTheorySemisentence 5}
    (hθ : IsSigmaFormula (k + 1) θ) : IsSigmaFormula (k + 1) (forcingWitnessBelowFormula θ) :=
  .exs (.and ((sigmaOneRankLtFormula_sigmaOne.mono (by omega)).subst _)
    ((forcingWitnessEntryFormula_sigma hθ).subst _))

theorem forcingWitnessBoundBody_levy {k : ℕ} {θ : SetTheorySemisentence 5}
    (hθ : IsSigmaFormula (k + 1) θ) (pol : LevyPolarity) :
    IsLevyFormula pol (k + 2) (forcingWitnessBoundBody θ) :=
  .boundedAll (.bvar 0) (.or (.raise ((forcingWitnessExistsFormula_sigma hθ).subst _).neg)
    (.raise ((forcingWitnessBelowFormula_sigma hθ).subst _)))

theorem leastForcingWitnessBoundBody_levy {k : ℕ} {θ : SetTheorySemisentence 5}
    (hθ : IsSigmaFormula (k + 1) θ) (pol : LevyPolarity) :
    IsLevyFormula pol (k + 2) (leastForcingWitnessBoundBody θ) := by
  cases pol with
  | sigma =>
    exact .and (.bounded (isOrdinalFormula_bounded.subst _))
      (.and ((forcingWitnessBoundBody_levy hθ .sigma).subst _)
        (.boundedAll (.bvar 0) ((forcingWitnessBoundBody_levy hθ .pi).subst _).neg))
  | pi =>
    exact .and (.bounded (isOrdinalFormula_bounded.subst _))
      (.and ((forcingWitnessBoundBody_levy hθ .pi).subst _)
        (.boundedAll (.bvar 0) ((forcingWitnessBoundBody_levy hθ .sigma).subst _).neg))
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_forcingWitnessEntryFormula (θ : SetTheorySemisentence 5) (P R a ν p : V) :
    (forcingWitnessEntryFormula θ).Evalb ![P, R, a, ν, p] ↔
      IsForcingName P ν ∧ θ.Evalb ![P, R, a, ν, p] := by
  simp [forcingWitnessEntryFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]

theorem eval_forcingWitnessBoundBody (θ : SetTheorySemisentence 5) (P R a b α : V)
    (F : V → V → V) [IsOrdinal α]
    (he : ∀ ν : V, IsForcingName P ν → ∀ p : V,
      θ.Evalb ![P, R, a, ν, p] ↔ p ∈ F b ν) :
    (forcingWitnessBoundBody θ).Evalb ![P, R, a, α] ↔ IsForcingWitnessBound P F b α := by
  have hentry (ν p : V) : (forcingWitnessEntryFormula θ).Evalb ![P, R, a, ν, p] ↔
      IsForcingName P ν ∧ p ∈ F b ν := by
    rw [eval_forcingWitnessEntryFormula]
    exact and_congr_right fun hn ↦ he ν hn p
  have hex (p : V) : (forcingWitnessExistsFormula θ).Evalb ![P, R, a, p] ↔
      ∃ ν, IsForcingName P ν ∧ p ∈ F b ν := by
    have h : (forcingWitnessExistsFormula θ).Evalb ![P, R, a, p] ↔
        ∃ ν, (forcingWitnessEntryFormula θ).Evalb ![P, R, a, ν, p] := by
      simp [forcingWitnessExistsFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
        Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
    simp only [h, hentry]
  have hbelow (p : V) : (forcingWitnessBelowFormula θ).Evalb ![P, R, a, p, α] ↔
      ∃ ν ∈ hierarchy α, IsForcingName P ν ∧ p ∈ F b ν := by
    have h : (forcingWitnessBelowFormula θ).Evalb ![P, R, a, p, α] ↔
        ∃ ν, rank ν ∈ α ∧ (forcingWitnessEntryFormula θ).Evalb ![P, R, a, ν, p] := by
      simp [forcingWitnessBelowFormula, sigmaOneRankLtFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
        Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
    simp only [h, hentry, mem_hierarchy_iff_rank_mem]
  have h : (forcingWitnessBoundBody θ).Evalb ![P, R, a, α] ↔
      ∀ p ∈ P, (forcingWitnessExistsFormula θ).Evalb ![P, R, a, p] →
        (forcingWitnessBelowFormula θ).Evalb ![P, R, a, p, α] := by
    simp [forcingWitnessBoundBody, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  simp only [h, hex, hbelow, IsForcingWitnessBound]
theorem eval_leastForcingWitnessBoundBody (θ : SetTheorySemisentence 5) (P R a b α : V)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    (he : ∀ ν : V, IsForcingName P ν → ∀ p : V,
      θ.Evalb ![P, R, a, ν, p] ↔ p ∈ F b ν) :
    (leastForcingWitnessBoundBody θ).Evalb ![α, P, R, a] ↔ α = forcingWitnessBound P F hF b := by
  have hb : (leastForcingWitnessBoundBody θ).Evalb ![α, P, R, a] ↔
      IsOrdinal α ∧ (forcingWitnessBoundBody θ).Evalb ![P, R, a, α] ∧
        ∀ β ∈ α, ¬(forcingWitnessBoundBody θ).Evalb ![P, R, a, β] := by
    simp [leastForcingWitnessBoundBody, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  have hs := leastOrdinalOrZero_spec (IsForcingWitnessBound P F)
    (forcingWitnessBound_definable P F hF) b (forcingWitnessBound_exists P F hF b)
  have hl : (leastForcingWitnessBoundBody θ).Evalb ![α, P, R, a] ↔
      IsLeastOrdinal (IsForcingWitnessBound P F b) α := by
    rw [hb, isLeastOrdinal_iff_no_smaller]
    apply and_congr_right
    intro ha
    let := ha
    rw [eval_forcingWitnessBoundBody θ P R a b α F he]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro β
    apply forall_congr'
    intro hβ
    let := IsOrdinal.of_mem hβ
    rw [eval_forcingWitnessBoundBody θ P R a b β F he]
  rw [hl]
  constructor
  · intro h
    exact subset_antisymm (h.2.2 _ hs.1 hs.2.1) (hs.2.2 _ h.1 h.2.1)
  · rintro rfl
    exact hs

end ZFVP




