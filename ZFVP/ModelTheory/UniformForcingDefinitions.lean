import ZFVP.ModelTheory.InternalGenericTruth
import ZFVP.Syntax.BoundedInternalForcingAtoms
import ZFVP.Syntax.DictionaryComplexity
import ZFVP.Syntax.SigmaOneInternalForcing

/-! Endpoint-free defining formulas for the forcing relation, one per standard Levy level.

For each polarity `p` and each standard `k` this file gives a single formula
`uniformForcingLevelFormula p k` in the seven variables `P R D n φ b q`, together with the
Levy bound `uniformForcingLevelBound p k` that it meets and a proof that it defines
`internalForcingSet` on codes of level `k`.  The bound is a computable function of `p` and `k`
alone: it does not mention the poset `P`, the order `R` or the name set `D`.

The truth lemma at each level is `ForcingContext.levelGenericTruth`, with the two directions
also stated separately.  Nothing here refers to any particular forcing iteration. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Levy codes are membership formula codes -/

theorem IsLevyFormulaCode.membershipCode {p : LevyPolarity} {k : ℕ} {n φ : V}
    (h : IsLevyFormulaCode p k n φ) : IsMembershipFormulaCode n φ :=
  levyFormulaFamily_subset k p _ h

/-! ### The uniform forcing formula against the forcing set -/

theorem eval_uniformForcing {P R D n φ b p : V}
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ D ^ n) (hp : p ∈ P) :
    sigmaOneInternalForcingFormula.Evalb ![P, R, D, n, φ, b, p] ↔
      p ∈ internalForcingSet P R D n φ b :=
  (eval_sigmaOneInternalForcingFormula hφ hb hp).trans (mem_internalForcingSet hφ).symm

/-! ### The atomic clause -/

theorem uniformAtomicForcingFormula_bounded :
    IsBoundedSetFormula boundedInternalForcingAtomicFormula :=
  boundedInternalForcingAtomicFormula_bounded

theorem uniformAtomicForcingFormula_levy (p : LevyPolarity) (k : ℕ) :
    IsLevyFormula p k boundedInternalForcingAtomicFormula :=
  .bounded boundedInternalForcingAtomicFormula_bounded

theorem eval_uniformAtomicForcing {U P R H n b : V} [IsCodingSupport U]
    (hH : IsAtomicTruthTable P R U H) (hn : n ∈ U) (hb : b ∈ U ^ n) {r args p : V} (hp : p ∈ P) :
    boundedInternalForcingAtomicFormula.Evalb ![U, P, R, H, n, b, r, args, p] ↔
      p ∈ internalAtomicForcingSet P R n b r args := by
  rw [eval_boundedInternalForcingAtomicFormula hH hn hb r args p, mem_internalAtomicForcingSet]
  exact (and_iff_right hp).symm

theorem uniformForcing_atom {P R D n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (atomCode r args) b = internalAtomicForcingSet P R n b r args :=
  internalForcingSet_atom hn ha hb

theorem uniformForcing_negAtom {P R D n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (negAtomCode r args) b =
      forcingNegation P R (internalAtomicForcingSet P R n b r args) :=
  internalForcingSet_negAtom hn ha hb

/-! ### The level formula and its bound -/

/-- The forcing relation restricted to codes of Levy level `k` and polarity `p`. -/
def uniformForcingLevelFormula (p : LevyPolarity) (k : ℕ) : SetTheorySemisentence 7 :=
  “P R D n φ b q. !(isLevyFormulaCodeFormula p k) n φ ∧
    !sigmaOneInternalForcingFormula P R D n φ b q”

/-- A computable Levy bound for `uniformForcingLevelFormula p k`, depending on `p` and `k` only. -/
def uniformForcingLevelBound (p : LevyPolarity) (k : ℕ) : ℕ :=
  max 1 (levyCodeDefinitionBound p k)

theorem uniformForcingLevelFormula_sigma (p : LevyPolarity) (k : ℕ) :
    IsSigmaFormula (uniformForcingLevelBound p k) (uniformForcingLevelFormula p k) :=
  .and (((levyFormulaCodeFormula_complexity p k .sigma).subst _).mono (Nat.le_max_right _ _))
    ((sigmaOneInternalForcingFormula_sigmaOne.subst _).mono (Nat.le_max_left _ _))

theorem eval_uniformForcingLevelFormula {pol : LevyPolarity} {k : ℕ} {P R D n φ b q : V}
    (hb : b ∈ D ^ n) (hq : q ∈ P) :
    (uniformForcingLevelFormula pol k).Evalb ![P, R, D, n, φ, b, q] ↔
      IsLevyFormulaCode pol k n φ ∧ q ∈ internalForcingSet P R D n φ b := by
  have h : (uniformForcingLevelFormula pol k).Evalb ![P, R, D, n, φ, b, q] ↔
      IsLevyFormulaCode pol k n φ ∧
        sigmaOneInternalForcingFormula.Evalb ![P, R, D, n, φ, b, q] := by
    simp [uniformForcingLevelFormula, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton]
  rw [h]
  exact and_congr_right fun hc ↦ eval_uniformForcing hc.membershipCode hb hq

theorem uniformForcingLevelFormula_mono {pol : LevyPolarity} {k l : ℕ} (hkl : k ≤ l)
    {P R D n φ b q : V} (hb : b ∈ D ^ n) (hq : q ∈ P)
    (h : (uniformForcingLevelFormula pol k).Evalb ![P, R, D, n, φ, b, q]) :
    (uniformForcingLevelFormula pol l).Evalb ![P, R, D, n, φ, b, q] := by
  obtain ⟨hc, hf⟩ := (eval_uniformForcingLevelFormula hb hq).mp h
  exact (eval_uniformForcingLevelFormula hb hq).mpr ⟨hc.mono hkl, hf⟩

/-! ### The truth lemma at each level -/

namespace ForcingContext

theorem levelGenericTruth (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {pol : LevyPolarity} {k : ℕ} {n φ : V}
    (hφ : IsLevyFormulaCode pol k n φ) : A.GroundGenericTruth D hD n φ :=
  A.groundGenericTruth D hD hφ.membershipCode

/-- Soundness: a condition of the generic filter that forces the code makes it true. -/
theorem levelGenericTruth_sound (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {pol : LevyPolarity} {k : ℕ} {n φ b p : V}
    (hφ : IsLevyFormulaCode pol k n φ) (hb : b ∈ D ^ n) (hpG : p ∈ A.G)
    (hp : p ∈ internalForcingSet A.P A.R D n φ b) :
    MembershipSatisfies (range (A.evaluationGraph D hD)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function hD hb)) :=
  (A.levelGenericTruth D hD hφ b hb).mpr ⟨p, hpG, hp⟩

/-- Truth lemma: a true code is forced by some condition of the generic filter. -/
theorem levelGenericTruth_forced (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {pol : LevyPolarity} {k : ℕ} {n φ b : V}
    (hφ : IsLevyFormulaCode pol k n φ) (hb : b ∈ D ^ n)
    (h : MembershipSatisfies (range (A.evaluationGraph D hD)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function hD hb))) :
    ∃ p ∈ A.G, p ∈ internalForcingSet A.P A.R D n φ b :=
  (A.levelGenericTruth D hD hφ b hb).mp h

end ForcingContext
end ZFVP
