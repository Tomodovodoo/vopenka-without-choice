import ZFVP.Syntax.SigmaOneBoundedCodes
import ZFVP.Syntax.LocalBoundedClosure
import ZFVP.SetTheory.BoundedIdentity

/-! Universal bounded closure tests give a Pi-one definition of bounded syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedClosureTestFormula : SetTheorySemisentence 4 :=
  “U O s Q. ∀ q ∈ U, !boundedCertificateStepFormula U O s Q q → q ∈ Q”

def piOneBoundedMatrix : SetTheorySemisentence 3 :=
  “U n φ. !codingSupportFormula U → n ∈ U → φ ∈ U →
    ∀ O ∈ U, !boundedOmegaFormula O → ∀ Q ∈ U, ∀ s ∈ U,
      (!boundedIdentityFormula s Q ∧ !boundedClosureTestFormula U O s Q) → !boundedPairMemberFormula Q n φ”

def piOneBoundedCodeFormula : SetTheorySemisentence 2 := .all piOneBoundedMatrix

theorem boundedClosureTestFormula_bounded : IsBoundedSetFormula boundedClosureTestFormula :=
  .all (.bvar 0) (.or (boundedCertificateStepFormula_bounded.subst _).neg (.rel _ _))

theorem piOneBoundedMatrix_bounded : IsBoundedSetFormula piOneBoundedMatrix :=
  .or (codingSupportFormula_bounded.subst _).neg (.or (.nrel _ _) (.or (.nrel _ _)
    (.all (.bvar 0) (.or (boundedOmegaFormula_bounded.subst _).neg
      (.all (.bvar 1) (.all (.bvar 2) (.or
        (IsBoundedSetFormula.and (boundedIdentityFormula_bounded.subst _) (boundedClosureTestFormula_bounded.subst _)).neg
        (boundedPairMemberFormula_bounded.subst _))))))))

theorem piOneBoundedCodeFormula_piOne : IsLevyFormula .pi 1 piOneBoundedCodeFormula :=
  .all (.bounded piOneBoundedMatrix_bounded)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem range_identity_restrict (Q : V) : range ((identity Q) ↾ Q) = Q := by
  apply mem_ext
  intro q
  simp [mem_range_iff]

theorem eval_boundedClosureTestFormula {U Q : V} [IsCodingSupport U] (hs : identity Q ∈ U) :
    boundedClosureTestFormula.Evalb ![U, ω, identity Q, Q] ↔ IsLocallyBoundedClosed U Q := by
  simp [boundedClosureTestFormula, IsLocallyBoundedClosed,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  refine forall_congr' fun q ↦ imp_congr_right fun hq ↦ ?_
  rw [eval_boundedCertificateStepFormula hs hq, range_identity_restrict]

theorem eval_piOneBoundedMatrix (U n φ : V) :
    piOneBoundedMatrix.Evalb ![U, n, φ] ↔
      (IsCodingSupport U → n ∈ U → φ ∈ U →
        ∀ Q ∈ U, identity Q ∈ U → IsLocallyBoundedClosed U Q → ⟨n, φ⟩ₖ ∈ Q) := by
  simp [piOneBoundedMatrix, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  refine imp_congr_right fun hU ↦ ?_
  let := hU
  refine imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  constructor
  · intro h Q hQ hs hclose
    exact h ω hU.omega_mem rfl Q hQ (identity Q) hs rfl ((eval_boundedClosureTestFormula hs).mpr hclose)
  · intro h O _ rfl Q hQ s hs rfl hclose
    exact h Q hQ hs ((eval_boundedClosureTestFormula hs).mp hclose)

theorem eval_piOneBoundedCodeFormula (n φ : V) :
    piOneBoundedCodeFormula.Evalb ![n, φ] ↔ IsBoundedFormulaCode n φ := by
  change (∀ U : V, piOneBoundedMatrix.Evalb ![U, n, φ]) ↔ _
  simp only [eval_piOneBoundedMatrix]
  constructor
  · intro h
    let Q : V := boundedFormulaFamily
    obtain ⟨U, hU, hX⟩ := codingSupport_containing ⟨⟨n, φ⟩ₖ, ⟨Q, identity Q⟩ₖ⟩ₖ
    let := hU
    obtain ⟨hnφ, hQs⟩ := kpair_components_mem_transitive hX
    obtain ⟨hn, hφ⟩ := kpair_components_mem_transitive hnφ
    obtain ⟨hQ, hs⟩ := kpair_components_mem_transitive hQs
    exact h U hU hn hφ Q hQ hs (boundedFormulaFamily_closed.locally U)
  · intro h U hU hn hφ Q _ _ hQ
    let := hU
    exact boundedFormulaFamily_local_minimal hQ _ h (hU.kpair_closed _ hn _ hφ)

instance piOneBoundedCodeFormula_defined :
    ℒₛₑₜ-relation[V] IsBoundedFormulaCode via piOneBoundedCodeFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change piOneBoundedCodeFormula.Evalb v ↔ IsBoundedFormulaCode (v 0) (v 1)
    rw [← hv]
    exact eval_piOneBoundedCodeFormula (v 0) (v 1)⟩

theorem boundedCode_definitions_equivalent (n φ : V) :
    sigmaOneBoundedCodeFormula.Evalb ![n, φ] ↔ piOneBoundedCodeFormula.Evalb ![n, φ] := by
  rw [eval_sigmaOneBoundedCodeFormula, eval_piOneBoundedCodeFormula]

end ZFVP
