import ZFVP.Syntax.DeltaOneMembershipTruth
import ZFVP.SetTheory.DeltaOneBoundedTruth

/-! Exact Levy-complexity bounds for the ambient level-one truth predicates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def exactSigmaOneTruthFormula : SetTheorySemisentence 3 :=
  “n φ b. ∃ A, !IsTransitive.dfn A ∧ !boundedNonemptyFormula A ∧
    !(sigmaOneMembershipModelTruthFormula true) A n φ b”

def exactPiOneTruthFormula : SetTheorySemisentence 3 :=
  “n φ b. ∀ A, !IsTransitive.dfn A → !boundedNonemptyFormula A →
    !boundedFunctionFormula b n A → !piOneMembershipTruthFormula A n φ b”

theorem exactSigmaOneTruthFormula_sigmaOne : IsLevyFormula .sigma 1 exactSigmaOneTruthFormula :=
  .exs (.and (.bounded (isTransitiveFormula_bounded.subst _))
    (.and (.bounded (boundedNonemptyFormula_bounded.subst _))
      ((sigmaOneMembershipModelTruthFormula_sigmaOne true).subst _)))

theorem exactPiOneTruthFormula_piOne : IsLevyFormula .pi 1 exactPiOneTruthFormula :=
  .all (.or (.bounded (isTransitiveFormula_bounded.subst _).neg)
    (.or (.bounded (boundedNonemptyFormula_bounded.subst _).neg)
      (.or (.bounded (boundedFunctionFormula_bounded.subst _).neg)
        (piOneMembershipTruthFormula_piOne.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_exactSigmaOneTruthFormula (n φ b : V) :
    exactSigmaOneTruthFormula.Evalb ![n, φ, b] ↔ SigmaOneTruth n φ b := by
  simp [exactSigmaOneTruthFormula, SigmaOneTruth]
  constructor
  · rintro ⟨A, ht, hA, hs⟩
    exact ⟨A, ht, hA, (membershipSatisfies_valid hs).2, hs⟩
  · rintro ⟨A, ht, hA, _, hs⟩
    exact ⟨A, ht, hA, hs⟩

theorem eval_exactPiOneTruthFormula (n φ b : V) :
    exactPiOneTruthFormula.Evalb ![n, φ, b] ↔ PiOneTruth n φ b := by
  simp [exactPiOneTruthFormula, PiOneTruth]

instance exactSigmaOneTruthFormula_defined : ℒₛₑₜ-relation₃[V] SigmaOneTruth via exactSigmaOneTruthFormula :=
  ⟨fun (v : Fin 3 → V) ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
    change exactSigmaOneTruthFormula.Evalb v ↔ SigmaOneTruth (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_exactSigmaOneTruthFormula (v 0) (v 1) (v 2)⟩

instance exactPiOneTruthFormula_defined : ℒₛₑₜ-relation₃[V] PiOneTruth via exactPiOneTruthFormula :=
  ⟨fun (v : Fin 3 → V) ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
    change exactPiOneTruthFormula.Evalb v ↔ PiOneTruth (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_exactPiOneTruthFormula (v 0) (v 1) (v 2)⟩

theorem exactSigmaOneTruthFormula_correct {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsSigmaFormula 1 φ) (b : Fin n → V) :
    exactSigmaOneTruthFormula.Evalb ![(n : V), encodeMembershipFormula φ, standardTuple b] ↔ φ.Evalb b :=
  (eval_exactSigmaOneTruthFormula _ _ _).trans (sigmaOneTruth_correct hφ b)

theorem exactPiOneTruthFormula_correct {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsPiFormula 1 φ) (b : Fin n → V) :
    exactPiOneTruthFormula.Evalb ![(n : V), encodeMembershipFormula φ, standardTuple b] ↔ φ.Evalb b :=
  (eval_exactPiOneTruthFormula _ _ _).trans (piOneTruth_correct hφ b)

end ZFVP
