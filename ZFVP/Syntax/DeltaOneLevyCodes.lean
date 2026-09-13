import ZFVP.Syntax.SigmaOneLevyExtension
import ZFVP.Syntax.SigmaOneBoundedFamily
import ZFVP.SetTheory.BoundedUnion

/-! At every standard level, internal Levy-code recognition has Sigma-one and Pi-one definitions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneLevyFamilyFormula : ℕ → LevyPolarity → SetTheorySemisentence 1
  | 0, _ => sigmaOneBoundedFamilyFormula
  | k + 1, p => “Q. ∃ A, !(sigmaOneLevyFamilyFormula k .sigma) A ∧
      ∃ B, !(sigmaOneLevyFamilyFormula k .pi) B ∧
      ∃ C, !boundedUnionFormula C A B ∧ !(sigmaOneLevyExtensionFormula p) Q C”

theorem sigmaOneLevyFamilyFormula_sigmaOne (k : ℕ) (p : LevyPolarity) :
    IsLevyFormula .sigma 1 (sigmaOneLevyFamilyFormula k p) := by
  induction k generalizing p with
  | zero => exact sigmaOneBoundedFamilyFormula_sigmaOne
  | succ k ih =>
    exact .exs (.and ((ih .sigma).subst _) (.exs (.and ((ih .pi).subst _)
      (.exs (.and (.bounded (boundedUnionFormula_bounded.subst _)) ((sigmaOneLevyExtensionFormula_sigmaOne p).subst _))))))

def sigmaOneLevyCodeFormula (p : LevyPolarity) (k : ℕ) : SetTheorySemisentence 2 :=
  “n φ. ∃ Q, !(sigmaOneLevyFamilyFormula k p) Q ∧ !boundedPairMemberFormula Q n φ”

def sigmaOneNonLevyCodeFormula (p : LevyPolarity) (k : ℕ) : SetTheorySemisentence 2 :=
  “n φ. ∃ Q, !(sigmaOneLevyFamilyFormula k p) Q ∧ ¬!boundedPairMemberFormula Q n φ”

def piOneLevyCodeFormula (p : LevyPolarity) (k : ℕ) : SetTheorySemisentence 2 :=
  ∼(sigmaOneNonLevyCodeFormula p k)

def piOneLevyFamilyFormula (k : ℕ) (p : LevyPolarity) : SetTheorySemisentence 1 :=
  “Q. ∀ R, !(sigmaOneLevyFamilyFormula k p) R → R = Q”

theorem piOneLevyFamilyFormula_piOne (k : ℕ) (p : LevyPolarity) :
    IsLevyFormula .pi 1 (piOneLevyFamilyFormula k p) :=
  .all (.or ((sigmaOneLevyFamilyFormula_sigmaOne k p).subst _).neg (.bounded (.rel _ _)))

theorem sigmaOneLevyCodeFormula_sigmaOne (p : LevyPolarity) (k : ℕ) :
    IsLevyFormula .sigma 1 (sigmaOneLevyCodeFormula p k) :=
  .exs (.and ((sigmaOneLevyFamilyFormula_sigmaOne k p).subst _) (.bounded (boundedPairMemberFormula_bounded.subst _)))

theorem sigmaOneNonLevyCodeFormula_sigmaOne (p : LevyPolarity) (k : ℕ) :
    IsLevyFormula .sigma 1 (sigmaOneNonLevyCodeFormula p k) :=
  .exs (.and ((sigmaOneLevyFamilyFormula_sigmaOne k p).subst _) (.bounded (boundedPairMemberFormula_bounded.subst _).neg))

theorem piOneLevyCodeFormula_piOne (p : LevyPolarity) (k : ℕ) :
    IsLevyFormula .pi 1 (piOneLevyCodeFormula p k) := (sigmaOneNonLevyCodeFormula_sigmaOne p k).neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneLevyFamilyFormula (k : ℕ) (p : LevyPolarity) (Q : V) :
    (sigmaOneLevyFamilyFormula k p).Evalb ![Q] ↔ Q = (levyFormulaFamily k p : V) := by
  induction k generalizing p Q with
  | zero => exact eval_sigmaOneBoundedFamilyFormula Q
  | succ k ih =>
    have hB : (levyFormulaFamily k .sigma : V) ∪ levyFormulaFamily k .pi ⊆ formulaFamily membershipLanguageCode ∅ := by
      intro q hq
      exact (mem_union_iff.mp hq).elim (levyFormulaFamily_subset k .sigma q) (levyFormulaFamily_subset k .pi q)
    simp [sigmaOneLevyFamilyFormula, ih, eval_sigmaOneLevyExtensionFormula p hB, levyFormulaFamily]

theorem eval_sigmaOneLevyCodeFormula (p : LevyPolarity) (k : ℕ) (n φ : V) :
    (sigmaOneLevyCodeFormula p k).Evalb ![n, φ] ↔ IsLevyFormulaCode p k n φ := by
  simp [sigmaOneLevyCodeFormula, eval_sigmaOneLevyFamilyFormula, IsLevyFormulaCode]

theorem eval_piOneLevyFamilyFormula (k : ℕ) (p : LevyPolarity) (Q : V) :
    (piOneLevyFamilyFormula k p).Evalb ![Q] ↔ Q = (levyFormulaFamily k p : V) := by
  simp [piOneLevyFamilyFormula, eval_sigmaOneLevyFamilyFormula, eq_comm]

theorem eval_sigmaOneNonLevyCodeFormula (p : LevyPolarity) (k : ℕ) (n φ : V) :
    (sigmaOneNonLevyCodeFormula p k).Evalb ![n, φ] ↔ ¬IsLevyFormulaCode p k n φ := by
  simp [sigmaOneNonLevyCodeFormula, eval_sigmaOneLevyFamilyFormula, IsLevyFormulaCode]

theorem eval_piOneLevyCodeFormula (p : LevyPolarity) (k : ℕ) (n φ : V) :
    (piOneLevyCodeFormula p k).Evalb ![n, φ] ↔ IsLevyFormulaCode p k n φ := by
  simp [piOneLevyCodeFormula, eval_sigmaOneNonLevyCodeFormula]

instance sigmaOneLevyFamilyFormula_defined (k : ℕ) (p : LevyPolarity) :
    ℒₛₑₜ-function₀[V] (levyFormulaFamily k p : V) via sigmaOneLevyFamilyFormula k p :=
  ⟨fun (v : Fin 1 → V) ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change (sigmaOneLevyFamilyFormula k p).Evalb v ↔ v 0 = levyFormulaFamily k p
    rw [← hv]
    exact eval_sigmaOneLevyFamilyFormula k p (v 0)⟩

instance sigmaOneLevyCodeFormula_defined (p : LevyPolarity) (k : ℕ) :
    ℒₛₑₜ-relation[V] (IsLevyFormulaCode p k) via sigmaOneLevyCodeFormula p k :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    change (sigmaOneLevyCodeFormula p k).Evalb v ↔ IsLevyFormulaCode p k (v 0) (v 1)
    rw [← hv]
    exact eval_sigmaOneLevyCodeFormula p k (v 0) (v 1)⟩

instance piOneLevyFamilyFormula_defined (k : ℕ) (p : LevyPolarity) :
    ℒₛₑₜ-function₀[V] (levyFormulaFamily k p : V) via piOneLevyFamilyFormula k p :=
  ⟨fun (v : Fin 1 → V) ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change (piOneLevyFamilyFormula k p).Evalb v ↔ v 0 = levyFormulaFamily k p
    rw [← hv]
    exact eval_piOneLevyFamilyFormula k p (v 0)⟩

instance piOneLevyCodeFormula_defined (p : LevyPolarity) (k : ℕ) :
    ℒₛₑₜ-relation[V] (IsLevyFormulaCode p k) via piOneLevyCodeFormula p k :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    change (piOneLevyCodeFormula p k).Evalb v ↔ IsLevyFormulaCode p k (v 0) (v 1)
    rw [← hv]
    exact eval_piOneLevyCodeFormula p k (v 0) (v 1)⟩

end ZFVP
