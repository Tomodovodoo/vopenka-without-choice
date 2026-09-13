import ZFVP.ModelTheory.SchmerlGeneralizedInfinitarySemantics
import ZFVP.ModelTheory.SchmerlInfinitaryClassSentence

/-! The definability and weak-coloring clauses contain no Q. Their ordinary
semantics is therefore available when the rest of the sentence uses internal Q. -/

set_option autoImplicit false

namespace ZFVP.Infinitary.Formula

open LO LO.FirstOrder

variable {L : Language}

def QFree : {n : ℕ} → Formula L n → Prop
  | _, .fo _ => True
  | _, .neg φ => QFree φ
  | _, .conj φ => ∀ i, QFree (φ i)
  | _, .exs φ => QFree φ
  | _, .q _ => False

@[simp] theorem qFree_fo {n} (φ : Semisentence L n) : QFree (.fo φ) := True.intro
@[simp] theorem qFree_neg {n} (φ : Formula L n) : QFree (.neg φ) ↔ QFree φ := Iff.rfl
@[simp] theorem qFree_conj {n} (φ : ℕ → Formula L n) : QFree (.conj φ) ↔ ∀ i, QFree (φ i) := Iff.rfl
@[simp] theorem qFree_exs {n} (φ : Formula L (n + 1)) : QFree (.exs φ) ↔ QFree φ := Iff.rfl
@[simp] theorem qFree_disj {n} (φ : ℕ → Formula L n) : QFree (disj φ) ↔ ∀ i, QFree (φ i) := Iff.rfl
@[simp] theorem qFree_all {n} (φ : Formula L (n + 1)) : QFree (all φ) ↔ QFree φ := Iff.rfl

@[simp] theorem qFree_and {n} (φ ψ : Formula L n) : QFree (and φ ψ) ↔ QFree φ ∧ QFree ψ := by
  simp only [and, qFree_conj]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨hφ, hψ⟩ i
    split_ifs <;> assumption

@[simp] theorem qFree_or {n} (φ ψ : Formula L n) : QFree (or φ ψ) ↔ QFree φ ∧ QFree ψ := by simp [or]
@[simp] theorem qFree_imp {n} (φ ψ : Formula L n) : QFree (imp φ ψ) ↔ QFree φ ∧ QFree ψ := by simp [imp]
@[simp] theorem qFree_iff {n} (φ ψ : Formula L n) : QFree (iff φ ψ) ↔ QFree φ ∧ QFree ψ := by
  simp [iff]
  tauto

@[simp] theorem qFree_rename {n m} (ρ : Fin n → Fin m) (φ : Formula L n) :
    QFree (rename ρ φ) ↔ QFree φ := by
  induction φ generalizing m with
  | fo φ => rfl
  | neg φ ih => exact ih ρ
  | conj φ ih => exact forall_congr' fun i ↦ ih i ρ
  | exs φ ih => exact ih (liftRenaming ρ)
  | q φ _ => rfl

@[simp] theorem qFree_swapFirstTwo {n} (φ : Formula L (n + 2)) :
    QFree (swapFirstTwo φ) ↔ QFree φ := qFree_rename _ _

theorem QFree.evalWithQ_iff {M : Type*} [Structure L M] {n} {φ : Formula L n}
    (h : QFree φ) (Q : Set M → Prop) (b : Fin n → M) : EvalWithQ Q φ b ↔ Eval φ b := by
  induction φ with
  | fo _ => rfl
  | neg φ ih => exact not_congr (ih h b)
  | conj φ ih => exact forall_congr' fun i ↦ ih i (h i) b
  | exs φ ih => exact exists_congr fun x ↦ ih h (x :> b)
  | q _ _ => exact h.elim

end ZFVP.Infinitary.Formula

namespace ZFVP.Schmerl

open LO LO.FirstOrder
open ZFVP.Infinitary (Formula)

variable {L : Language}

@[simp] theorem qFree_existsTuple {n : ℕ} (k : ℕ) (φ : Formula L (n + k)) :
    Formula.QFree (existsTuple k φ) ↔ Formula.QFree φ := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (.exs φ)

@[simp] theorem qFree_selectedRankNodes (D : Formula L 1) (J : Formula L 2) :
    Formula.QFree (selectedRankNodes D J) ↔ Formula.QFree D ∧ Formula.QFree J := by simp [selectedRankNodes]

@[simp] theorem qFree_equalityOfColors (F : Formula L 2) :
    Formula.QFree (equalityOfColors F) ↔ Formula.QFree F := by simp [equalityOfColors]

@[simp] theorem qFree_nodeRankAbove (J r : Formula L 2) :
    Formula.QFree (nodeRankAbove J r) ↔ Formula.QFree J ∧ Formula.QFree r := by simp [nodeRankAbove]

theorem qFree_canonicalBranchCandidate (N D : Formula L 1) (r E : Formula L 2)
    (hN : Formula.QFree N) (hD : Formula.QFree D) (hr : Formula.QFree r) (hE : Formula.QFree E) :
    Formula.QFree (canonicalBranchCandidate N D r E) := by
  simp [canonicalBranchCandidate, hN, hD, hr, hE]

theorem qFree_branchDefinabilityClause {L₀ : Language.{0}} [L₀.Encodable]
    (η : L₀ →ᵥ L) (N D O : Formula L 1) (r E H : Formula L 2)
    (hN : Formula.QFree N) (hD : Formula.QFree D) (hO : Formula.QFree O)
    (hr : Formula.QFree r) (hE : Formula.QFree E) (hH : Formula.QFree H) :
    Formula.QFree (branchDefinabilityClause η N D O r E H) := by
  have hψ := qFree_canonicalBranchCandidate N D r E hN hD hr hE
  simp [branchDefinabilityClause, candidateCofinalityTest, originalDefinabilityClause,
    originalDefinitionInstance, hN, hD, hO, hH, hψ]

theorem qFree_weakSpecializationClause (N D : Formula L 1) (r E : Formula L 2)
    (hN : Formula.QFree N) (hD : Formula.QFree D) (hr : Formula.QFree r) (hE : Formula.QFree E) :
    Formula.QFree (weakSpecializationClause N D r E) := by
  simp [weakSpecializationClause, hN, hD, hr, hE]

@[simp] theorem qFree_classOriginal {n : ℕ} (φ : SetTheorySemisentence n) :
    Formula.QFree (classOriginal φ) := True.intro

@[simp] theorem qFree_classSelected : Formula.QFree classSelected := True.intro
@[simp] theorem qFree_classColor : Formula.QFree classColor := True.intro

theorem qFree_classColorTotal : Formula.QFree classColorTotal := by simp [classColorTotal]

end ZFVP.Schmerl
