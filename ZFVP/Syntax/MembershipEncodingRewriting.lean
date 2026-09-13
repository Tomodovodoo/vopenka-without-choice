import ZFVP.Syntax.FoundationFormulaSubstitution
import ZFVP.Syntax.MembershipRenaming
import ZFVP.Syntax.NegationSemantics
import ZFVP.Syntax.FiniteVariableClosure
import ZFVP.ModelTheory.CodedSequentQuantifiers

/-! Standard formula rewriting agrees syntactically with the internal code operations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem encodeMembershipFormula_and {n : ℕ} (φ ψ : SetTheorySemisentence n) :
    encodeMembershipFormula (V := V) (φ ⋏ ψ) = andCode (encodeMembershipFormula φ) (encodeMembershipFormula ψ) := rfl

@[simp] theorem encodeMembershipFormula_or {n : ℕ} (φ ψ : SetTheorySemisentence n) :
    encodeMembershipFormula (V := V) (φ ⋎ ψ) = orCode (encodeMembershipFormula φ) (encodeMembershipFormula ψ) := rfl

@[simp] theorem encodeMembershipFormula_all {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    encodeMembershipFormula (V := V) (∀¹ φ) = allCode (encodeMembershipFormula φ) := rfl

@[simp] theorem encodeMembershipFormula_exs {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    encodeMembershipFormula (V := V) (∃¹ φ) = existsCode (encodeMembershipFormula φ) := rfl

theorem encodeMembershipFormula_neg {n : ℕ} (φ : SetTheorySemisentence n) :
    encodeMembershipFormula (V := V) (∼φ) =
      negateFormula membershipLanguageCode ∅ (n : V) (encodeMembershipFormula φ) :=
  encodeSemiformula_neg (V := V) (Λ := ℒₛₑₜ) (ξ := Empty)
    (L := membershipLanguageCode) (Γ := ∅) membershipLanguageCode_valid
    (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol Empty.elim
    (fun k f ↦ membershipFunctionSymbol_valid (k := k) f) (fun _ r ↦ membershipSymbol_valid r)
    (fun x ↦ Empty.elim x) φ

theorem renameMembershipFormula_encode {n m : ℕ} {r : V}
    (hr : r ∈ (m : V) ^ (n : V)) (f : Fin n → Fin m)
    (he : ∀ i : Fin n, r ‘ (i.val : V) = ((f i).val : V))
    (σ : Rew ℒₛₑₜ Empty n Empty m) (hσ : ∀ i, σ (.bvar i) = .bvar (f i))
    (φ : SetTheorySemisentence n) :
    renameMembershipFormula (n : V) (m : V) r (encodeMembershipFormula φ) =
      encodeMembershipFormula (σ ▹ φ) := by
  let F : ∀ {k}, (ℒₛₑₜ).Func k → V := fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)
  have hF := fun k f ↦ membershipFunctionSymbol_valid (V := V) (k := k) f
  have hR := fun k r ↦ membershipSymbol_valid (V := V) (k := k) r
  apply encodeSemiformula_rew (V := V) (Λ := ℒₛₑₜ) (ξ := Empty) (η := Empty)
    (L := membershipLanguageCode) (Γ := ∅) (Δ := ∅)
    (B := compose r (boundVariableAssignment (m : V))) (E := ∅)
    membershipLanguageCode_valid F membershipSymbol Empty.elim Empty.elim
    hF hR (fun x ↦ Empty.elim x) (fun x ↦ Empty.elim x) σ
    (compose_function hr (boundVariableAssignment_mem (by simp)))
    (by simp [mem_function_iff]) ?_ (fun x ↦ Empty.elim x) φ
  intro i
  rw [value_compose_of_mem_function hr (boundVariableAssignment_mem (by simp)) (natCast_mem_of_lt i.isLt),
    he i, boundVariableAssignment_value (natCast_mem_of_lt (f i).isLt), hσ i]
  rfl

theorem encodeMembershipFormula_bShift {n : ℕ} (φ : SetTheorySemisentence n) :
    encodeMembershipFormula (V := V) (Rew.bShift ▹ φ) =
      renameMembershipFormula (n : V) (succ (n : V)) (successorIndices (n : V)) (encodeMembershipFormula φ) := by
  have hr : successorIndices (n : V) ∈ ((n + 1 : ℕ) : V) ^ (n : V) := by
    simpa [num_succ_def] using successorIndices_function (V := V) (n := (n : V)) (by simp)
  have he (i : Fin n) : (successorIndices (n : V)) ‘ (i.val : V) = (i.succ.val : V) := by
    rw [show (successorIndices (n : V)) ‘ (i.val : V) = succ (i.val : V) from
      value_definableGraph _ _ _ (natCast_mem_of_lt i.isLt)]
    simp [num_succ_def]
  simpa [num_succ_def] using (renameMembershipFormula_encode hr Fin.succ he Rew.bShift (fun _ ↦ rfl) φ).symm

theorem encodeMembershipFormula_instantiate {n : ℕ} (i : Fin n) (φ : SetTheorySemisentence (n + 1)) :
    encodeMembershipFormula (V := V) (instantiateBoundRew i ▹ φ) =
      instantiateMembershipFormula (n : V) (i.val : V) (encodeMembershipFormula φ) := by
  have hr : assignmentPrepend (n : V) (identity (n : V)) (i.val : V) ∈ (n : V) ^ ((n + 1 : ℕ) : V) := by
    simpa [num_succ_def] using assignmentPrepend_mem_function (by simp)
      (identity_mem_function (n : V)) (natCast_mem_of_lt i.isLt)
  have he (j : Fin (n + 1)) :
      (assignmentPrepend (n : V) (identity (n : V)) (i.val : V)) ‘ (j.val : V) =
        (((Fin.cons i id : Fin (n + 1) → Fin n) j).val : V) := by
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · exact assignmentPrepend_zero (by simp) _ _
    · rw [show (k.succ.val : V) = succ (k.val : V) from num_succ_def _,
        assignmentPrepend_succ (by simp) (natCast_mem_of_lt k.isLt)]
      exact value_eq_of_kpair_mem (kpair_mem_identity_iff.mpr ⟨natCast_mem_of_lt k.isLt, rfl⟩)
  have hσ (j : Fin (n + 1)) : instantiateBoundRew i (.bvar j) =
      .bvar ((Fin.cons i id : Fin (n + 1) → Fin n) j) := by
    refine Fin.cases rfl (fun _ ↦ rfl) j
  simpa [instantiateMembershipFormula, num_succ_def] using
    (renameMembershipFormula_encode hr (Fin.cons i id) he (instantiateBoundRew i) hσ φ).symm

end ZFVP
