import ZFVP.Syntax.PrefixTuples
import ZFVP.Syntax.UniformAssignments

/-! Shared formulas for standard prefixes with an arbitrary internal parameter tail. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def prefixSizeFormula : ℕ → SetTheorySemisentence 2
  | 0 => f“y n. y = n”
  | m + 1 => f“y n. y = !succ.dfn (!(prefixSizeFormula m) n)”

def skipIndicesFormula (m : ℕ) : SetTheorySemisentence 2 :=
  f“B n. ∀ p, p ∈ B ↔ ∃ i ∈ n, p = !kpair.dfn i (!(prefixSizeFormula m) i)”

def prependTupleFormula : {m : ℕ} → (Fin m → SetTheorySemisentence 1) → SetTheorySemisentence 3
  | 0, _ => f“B n b. B = b”
  | m + 1, q => f“B n b. B = !assignmentPrependFormula (!(prefixSizeFormula m) n)
      (!(prependTupleFormula (fun i ↦ q i.succ)) n b) (!(q 0))”

def standardTupleConstantFormula : {m : ℕ} → (Fin m → SetTheorySemisentence 1) → SetTheorySemisentence 1
  | 0, _ => isEmpty
  | m + 1, q => f“B. B = !assignmentPrependFormula (!(numeralFormula m))
      (!(standardTupleConstantFormula (fun i ↦ q i.succ))) (!(q 0))”

def prefixRenamingFormula {a m : ℕ} (r : Fin a → Fin m) : SetTheorySemisentence 2 :=
  f“B n. B = !(prependTupleFormula (fun i ↦ numeralFormula (r i).val)) n (!(skipIndicesFormula m) n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance prefixSizeFormula_defined (m : ℕ) :
    ℒₛₑₜ-function₁[V] (prefixSize m) via prefixSizeFormula m := by
  induction m with
  | zero => exact ⟨fun v ↦ by simp [prefixSizeFormula, prefixSize]⟩
  | succ m ih => exact ⟨fun v ↦ by simp [prefixSizeFormula, prefixSize]⟩

instance skipIndicesFormula_defined (m : ℕ) :
    ℒₛₑₜ-function₁[V] (skipIndices m) via skipIndicesFormula m :=
  ⟨fun v ↦ by
    change (skipIndicesFormula m).Evalb v ↔ v 0 = skipIndices m (v 1)
    rw [mem_ext_iff]
    simp [skipIndicesFormula, skipIndices, mem_definableGraph_iff]⟩

instance prependTupleFormula_defined {m : ℕ} (c : Fin m → V)
    (q : Fin m → SetTheorySemisentence 1) [∀ i, ℒₛₑₜ-function₀[V] (c i) via q i] :
    ℒₛₑₜ-function₂[V] (fun n b ↦ prependTuple n b c) via prependTupleFormula q := by
  induction m with
  | zero => exact ⟨fun v ↦ by simp [prependTupleFormula, prependTuple]⟩
  | succ m ih =>
    have := ih (fun i ↦ c i.succ) (fun i ↦ q i.succ)
    exact ⟨fun v ↦ by simp [prependTupleFormula, prependTuple]⟩

instance standardTupleConstantFormula_defined {m : ℕ} (c : Fin m → V)
    (q : Fin m → SetTheorySemisentence 1) [∀ i, ℒₛₑₜ-function₀[V] (c i) via q i] :
    ℒₛₑₜ-function₀[V] (standardTuple c) via standardTupleConstantFormula q := by
  induction m with
  | zero => exact ⟨fun v ↦ by simp [standardTupleConstantFormula, standardTuple, isEmpty_iff_eq_empty]⟩
  | succ m ih =>
    have := ih (fun i ↦ c i.succ) (fun i ↦ q i.succ)
    exact ⟨fun v ↦ by simp [standardTupleConstantFormula, standardTuple]⟩

instance prefixRenamingFormula_defined {a m : ℕ} (r : Fin a → Fin m) :
    ℒₛₑₜ-function₁[V] (prefixRenaming r) via prefixRenamingFormula r :=
  ⟨fun v ↦ by simp [prefixRenamingFormula, prefixRenaming]⟩

end ZFVP
