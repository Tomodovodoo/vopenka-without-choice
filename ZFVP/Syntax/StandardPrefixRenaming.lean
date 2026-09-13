import ZFVP.Syntax.MembershipEncodingRewriting
import ZFVP.Syntax.PrefixTuples

/-! Standard parameter tuples and the prefix renamings used by the schema compiler. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def prefixVector {α : Type*} {k : ℕ} : {m : ℕ} → (Fin m → α) → (Fin k → α) → Fin (k + m) → α
  | 0, _, b => b
  | _ + 1, v, b => Fin.cons (v 0) (prefixVector (fun i ↦ v i.succ) b)

theorem prefixVector_front {α : Type*} {k m : ℕ} (v : Fin m → α) (b : Fin k → α) (i : Fin m) :
    prefixVector v b (Fin.castLE (Nat.le_add_left m k) i) = v i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases rfl (fun j ↦ ?_) i
    exact ih (fun i ↦ v i.succ) j

theorem prefixVector_tail {α : Type*} {k m : ℕ} (v : Fin m → α) (b : Fin k → α) (i : Fin k) :
    prefixVector v b (Fin.addNat i m) = b i := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih (fun i ↦ v i.succ)

theorem prefixVector_map {α β : Type*} {k m : ℕ} (f : α → β) (v : Fin m → α) (b : Fin k → α) :
    f ∘ prefixVector v b = prefixVector (f ∘ v) (f ∘ b) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    refine Fin.cases rfl (fun j ↦ ?_) i
    exact congrFun (ih (fun i ↦ v i.succ)) j

def prefixIndexMap {a m : ℕ} (k : ℕ) (r : Fin a → Fin m) : Fin (k + a) → Fin (k + m) :=
  prefixVector (fun i ↦ Fin.castLE (Nat.le_add_left m k) (r i)) (fun i ↦ Fin.addNat i m)

theorem prefixVector_comp_prefixIndexMap {α : Type*} {a m k : ℕ}
    (r : Fin a → Fin m) (v : Fin m → α) (b : Fin k → α) :
    prefixVector v b ∘ prefixIndexMap k r = prefixVector (v ∘ r) b := by
  rw [prefixIndexMap, prefixVector_map]
  congr 1
  · funext i
    exact prefixVector_front v b (r i)
  · funext i
    exact prefixVector_tail v b i

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem prefixSize_natCast (m k : ℕ) : prefixSize m (k : V) = ((k + m : ℕ) : V) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [prefixSize, ih, Nat.add_succ, num_succ_def]

theorem standardTuple_prefixVector {k m : ℕ} (v : Fin m → V) (b : Fin k → V) :
    standardTuple (prefixVector v b) = prependTuple (k : V) (standardTuple b) v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change assignmentPrepend (((k + m : ℕ) : V)) (standardTuple (prefixVector (fun i ↦ v i.succ) b)) (v 0) = _
    rw [ih]
    simp only [prependTuple, prefixSize_natCast]

theorem skipIndices_natCast (m k : ℕ) :
    skipIndices m (k : V) = standardTuple (fun i : Fin k ↦ ((i.val + m : ℕ) : V)) := by
  have hs : skipIndices m (k : V) ∈ (((k + m : ℕ) : V)) ^ (k : V) := by
    simpa only [prefixSize_natCast] using skipIndices_function (V := V) m (n := (k : V)) (by simp)
  apply function_eq_of_values hs (standardTuple_mem_function _ (fun i ↦ natCast_mem_of_lt (by omega)))
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_natCast_iff x k).mp hx
  rw [show (skipIndices m (k : V)) ‘ (i.val : V) = prefixSize m (i.val : V) from
    value_definableGraph _ _ _ (natCast_mem_of_lt i.isLt), prefixSize_natCast, value_standardTuple]

theorem prefixRenaming_natCast {a m : ℕ} (k : ℕ) (r : Fin a → Fin m) :
    prefixRenaming r (k : V) = standardTuple (fun i ↦ ((prefixIndexMap k r i).val : V)) := by
  have he := prefixVector_map (fun i : Fin (k + m) ↦ (i.val : V))
    (fun i : Fin a ↦ Fin.castLE (Nat.le_add_left m k) (r i)) (fun i : Fin k ↦ Fin.addNat i m)
  change prependTuple (k : V) (skipIndices m (k : V)) (fun i ↦ ((r i).val : V)) = _
  rw [skipIndices_natCast]
  have hv : (fun i ↦ ((prefixIndexMap k r i).val : V)) =
      prefixVector (fun i ↦ ((r i).val : V)) (fun i : Fin k ↦ ((i.val + m : ℕ) : V)) := he
  rw [hv, standardTuple_prefixVector]

end ZFVP
