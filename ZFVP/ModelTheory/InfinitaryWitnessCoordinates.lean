import ZFVP.ModelTheory.InfinitaryProjectionAssignments

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula
variable {M : Type*}

def tailIndex : (k : ℕ) → {n : ℕ} → Fin n → Fin (n + k)
  | 0, _, i => i
  | k + 1, _, i => (tailIndex k i).succ

theorem tailIndex_val (k : ℕ) {n} (i : Fin n) : (tailIndex k i).val = i.val + k := by
  induction k with
  | zero => rfl
  | succ k ih => change (tailIndex k i).val + 1 = _; omega

theorem dropFirst_apply (k : ℕ) {n} (e : Fin (n + k) → M) (i : Fin n) :
    dropFirst k e i = e (tailIndex k i) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (fun i ↦ e i.succ)

end Formula
namespace WitnessCoordinates

def embed (k : ℕ) (i : Fin (1 + k)) : Fin (2 + k) :=
  ⟨if i.val < k then i.val else i.val + 1, by split_ifs <;> omega⟩

def witness (k : ℕ) : Fin (2 + k) := ⟨k, by omega⟩

theorem embed_injective (k : ℕ) : Function.Injective (embed k) := by
  intro i j he
  have hv := congrArg Fin.val he
  simp only [embed] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem witness_not_range (k : ℕ) (i : Fin (1 + k)) : embed k i ≠ witness k := by
  intro he
  have hv := congrArg Fin.val he
  simp only [embed, witness] at hv
  split_ifs at hv <;> omega

theorem tail_zero (k : ℕ) : Formula.tailIndex k (0 : Fin 2) = witness k := by
  apply Fin.ext
  simp [Formula.tailIndex_val, witness]

theorem tail_one (k : ℕ) : Formula.tailIndex k (1 : Fin 2) = embed k (Formula.lastCoordinate k) := by
  apply Fin.ext
  simp [Formula.tailIndex_val, embed, Formula.lastCoordinate_val]
  omega

noncomputable def insert {M : Type*} (k : ℕ) (e : Fin (1 + k) → M) (y : M) : Fin (2 + k) → M :=
  fun j ↦ if h : ∃ i, embed k i = j then e h.choose else y

theorem insert_embed {M : Type*} (k : ℕ) (e : Fin (1 + k) → M) (y : M) (i : Fin (1 + k)) :
    insert k e y (embed k i) = e i := by
  have h : ∃ a, embed k a = embed k i := ⟨i, rfl⟩
  simp only [insert, dif_pos h]
  rw [embed_injective k h.choose_spec]

theorem insert_witness {M : Type*} (k : ℕ) (e : Fin (1 + k) → M) (y : M) :
    insert k e y (witness k) = y := by
  have h : ¬∃ i, embed k i = witness k := fun ⟨i, hi⟩ ↦ witness_not_range k i hi
  simp only [insert, dif_neg h]

theorem insert_comp_embed {M : Type*} (k : ℕ) (e : Fin (1 + k) → M) (y : M) :
    insert k e y ∘ embed k = e := funext (insert_embed k e y)

theorem drop_insert {M : Type*} (k : ℕ) (e : Fin (1 + k) → M) (y : M) :
    Formula.dropFirst k (insert k e y) = (y :> e (Formula.lastCoordinate k) :> Fin.elim0) := by
  funext i
  rw [Formula.dropFirst_apply]
  cases i using Fin.cases with
  | zero => rw [tail_zero, insert_witness]; rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rw [show (0 : Fin 1).succ = (1 : Fin 2) from rfl, tail_one, insert_embed]; rfl
    | succ i => exact i.elim0

end WitnessCoordinates
end ZFVP.Infinitary
