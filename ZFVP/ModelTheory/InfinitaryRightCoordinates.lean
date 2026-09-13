import ZFVP.ModelTheory.InfinitaryLargeConditionFreezing

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula

/-- Keep the last coordinates fixed when new variables are inserted at the front. -/
def rightEmbed {n m : ℕ} (h : n ≤ m) (i : Fin n) : Fin m :=
  ⟨i.val + (m - n), by omega⟩

@[simp] theorem rightEmbed_refl {n} (i : Fin n) : rightEmbed (le_refl n) i = i := by
  apply Fin.ext
  simp [rightEmbed]

theorem rightEmbed_injective {n m} (h : n ≤ m) : Function.Injective (rightEmbed h) := by
  intro i j he
  apply Fin.ext
  have := congrArg Fin.val he
  simp only [rightEmbed] at this
  omega

@[simp] theorem rightEmbed_trans {n m k} (h : n ≤ m) (g : m ≤ k) (i : Fin n) :
    rightEmbed g (rightEmbed h i) = rightEmbed (h.trans g) i := by
  apply Fin.ext
  simp only [rightEmbed]
  omega

@[simp] theorem rightEmbed_succ {n} (i : Fin n) :
    rightEmbed (Nat.le_succ n) i = i.succ := by
  apply Fin.ext
  simp [rightEmbed]

@[simp] theorem rightEmbed_last {n m} (h : 1 + n ≤ 1 + m) :
    rightEmbed h (lastCoordinate n) = lastCoordinate m := by
  apply Fin.ext
  simp only [rightEmbed, lastCoordinate_val]
  omega

noncomputable def extendRight {M : Type*} [Nonempty M] {n m} (h : n ≤ m)
    (b : Fin n → M) (j : Fin m) : M :=
  if hj : ∃ i, rightEmbed h i = j then b hj.choose else Classical.choice inferInstance

@[simp] theorem extendRight_embed {M : Type*} [Nonempty M] {n m} (h : n ≤ m)
    (b : Fin n → M) (i : Fin n) : extendRight h b (rightEmbed h i) = b i := by
  classical
  unfold extendRight
  split_ifs with hj
  · congr 1
    exact rightEmbed_injective h hj.choose_spec
  · exact (hj ⟨i, rfl⟩).elim

@[simp] theorem extendRight_comp {M : Type*} [Nonempty M] {n m} (h : n ≤ m)
    (b : Fin n → M) : extendRight h b ∘ rightEmbed h = b := by
  funext i
  exact extendRight_embed h b i

end Formula
end ZFVP.Infinitary
