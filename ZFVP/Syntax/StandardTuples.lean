import ZFVP.Syntax.Assignments
import ZFVP.SetTheory.StandardNaturals

/-! External finite tuples represented by internal function graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def standardTuple : {n : ℕ} → (Fin n → V) → V
  | 0, _ => ∅
  | n + 1, v => assignmentPrepend (n : V) (standardTuple (fun i ↦ v i.succ)) (v 0)

theorem standardTuple_mem_function {n : ℕ} {A : V} (v : Fin n → V)
    (hv : ∀ i, v i ∈ A) : standardTuple v ∈ A ^ (n : V) := by
  induction n with
  | zero => simp [standardTuple, mem_function_iff, zero_def]
  | succ n ih =>
    simpa [standardTuple, num_succ_def] using
      assignmentPrepend_mem_function (by simp) (ih (fun i ↦ v i.succ) (fun i ↦ hv i.succ)) (hv 0)

instance standardTuple_isFunction {n : ℕ} (v : Fin n → V) : IsFunction (standardTuple v) := by
  induction n with
  | zero => simp only [standardTuple]; infer_instance
  | succ n ih => simp only [standardTuple]; infer_instance

@[simp] theorem domain_standardTuple {n : ℕ} (v : Fin n → V) :
    domain (standardTuple v) = (n : V) := by
  cases n <;> simp [standardTuple, num_succ_def, zero_def]

@[simp] theorem value_standardTuple {n : ℕ} (v : Fin n → V) (i : Fin n) :
    (standardTuple v) ‘ (i.val : V) = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact assignmentPrepend_zero (by simp) _ _
    · change (assignmentPrepend (n : V) (standardTuple (fun i ↦ v i.succ)) (v 0)) ‘
        ((j.val + 1 : ℕ) : V) = v j.succ
      rw [num_succ_def, assignmentPrepend_succ (by simp) (natCast_mem_of_lt j.isLt)]
      exact ih (fun j ↦ v j.succ) j

theorem standardTuple_injective {n : ℕ} :
    Function.Injective (standardTuple (V := V) (n := n)) := by
  intro v w h
  funext i
  have := congrArg (fun f : V ↦ f ‘ (i.val : V)) h
  simpa only [value_standardTuple] using this

theorem mem_standardTuple_iff {n : ℕ} (v : Fin n → V) (p : V) :
    p ∈ standardTuple v ↔ ∃ i : Fin n, p = ⟨(i.val : V), v i⟩ₖ := by
  constructor
  · intro hp
    obtain ⟨x, hx, y, _, rfl⟩ := mem_prod_iff.mp
      (subset_prod_of_mem_function (IsFunction.mem_function (standardTuple v)) _ hp)
    rw [domain_standardTuple, mem_natCast_iff] at hx
    obtain ⟨i, rfl⟩ := hx
    have hy := value_eq_of_kpair_mem hp
    rw [value_standardTuple] at hy
    exact ⟨i, by rw [hy]⟩
  · rintro ⟨i, rfl⟩
    apply kpair_mem_iff_value.mpr
    exact ⟨by rw [domain_standardTuple]; exact natCast_mem_of_lt i.isLt,
      value_standardTuple v i⟩

theorem compose_standardTuple {n : ℕ} (v : Fin n → V) (g : V) [IsFunction g]
    (hg : ∀ i, v i ∈ domain g) :
    compose (standardTuple v) g = standardTuple (fun i ↦ g ‘ (v i)) := by
  apply mem_ext
  intro p
  rw [mem_compose_iff, mem_standardTuple_iff]
  constructor
  · rintro ⟨x, y, z, hxy, hyz, rfl⟩
    obtain ⟨i, hi⟩ := (mem_standardTuple_iff v _).mp hxy
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hi
    exact ⟨i, by rw [value_eq_of_kpair_mem hyz]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(i.val : V), v i, g ‘ (v i),
      (mem_standardTuple_iff v _).mpr ⟨i, rfl⟩, kpair_value_mem (hg i), rfl⟩

end ZFVP
