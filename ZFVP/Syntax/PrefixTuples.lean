import ZFVP.Syntax.MembershipSwap

/-! A standard finite prefix attached to an arbitrary internal finite tuple. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def prefixSize : ℕ → V → V
  | 0, n => n
  | m + 1, n => succ (prefixSize m n)

instance prefixSize_definable (m : ℕ) : ℒₛₑₜ-function₁[V] (prefixSize m) := by
  induction m with
  | zero => change ℒₛₑₜ-function₁[V] (fun n ↦ n); definability
  | succ m ih => change ℒₛₑₜ-function₁[V] (fun n ↦ succ (prefixSize m n)); definability

theorem prefixSize_natural (m : ℕ) {n : V} (hn : n ∈ (ω : V)) :
    prefixSize m n ∈ (ω : V) := by
  induction m with
  | zero => exact hn
  | succ m ih => exact ω_succ_closed ih

theorem prefixSize_mem_of_mem (m : ℕ) {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) :
    prefixSize m i ∈ prefixSize m n := by
  induction m with
  | zero => exact hi
  | succ m ih => exact succ_mem_succ_of_natural_mem (prefixSize_natural m hn) ih

theorem natCast_mem_prefixSize {m : ℕ} {n : V} (hn : n ∈ (ω : V)) (i : Fin m) :
    (i.val : V) ∈ prefixSize m n := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact zero_mem_succ_natural (prefixSize_natural m hn)
    · change ((j.val + 1 : ℕ) : V) ∈ succ (prefixSize m n)
      rw [num_succ_def]
      exact succ_mem_succ_of_natural_mem (prefixSize_natural m hn) (ih j)

noncomputable def prependTuple (n b : V) : {m : ℕ} → (Fin m → V) → V
  | 0, _ => b
  | m + 1, v => assignmentPrepend (prefixSize m n) (prependTuple n b (fun i ↦ v i.succ)) (v 0)

theorem prependTuple_function {m : ℕ} {n b A : V} (hn : n ∈ (ω : V))
    (hb : b ∈ A ^ n) (v : Fin m → V) (hv : ∀ i, v i ∈ A) :
    prependTuple n b v ∈ A ^ prefixSize m n := by
  induction m with
  | zero => exact hb
  | succ m ih =>
    exact assignmentPrepend_mem_function (prefixSize_natural m hn)
      (ih (fun i ↦ v i.succ) (fun i ↦ hv i.succ)) (hv 0)

theorem prependTuple_value_front {m : ℕ} {n : V} (hn : n ∈ (ω : V))
    (b : V) (v : Fin m → V) (i : Fin m) :
    (prependTuple n b v) ‘ (i.val : V) = v i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact assignmentPrepend_zero (prefixSize_natural m hn) _ _
    · change (assignmentPrepend (prefixSize m n) (prependTuple n b (fun i ↦ v i.succ)) (v 0)) ‘
        ((j.val + 1 : ℕ) : V) = v j.succ
      rw [num_succ_def, assignmentPrepend_succ (prefixSize_natural m hn) (natCast_mem_prefixSize hn j)]
      exact ih (fun i ↦ v i.succ) j

theorem prependTuple_value_tail {m : ℕ} {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (b : V) (v : Fin m → V) : (prependTuple n b v) ‘ (prefixSize m i) = b ‘ i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [prependTuple, prefixSize]
    rw [assignmentPrepend_succ (prefixSize_natural m hn) (prefixSize_mem_of_mem m hn hi)]
    exact ih (fun j ↦ v j.succ)

noncomputable def skipIndices (m : ℕ) (n : V) : V :=
  definableGraph n (prefixSize m) (by definability)

instance skipIndices_definable (m : ℕ) : ℒₛₑₜ-function₁[V] (skipIndices m) := by
  unfold skipIndices
  definability

theorem skipIndices_function (m : ℕ) {n : V} (hn : n ∈ (ω : V)) :
    skipIndices m n ∈ prefixSize m n ^ n :=
  definableGraph_mem_function_of_mapsTo _ _ _ (by definability) (fun _ hi ↦ prefixSize_mem_of_mem m hn hi)

theorem skipIndices_compose_prependTuple {m : ℕ} {n b A : V} (hn : n ∈ (ω : V))
    (hb : b ∈ A ^ n) (v : Fin m → V) (hv : ∀ i, v i ∈ A) :
    compose (skipIndices m n) (prependTuple n b v) = b := by
  have hr := skipIndices_function m hn
  have hp := prependTuple_function hn hb v hv
  apply function_eq_of_values (compose_function hr hp) hb
  intro i hi
  rw [value_compose_of_mem_function hr hp hi,
    show (skipIndices m n) ‘ i = prefixSize m i from value_definableGraph _ _ _ hi,
    prependTuple_value_tail hn hi]

theorem compose_prependTuple {m : ℕ} {n r b A B : V} (hn : n ∈ (ω : V))
    (hr : r ∈ A ^ n) (hb : b ∈ B ^ A) (v : Fin m → V) (hv : ∀ i, v i ∈ A) :
    compose (prependTuple n r v) b = prependTuple n (compose r b) (fun i ↦ b ‘ (v i)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change compose (assignmentPrepend (prefixSize m n) (prependTuple n r (fun i ↦ v i.succ)) (v 0)) b = _
    rw [compose_assignmentPrepend (prefixSize_natural m hn)
      (prependTuple_function hn hr _ (fun i ↦ hv i.succ)) hb (hv 0),
      ih (fun i ↦ v i.succ) (fun i ↦ hv i.succ)]
    rfl

noncomputable def prefixRenaming {a m : ℕ} (r : Fin a → Fin m) (n : V) : V :=
  prependTuple n (skipIndices m n) (fun i ↦ ((r i).val : V))

theorem prefixRenaming_function {a m : ℕ} (r : Fin a → Fin m) {n : V} (hn : n ∈ (ω : V)) :
    prefixRenaming r n ∈ prefixSize m n ^ prefixSize a n :=
  prependTuple_function hn (skipIndices_function m hn) _ (fun i ↦ natCast_mem_prefixSize hn (r i))

theorem prefixRenaming_compose {a m : ℕ} (r : Fin a → Fin m) {n b A : V} (hn : n ∈ (ω : V))
    (hb : b ∈ A ^ n) (v : Fin m → V) (hv : ∀ i, v i ∈ A) :
    compose (prefixRenaming r n) (prependTuple n b v) = prependTuple n b (v ∘ r) := by
  rw [prefixRenaming, compose_prependTuple hn (skipIndices_function m hn)
    (prependTuple_function hn hb v hv) _ (fun i ↦ natCast_mem_prefixSize hn (r i)),
    skipIndices_compose_prependTuple hn hb v hv]
  congr 1
  funext i
  exact prependTuple_value_front hn b v (r i)

theorem standardIndices_compose_prependTuple {m : ℕ} {n b A : V} (hn : n ∈ (ω : V))
    (hb : b ∈ A ^ n) (v : Fin m → V) (hv : ∀ i, v i ∈ A) :
    compose (standardTuple (fun i : Fin m ↦ (i.val : V))) (prependTuple n b v) = standardTuple v := by
  have hr := standardTuple_mem_function (fun i : Fin m ↦ (i.val : V)) (natCast_mem_prefixSize hn)
  have hp := prependTuple_function hn hb v hv
  apply function_eq_of_values (compose_function hr hp) (standardTuple_mem_function v hv)
  intro i hi
  rw [mem_natCast_iff] at hi
  obtain ⟨j, rfl⟩ := hi
  rw [value_compose_of_mem_function hr hp (natCast_mem_of_lt j.isLt), value_standardTuple,
    prependTuple_value_front hn, value_standardTuple]

end ZFVP
