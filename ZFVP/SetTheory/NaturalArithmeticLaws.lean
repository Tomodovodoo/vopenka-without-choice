import ZFVP.SetTheory.NaturalMultiplication

/-! Addition and multiplication laws for all internal natural numbers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalAdd_one_natural {a : V} (ha : a ∈ (ω : V)) : ordinalAdd a 1 = succ a := by
  let := IsOrdinal.of_mem ha
  change ordinalAdd a (succ 0) = succ a
  rw [ordinalAdd_succ, show (0 : V) = ∅ from rfl, ordinalAdd_zero]

theorem ordinalAdd_assoc_natural {a b c : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    ordinalAdd (ordinalAdd a b) c = ordinalAdd a (ordinalAdd b c) := by
  let := IsOrdinal.of_mem ha
  let := IsOrdinal.of_mem hb
  apply naturalNumber_induction (fun c ↦ ordinalAdd (ordinalAdd a b) c = ordinalAdd a (ordinalAdd b c))
    (by definability) ?_ ?_ c hc
  · simp only [zero_def, ordinalAdd_zero]
  · intro n hn ih
    let := IsOrdinal.of_mem hn
    rw [ordinalAdd_succ, ordinalAdd_succ, ordinalAdd_succ, ih]

theorem ordinalAdd_swap_natural {a b c : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    ordinalAdd (ordinalAdd a b) c = ordinalAdd (ordinalAdd a c) b := by
  rw [ordinalAdd_assoc_natural ha hb hc, ordinalAdd_comm_natural hb hc,
    ← ordinalAdd_assoc_natural ha hc hb]

theorem naturalMul_one_left {a : V} (ha : a ∈ (ω : V)) : naturalMul (1 : V) a = a := by
  apply naturalNumber_induction (fun a ↦ naturalMul (1 : V) a = a) (by definability) ?_ ?_ a ha
  · simp
  · intro n hn ih
    rw [naturalMul_succ _ hn, ih, ordinalAdd_one_natural hn]

theorem naturalMul_add_right {a b c : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    naturalMul a (ordinalAdd b c) = ordinalAdd (naturalMul a b) (naturalMul a c) := by
  let := IsOrdinal.of_mem hb
  apply naturalNumber_induction
    (fun c ↦ naturalMul a (ordinalAdd b c) = ordinalAdd (naturalMul a b) (naturalMul a c))
    (by definability) ?_ ?_ c hc
  · simp only [zero_def, ordinalAdd_zero, naturalMul_empty]
  · intro n hn ih
    let := IsOrdinal.of_mem hn
    rw [ordinalAdd_succ, naturalMul_succ _ (ordinalAdd_natural hb hn), ih, naturalMul_succ _ hn,
      ordinalAdd_assoc_natural (naturalMul_natural ha hb) (naturalMul_natural ha hn) ha]

theorem naturalMul_succ_left {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    naturalMul (succ a) b = ordinalAdd (naturalMul a b) b := by
  let := IsOrdinal.of_mem ha
  apply naturalNumber_induction (fun b ↦ naturalMul (succ a) b = ordinalAdd (naturalMul a b) b)
    (by definability) ?_ ?_ b hb
  · simp only [zero_def, naturalMul_empty, ordinalAdd_zero]
  · intro n hn ih
    let := IsOrdinal.of_mem hn
    let := IsOrdinal.of_mem (naturalMul_natural ha hn)
    rw [naturalMul_succ _ hn, ih, naturalMul_succ _ hn, ordinalAdd_succ, ordinalAdd_succ]
    exact congrArg succ (ordinalAdd_swap_natural (naturalMul_natural ha hn) hn ha)

theorem naturalMul_comm {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    naturalMul a b = naturalMul b a := by
  apply naturalNumber_induction (fun b ↦ naturalMul a b = naturalMul b a) (by definability) ?_ ?_ b hb
  · rw [naturalMul_zero, naturalMul_zero_left ha]
  · intro n hn ih
    rw [naturalMul_succ _ hn, naturalMul_succ_left hn ha, ih]

theorem naturalMul_assoc {a b c : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) :
    naturalMul (naturalMul a b) c = naturalMul a (naturalMul b c) := by
  apply naturalNumber_induction (fun c ↦ naturalMul (naturalMul a b) c = naturalMul a (naturalMul b c))
    (by definability) ?_ ?_ c hc
  · simp
  · intro n hn ih
    rw [naturalMul_succ _ hn, ih, naturalMul_succ _ hn,
      naturalMul_add_right ha (naturalMul_natural hb hn) hb]

end ZFVP
