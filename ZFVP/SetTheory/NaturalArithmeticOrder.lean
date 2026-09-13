import ZFVP.SetTheory.NaturalArithmeticLaws

/-! Order compatibility and differences for arithmetic on internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalAdd_mono_first_natural {a b c : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) (hab : a ⊆ b) :
    ordinalAdd a c ⊆ ordinalAdd b c := by
  let := IsOrdinal.of_mem ha
  let := IsOrdinal.of_mem hb
  rw [ordinalAdd_comm_natural ha hc, ordinalAdd_comm_natural hb hc]
  exact ordinalAdd_mono_right c hab

theorem ordinalAdd_lt_first_natural {a b c : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) (hab : a ∈ b) :
    ordinalAdd a c ∈ ordinalAdd b c := by
  let := IsOrdinal.of_mem hb
  rw [ordinalAdd_comm_natural ha hc, ordinalAdd_comm_natural hb hc]
  exact ordinalAdd_mem hab

theorem ordinalAdd_mono_natural {a b c d : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hab : a ⊆ b) (hcd : c ⊆ d) : ordinalAdd a c ⊆ ordinalAdd b d := by
  let := IsOrdinal.of_mem hc
  let := IsOrdinal.of_mem hd
  exact subset_trans (ordinalAdd_mono_first_natural ha hb hc hab) (ordinalAdd_mono_right b hcd)

theorem ordinalAdd_difference_natural {a b : V} (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
    (hab : a ⊆ b) : ∃ c ∈ (ω : V), ordinalAdd a c = b := by
  let := IsOrdinal.of_mem ha
  apply naturalNumber_induction (fun b ↦ a ⊆ b → ∃ c ∈ (ω : V), ordinalAdd a c = b)
    (by definability) ?_ ?_ b hb hab
  · intro h
    have he : a = ∅ := subset_empty_iff_eq_empty.mp h
    exact ⟨0, by simp, by simpa only [zero_def, ordinalAdd_zero] using he⟩
  · intro n hn ih h
    let := IsOrdinal.of_mem hn
    rcases IsOrdinal.subset_iff.mp h with he | hlt
    · exact ⟨0, by simp, by simpa only [zero_def, ordinalAdd_zero] using he⟩
    · have han : a ⊆ n := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hlt)
      obtain ⟨c, hc, he⟩ := ih han
      let := IsOrdinal.of_mem hc
      exact ⟨succ c, ω_succ_closed hc, by rw [ordinalAdd_succ, he]⟩

theorem naturalMul_mono_first {a b c : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) (hab : a ⊆ b) :
    naturalMul a c ⊆ naturalMul b c := by
  apply naturalNumber_induction (fun c ↦ naturalMul a c ⊆ naturalMul b c) (by definability) ?_ ?_ c hc
  · simp
  · intro n hn ih
    rw [naturalMul_succ _ hn, naturalMul_succ _ hn]
    exact ordinalAdd_mono_natural (naturalMul_natural ha hn) (naturalMul_natural hb hn) ha hb ih hab

theorem naturalMul_lt_first {a b c : V}
    (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hc : c ∈ (ω : V)) (hab : a ∈ b) (hc0 : (0 : V) ∈ c) :
    naturalMul a c ∈ naturalMul b c := by
  let := IsOrdinal.of_mem ha
  let := IsOrdinal.of_mem hb
  rcases internalNatural_cases hc with rfl | ⟨n, hn, rfl⟩
  · exact False.elim (mem_irrefl _ hc0)
  · let := IsOrdinal.of_mem (naturalMul_natural ha hn)
    let := IsOrdinal.of_mem (naturalMul_natural hb hn)
    have hsub := naturalMul_mono_first ha hb hn (IsOrdinal.toIsTransitive.transitive _ hab)
    have hs := ordinalAdd_mono_first_natural (naturalMul_natural ha hn) (naturalMul_natural hb hn) ha hsub
    have ht : ordinalAdd (naturalMul b n) a ∈ ordinalAdd (naturalMul b n) b := ordinalAdd_mem hab
    rw [naturalMul_succ _ hn, naturalMul_succ _ hn]
    rcases IsOrdinal.subset_iff.mp hs with he | hlt
    · exact he ▸ ht
    · exact IsOrdinal.toIsTransitive.mem_trans hlt ht

end ZFVP
