import ZFVP.ModelTheory.SchmerlInternalInfinitaryInduction

/-! Internal truth at a formula does not depend on the choice of a valid
fragment containing that formula. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem holds_fragment_iff {L F H M : V} (hF : IsFragment L F) (hH : IsFragment L H) :
    ∀ n φ, ⟨n, φ⟩ₖ ∈ F → ⟨n, φ⟩ₖ ∈ H → ∀ b,
      Holds L F M n φ b ↔ Holds L H M n φ b := by
  apply fragment_induction hF (fun n φ ↦ ⟨n, φ⟩ₖ ∈ H → ∀ b,
    Holds L F M n φ b ↔ Holds L H M n φ b) (by unfold Holds; definability)
  · intro n φ ht _ hu b
    rw [holds_fo hF ht, holds_fo hH hu]
  · intro n φ ht _ ih hu b
    by_cases hb : b ∈ structureDomain M ^ n
    · rw [holds_neg hF ht hb, holds_neg hH hu hb]
      exact not_congr (ih (hH.immediate_mem hu ((immediate_neg_iff _ _ _).mpr rfl)) b)
    · exact iff_of_false (fun h ↦ hb (holds_assignment_mem h)) (fun h ↦ hb (holds_assignment_mem h))
  · intro n f ht hf hd _ ih hu b
    by_cases hb : b ∈ structureDomain M ^ n
    · rw [holds_conj hF ht hb, holds_conj hH hu hb]
      apply forall₂_congr
      intro i hi
      exact ih i hi (hH.immediate_mem hu
        ((immediate_conj_iff _ _ _).mpr ⟨hf, i, hd.symm ▸ hi, rfl⟩)) b
    · exact iff_of_false (fun h ↦ hb (holds_assignment_mem h)) (fun h ↦ hb (holds_assignment_mem h))
  · intro n φ ht _ ih hu b
    by_cases hb : b ∈ structureDomain M ^ n
    · rw [holds_exs hF ht hb, holds_exs hH hu hb]
      exact exists_congr fun x ↦ and_congr_right fun _ ↦
        ih (hH.immediate_mem hu ((immediate_exs_iff _ _ _).mpr rfl)) (assignmentPrepend n b x)
    · exact iff_of_false (fun h ↦ hb (holds_assignment_mem h)) (fun h ↦ hb (holds_assignment_mem h))
  · intro n φ ht _ ih hu b
    by_cases hb : b ∈ structureDomain M ^ n
    · rw [holds_q hF ht hb, holds_q hH hu hb]
      have he : witnessFiber M n b (truthGraph L F M) φ = witnessFiber M n b (truthGraph L H M) φ := by
        apply mem_ext
        intro x
        simp only [witnessFiber, mem_sep_iff]
        exact and_congr_right fun _ ↦
          ih (hH.immediate_mem hu ((immediate_q_iff _ _ _).mpr rfl)) (assignmentPrepend n b x)
      rw [he]
    · exact iff_of_false (fun h ↦ hb (holds_assignment_mem h)) (fun h ↦ hb (holds_assignment_mem h))

end ZFVP.Infinitary.Internal
