import ZFVP.ModelTheory.CriticalPoint

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

theorem value_natural_of_omega_mem {A B e n : V} [IsTransitive A] [IsTransitive B]
    (h : IsCodedMembershipEmbedding A B e) (hω : (ω : V) ∈ A) (hn : n ∈ (ω : V)) :
    e ‘ n = n := by
  have hm {i : V} (hi : i ∈ (ω : V)) : i ∈ A := (inferInstance : IsTransitive A).mem_trans hi hω
  apply naturalNumber_induction (fun n ↦ e ‘ n = n) (by definability)
    (h.value_empty (hm (by simp))) ?_ n hn
  intro i hi ih
  rw [h.value_succ (hm hi) (hm (ω_succ_closed hi)), ih]

end IsCodedMembershipEmbedding

theorem IsCriticalPoint.omega_lt_of_omega_mem {A B e κ : V} [IsTransitive A] [IsTransitive B]
    (hc : IsCriticalPoint A e κ) (he : IsCodedMembershipEmbedding A B e) (hω : (ω : V) ∈ A) :
    (ω : V) ∈ κ := by
  let := hc.ordinal
  rcases IsOrdinal.mem_trichotomy κ (ω : V) with hl | heq | hg
  · exact False.elim (hc.moved (he.value_natural_of_omega_mem hω hl))
  · exact False.elim (hc.moved (heq ▸ he.value_omega hω))
  · exact hg

end ZFVP
