import ZFVP.ModelTheory.EmbeddingBoundedOperations

/-! An internal elementary graph fixes every internal natural, including nonstandard naturals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f : V} [hA : IsCodingSupport A] [IsTransitive B]

theorem value_natural (h : IsCodedMembershipEmbedding A B f) {n : V} (hn : n ∈ (ω : V)) :
    f ‘ n = n := by
  apply naturalNumber_induction (fun n ↦ f ‘ n = n) (by definability)
    (h.value_empty IsCodingSupport.empty_mem) ?_ n hn
  intro i hi ih
  rw [h.value_succ (IsCodingSupport.natural_mem hi) (IsCodingSupport.natural_mem (ω_succ_closed hi)), ih]

theorem value_numeral (h : IsCodedMembershipEmbedding A B f) (n : ℕ) : f ‘ (n : V) = (n : V) :=
  h.value_natural (by simp)

end IsCodedMembershipEmbedding

end ZFVP
