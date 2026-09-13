import ZFVP.ModelTheory.ShiftedCriticalEmbeddings

/-! Bounds for shifted internal critical-sequence indices. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem iterate_subset_add {q i : V} (hq : q ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    criticalIterate f κ q ⊆ criticalIterate f κ (ordinalAdd q i) := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  have he := (h.power hi).ordinal_subset_value (iterate_spec hδ h hκ hq).1
    (iterate_spec hδ h hκ hq).2.1
  rw [embeddingPower_value_criticalIterate h hκ.mem_domain hq hi] at he
  exact he

theorem iterate_add_increasing {q i : V} (hq : q ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    criticalIterate f κ (ordinalAdd q i) ∈ criticalIterate f κ (ordinalAdd (succ q) i) := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  have he := ((h.power hi).value_mem_iff (iterate_spec hδ h hκ hq).2.1
    (iterate_spec hδ h hκ (ω_succ_closed hq)).2.1).mpr (iterate_increasing hδ h hκ hq)
  rw [embeddingPower_value_criticalIterate h hκ.mem_domain hq hi,
    embeddingPower_value_criticalIterate h hκ.mem_domain (ω_succ_closed hq) hi] at he
  exact he

end CriticalSequence

end ZFVP
