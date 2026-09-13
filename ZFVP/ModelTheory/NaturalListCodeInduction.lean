import ZFVP.ModelTheory.InternalFormulaRequirements

/-! Definable constructor induction for all internal natural list codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalListCode_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hzero : P 0)
    (hcons : ∀ x xs, x ∈ (ω : V) → xs ∈ (ω : V) → P xs → P (succ (naturalSquarePair x xs)))
    {xs : V} (hxs : xs ∈ (ω : V)) : P xs := by
  have H : ∀ c : Ordinal V, (c : V) ∈ (ω : V) → P c := by
    apply transfinite_induction (P := fun c : V ↦ c ∈ (ω : V) → P c) (by definability)
    intro c ih hc
    rcases naturalCode_cases hc with h0 | ⟨x, hx, xs, hxs, he⟩
    · simpa only [h0] using hzero
    · have : IsOrdinal xs := IsOrdinal.of_mem hxs
      have hmem : xs ∈ (c : V) := he ▸ naturalCode_payload_mem hx hxs
      rw [he]
      exact hcons x xs hx hxs (ih (IsOrdinal.toOrdinal xs) hmem hxs)
  have : IsOrdinal xs := IsOrdinal.of_mem hxs
  exact H (IsOrdinal.toOrdinal xs) hxs

end ZFVP
