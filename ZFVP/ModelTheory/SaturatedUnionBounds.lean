import ZFVP.ModelTheory.ForcingSaturatedName
import ZFVP.ModelTheory.ForcingNameUnions
import ZFVP.SetTheory.ForcingUnionClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem saturated_sequence_union_bound (A : ForcingContext V) {δ α s : V} [IsOrdinal δ] [IsFunction s]
    (hα : α ∈ internalCofinality δ) (hs : IsNameSequence A.P s)
    (hf : s ∈ (forcingNameHierarchy A.P δ) ^ α) (Q : ForcingName A.P)
    (hclosed : IsForcingUnionClosedAt (A.ofName Q) (A.check α))
    (hdir : IsForcingDirectedFamily (A.ofName (A.saturatedName (forcingNameHierarchy A.P δ) Q))
      (reverseInclusionOrder (A.ofName (A.saturatedName (forcingNameHierarchy A.P δ) Q)))
      (A.check α) (A.sequenceValue s hs)) :
    A.ofName ⟨⋃ˢ range s, hs.union_isName⟩ ∈ A.ofName (A.saturatedName (forcingNameHierarchy A.P δ) Q) ∧
      ∀ i, ∀ hi : i ∈ domain s, ⟨A.ofName ⟨⋃ˢ range s, hs.union_isName⟩, A.ofName ⟨s ‘ i, hs i hi⟩⟩ₖ ∈
        reverseInclusionOrder (A.ofName (A.saturatedName (forcingNameHierarchy A.P δ) Q)) := by
  have hd := domain_eq_of_mem_function hf
  have hm (i : V) (hi : i ∈ domain s) : A.ofName ⟨s ‘ i, hs i hi⟩ ∈
      A.ofName (A.saturatedName (forcingNameHierarchy A.P δ) Q) := by
    rw [← A.sequenceValue_value s hs hi]
    exact function_value_mem hdir.1 ((A.check_mem_iff _ _).mpr (hd ▸ hi))
  have hQ (i : V) (hi : i ∈ domain s) : A.ofName ⟨s ‘ i, hs i hi⟩ ∈ A.ofName Q :=
    ((A.mem_saturatedName_iff _ Q _).mp (hm i hi)).1
  have hF : A.sequenceValue s hs ∈ A.ofName Q ^ A.check α := by
    simpa only [hd] using A.sequenceValue_mem_function s hs hQ
  have huQ : A.ofName ⟨⋃ˢ range s, hs.union_isName⟩ ∈ A.ofName Q := by
    rw [A.sequenceNameUnion_value s hs]
    apply hclosed _ hF
    intro i hi j hj
    obtain ⟨k, hk, hki, hkj⟩ := hdir.2 i hi j hj
    exact ⟨k, hk, ((pair_mem_reverseInclusionOrder _ _ _).mp hki).2.2,
      ((pair_mem_reverseInclusionOrder _ _ _).mp hkj).2.2⟩
  have hu : A.ofName ⟨⋃ˢ range s, hs.union_isName⟩ ∈
      A.ofName (A.saturatedName (forcingNameHierarchy A.P δ) Q) :=
    (A.mem_saturatedName_iff _ Q _).mpr ⟨huQ, ⟨⋃ˢ range s, hs.union_isName⟩,
      forcingNameHierarchy_sequence_union hα hf, rfl⟩
  refine ⟨hu, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hu, hm i hi, ?_⟩⟩
  rw [A.sequenceNameUnion_value s hs, ← A.sequenceValue_value s hs hi]
  intro x hx
  exact mem_sUnion_iff.mpr ⟨(A.sequenceValue s hs) ‘ (A.check i), mem_range_of_kpair_mem
    (kpair_value_mem (by rw [A.sequenceValue_domain]; exact (A.check_mem_iff _ _).mpr hi)), hx⟩

end ForcingContext
end ZFVP
