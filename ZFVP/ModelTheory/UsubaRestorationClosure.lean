import ZFVP.ModelTheory.UsubaSaturatedIterand
import ZFVP.ModelTheory.ForcingSelectedUnion
import ZFVP.ModelTheory.ForcingDependentChoiceTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dcOrdinal_lt_usubaSeed {α : V} [IsOrdinal α]
    (hDC : InternalDependentChoiceAt α) (hAC : ¬InternalChoice V) :
    α ∈ (woodinSeedCardinal : V) := by
  have hs := woodinSeedCardinal_spec hAC
  rcases IsOrdinal.mem_trichotomy α (woodinSeedCardinal : V) with h | he | h
  · exact h
  · exact False.elim (hs.2.1 (he ▸ hDC))
  · exact False.elim (hs.2.1 (hDC.downward (IsOrdinal.toIsTransitive.transitive _ h)))

theorem usubaRestoration_condition_function {p : V} (hp : p ∈ (usubaRestorationPoset : V)) :
    IsFunction p := by
  classical
  by_cases hAC : InternalChoice V
  · rw [usubaRestorationPoset_of_choice hAC] at hp
    rw [mem_singleton_iff.mp hp]
    infer_instance
  · rw [usubaRestorationPoset_of_not_choice hAC] at hp
    exact ((mem_usubaCollapse _ _ _).mp hp).2.1

theorem usubaRestoration_sequence_union {α f : V} [IsOrdinal α]
    (hDC : InternalDependentChoiceAt α) (hf : f ∈ (usubaRestorationPoset : V) ^ α)
    (hc : CompatibleFunctionFamily (range f)) : ⋃ˢ range f ∈ (usubaRestorationPoset : V) := by
  classical
  by_cases hAC : InternalChoice V
  · rw [usubaRestorationPoset_of_choice hAC] at hf ⊢
    apply mem_singleton_iff.mpr
    apply subset_empty_iff_eq_empty.mp
    intro x hx
    obtain ⟨p, hp, hx⟩ := mem_sUnion_iff.mp hx
    have hp0 : p = (∅ : V) := mem_singleton_iff.mp (range_subset_of_mem_function hf _ hp)
    exact False.elim (not_mem_empty (hp0 ▸ hx))
  · rw [usubaRestorationPoset_of_not_choice hAC] at hf ⊢
    exact usubaCollapse_sequence_union woodinSeedCardinal_regular (dcOrdinal_lt_usubaSeed hDC hAC) hDC hf hc

theorem usubaRestoration_separative_union_bound {α f : V} [IsOrdinal α]
    (hDC : InternalDependentChoiceAt α)
    (hf : IsForcingDescending (usubaRestorationPoset : V)
      (forcingSeparativeOrder usubaRestorationPoset (reverseInclusionOrder usubaRestorationPoset)) α f) :
    ⋃ˢ range f ∈ (usubaRestorationPoset : V) ∧ ∀ i ∈ α,
      ⟨⋃ˢ range f, f ‘ i⟩ₖ ∈ reverseInclusionOrder (usubaRestorationPoset : V) := by
  have hc := compatible_range_of_separative_descending (fun _ hp ↦ usubaRestoration_condition_function hp) hf
  have hu := usubaRestoration_sequence_union hDC hf.1 hc
  refine ⟨hu, fun i hi ↦ (pair_mem_reverseInclusionOrder _ _ _).mpr
    ⟨hu, function_value_mem hf.1 hi, ?_⟩⟩
  intro x hx
  exact mem_sUnion_iff.mpr ⟨f ‘ i, value_mem_range hf.1 hi, hx⟩

theorem usubaRestoration_closedAt {α : V} [IsOrdinal α] (hDC : InternalDependentChoiceAt α) :
    IsForcingClosedAt (usubaRestorationPoset : V) (reverseInclusionOrder usubaRestorationPoset) α := by
  intro f hf
  have hs : IsForcingDescending (usubaRestorationPoset : V)
      (forcingSeparativeOrder usubaRestorationPoset (reverseInclusionOrder usubaRestorationPoset)) α f :=
    ⟨hf.1, fun i hi j hj ↦ forcingOrder_subset_separative
      (reverseInclusionOrder_poset _).1 _ (hf.2 i hi j hj)⟩
  exact ⟨⋃ˢ range f, usubaRestoration_separative_union_bound hDC hs⟩

theorem usubaRestoration_separative_closedAt {α : V} [IsOrdinal α]
    (hDC : InternalDependentChoiceAt α) :
    IsForcingClosedAt (usubaRestorationPoset : V)
      (forcingSeparativeOrder usubaRestorationPoset (reverseInclusionOrder usubaRestorationPoset)) α := by
  intro f hf
  obtain ⟨hu, hb⟩ := usubaRestoration_separative_union_bound hDC hf
  exact ⟨⋃ˢ range f, hu, fun i hi ↦
    forcingOrder_subset_separative (reverseInclusionOrder_poset _).1 _ (hb i hi)⟩

theorem usubaRestoration_closedThrough {α : V} [IsOrdinal α] (hDC : InternalDependentChoiceAt α) :
    IsForcingClosedThrough (usubaRestorationPoset : V) (reverseInclusionOrder usubaRestorationPoset) α := by
  intro β hβ hβα
  have := hβ
  exact usubaRestoration_closedAt (hDC.downward hβα)

namespace ForcingContext
variable (A : ForcingContext V)

theorem restoration_preserves_DC {α : V} [IsOrdinal α] (hDC : InternalDependentChoiceAt α)
    (hP : A.P = usubaRestorationPoset) (hR : A.R = reverseInclusionOrder A.P) :
    InternalDependentChoiceAt (A.check α) := by
  apply A.dependentChoiceAt_of_closed hDC
  rw [hR, hP]
  exact usubaRestoration_closedThrough hDC

theorem forcingSelectedUnion_usuba_bound {C D H : V}
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f : ForcingName A.P) {α : A.Model} [IsOrdinal α]
    (hf : A.ofName f ∈ A.check D ^ α) (hDC : InternalDependentChoiceAt α)
    (hs : IsForcingDescending (usubaRestorationPoset : A.Model)
      (forcingSeparativeOrder usubaRestorationPoset (reverseInclusionOrder usubaRestorationPoset)) α
      (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC))) :
    let u := A.ofName ⟨forcingSelectedUnion A.P A.R A.one C H f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩
    u ∈ (usubaRestorationPoset : A.Model) ∧ ∀ i ∈ α,
      ⟨u, (compose (compose (A.ofName f) (A.check H)) (A.evaluationGraph C hC)) ‘ i⟩ₖ ∈
        reverseInclusionOrder (usubaRestorationPoset : A.Model) := by
  dsimp only
  rw [A.forcingSelectedUnion_eq_union_range hC hH f hf]
  exact usubaRestoration_separative_union_bound hDC hs

end ForcingContext
end ZFVP
