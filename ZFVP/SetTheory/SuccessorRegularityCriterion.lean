import ZFVP.SetTheory.CofinalityDictionary
import ZFVP.SetTheory.SmallCollapseSurjection
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A surjection onto the index set preserves cofinality after composition. -/
theorem IsCofinalMap.precompose_surjection {α β D f e : V}
    (hf : IsCofinalMap α β f) (he : e ∈ β ^ D) (hre : range e = β) :
    IsCofinalMap α D (compose e f) := by
  have : IsFunction e := IsFunction.of_mem he
  refine ⟨compose_function he hf.1, ?_⟩
  intro ξ hξ
  obtain ⟨i, hi, hξi⟩ := hf.2 ξ hξ
  obtain ⟨d, hd⟩ := mem_range_iff.mp (hre.symm ▸ hi)
  have hdD : d ∈ D := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hd
  refine ⟨d, hdD, ?_⟩
  rw [value_compose_of_mem_function he hf.1 hdD, value_eq_of_kpair_mem hd]
  exact hξi

/-- If `Vκ` cannot map cofinally into the Hartogs successor of `κ`, that
successor is regular. -/
theorem hartogsNumber_regular_of_no_hierarchy_cofinalMap {κ : V} [IsOrdinal κ]
    (hω : (ω : V) ⊆ κ)
    (hNo : ∀ f, ¬IsCofinalMap (hartogsNumber κ) (hierarchy κ) f) :
    IsRegularCardinal (hartogsNumber κ) := by
  have hκH : κ ∈ hartogsNumber κ := ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl κ)
  have hκsub : κ ⊆ hartogsNumber κ := IsOrdinal.toIsTransitive.transitive _ hκH
  refine ⟨hartogsNumber_initial κ, subset_trans hω hκsub, ?_⟩
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset (hartogsNumber κ)) with heq | hlt
  · exact heq
  have hβκ : internalCofinality (hartogsNumber κ) ⊆ κ :=
    (initialOrdinal_cardLE_iff (internalCofinality_initial _)).mp (cardLE_of_mem_hartogsNumber hlt)
  obtain ⟨f, hf⟩ := cofinalMap_exists (hartogsNumber κ)
  have hzero : (∅ : V) ∈ hartogsNumber κ := hκsub ∅ (hω ∅ empty_mem_ω)
  obtain ⟨i, hi, _⟩ := hf.2 ∅ hzero
  have hne : IsNonempty (internalCofinality (hartogsNumber κ)) := ⟨i, hi⟩
  have hid : range (identity (internalCofinality (hartogsNumber κ))) =
      internalCofinality (hartogsNumber κ) := by
    apply mem_ext
    intro x
    simp only [mem_range_iff, kpair_mem_identity_iff]
    exact ⟨fun ⟨y, hy, he⟩ ↦ he ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩
  obtain ⟨e, he, hre⟩ := surjection_extension
    (subset_trans hβκ (ordinal_subset_hierarchy κ)) (identity_mem_function _) hid hne
  exact False.elim (hNo (compose e f) (hf.precompose_surjection he hre))

/-- At a singular infinite ordinal, ruling out cofinal maps from each smaller
rank suffices to make the Hartogs successor regular. -/
theorem hartogsNumber_regular_of_singular_no_small_cofinalMap {κ : V} [IsOrdinal κ]
    (hω : (ω : V) ⊆ κ) (hsing : internalCofinality κ ∈ κ)
    (hNo : ∀ x ∈ hierarchy κ, ∀ f, ¬IsCofinalMap (hartogsNumber κ) x f) :
    IsRegularCardinal (hartogsNumber κ) := by
  have hκH : κ ∈ hartogsNumber κ := ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl κ)
  have hκsub : κ ⊆ hartogsNumber κ := IsOrdinal.toIsTransitive.transitive _ hκH
  refine ⟨hartogsNumber_initial κ, subset_trans hω hκsub, ?_⟩
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset (hartogsNumber κ)) with heq | hlt
  · exact heq
  have hβκ : internalCofinality (hartogsNumber κ) ⊆ κ :=
    (initialOrdinal_cardLE_iff (internalCofinality_initial _)).mp (cardLE_of_mem_hartogsNumber hlt)
  rcases IsOrdinal.subset_iff.mp hβκ with heq | hlt
  · have hid := internalCofinality_idempotent (hartogsNumber κ)
    rw [heq] at hid
    rw [hid] at hsing
    exact False.elim (mem_irrefl κ hsing)
  · obtain ⟨f, hf⟩ := cofinalMap_exists (hartogsNumber κ)
    exact False.elim (hNo _ (ordinal_subset_hierarchy κ _ hlt) f hf)

end ZFVP


