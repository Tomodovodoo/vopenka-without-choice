import ZFVP.SetTheory.CohenTranspositions
import ZFVP.SetTheory.CohenSetName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cohenName_finiteSupport {I τ : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions I) (cohenGroup I) (cohenFilter I) τ) :
    ∃ E, E ⊆ I ∧ IsInternallyFinite E ∧
      ∀ π, IsInternalPermutation I π → (∀ i ∈ E, π ‘ i = i) → nameAction (cohenPermutation I π) τ = τ := by
  obtain ⟨_, E, hEI, hEf, hE⟩ := (mem_cohenFilter_iff I _).mp (hereditarilySymmetric_symmetric hτ).2
  exact ⟨E, hEI, hEf, fun π hπ hfix ↦ (mem_sep_iff.mp (hE π hπ hfix)).2⟩

theorem cohen_fresh_transposition {p E i : V} (hp : p ∈ cohenConditions (ω : V))
    (hE : IsInternallyFinite E) (hiE : i ∉ E) :
    ∃ j ∈ (ω : V), j ≠ i ∧ j ∉ cohenSupport p ∧ j ∉ E ∧
      ∀ k ∈ E, k ∈ (ω : V) → (internalTransposition (ω : V) i j) ‘ k = k := by
  obtain ⟨j, hj, hjout⟩ := internallyFinite_fresh_natural
    (internallyFinite_insert (internallyFinite_union hE (cohenSupport_finite hp)) i)
  have hji : j ≠ i := fun he ↦ hjout (mem_insert.mpr (Or.inl he))
  have hjE : j ∉ E := fun he ↦ hjout (mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inl he))))
  have hjp : j ∉ cohenSupport p := fun he ↦ hjout (mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inr he))))
  refine ⟨j, hj, hji, hjp, hjE, ?_⟩
  intro k hk hkω
  exact internalTransposition_fixed hkω (fun he ↦ hiE (he ▸ hk)) (fun he ↦ hjE (he ▸ hk))

end ZFVP
