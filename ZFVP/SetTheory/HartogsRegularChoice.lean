import ZFVP.SetTheory.RegularUnions
import ZFVP.SetTheory.CofinalityDictionary

/-! Under internal choice the Hartogs number of an infinite set is a regular cardinal. Applied to
an infinite well-orderable `A` this is the usual statement that successor cardinals are regular. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every ordinal below the Hartogs number of `A` injects into `A`. -/
theorem mem_hartogsNumber_cardLE {A α : V} (hα : α ∈ hartogsNumber A) : α ≤# A :=
  cardLE_of_mem_hartogsNumber hα

/-- If `ω` injects into `A` then `ω` is a subset of the Hartogs number of `A`. -/
theorem hartogs_omega_subset {A : V} (hω : (ω : V) ≤# A) : (ω : V) ⊆ hartogsNumber A :=
  IsOrdinal.toIsTransitive.transitive _ (ordinal_cardLE_iff_mem_hartogsNumber.mp hω)

/-- The Hartogs number of an infinite set is closed under successor. -/
theorem hartogsNumber_succ_mem {A α : V} (hω : (ω : V) ≤# A) (hα : α ∈ hartogsNumber A) :
    succ α ∈ hartogsNumber A := by
  have : IsOrdinal α := IsOrdinal.of_mem hα
  have hinf : (ω : V) ⊆ α → succ α ∈ hartogsNumber A := by
    intro h
    exact ordinal_cardLE_iff_mem_hartogsNumber.mp
      ((succ_cardLE_of_omega_subset h).trans (mem_hartogsNumber_cardLE hα))
  rcases IsOrdinal.mem_trichotomy α (ω : V) with h | h | h
  · exact hartogs_omega_subset hω _ (ω_succ_closed h)
  · exact hinf (h ▸ subset_refl _)
  · exact hinf (IsOrdinal.toIsTransitive.transitive _ h)

/-- With internal choice, the Hartogs number of a set that `ω` injects into is regular: it is an
initial ordinal above `ω` whose cofinality is itself. If it had a cofinal map from a smaller
ordinal `β`, it would be the union of `β` many sets each injecting into `A`, so it would inject
into `β × A` and hence into `A`. -/
theorem hartogsNumber_regular (hAC : InternalChoice V) {A : V} (hω : (ω : V) ≤# A) :
    IsRegularCardinal (hartogsNumber A) := by
  refine ⟨hartogsNumber_initial A, hartogs_omega_subset hω, ?_⟩
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset (hartogsNumber A)) with he | hlt
  · exact he
  exfalso
  obtain ⟨f, hf⟩ := cofinalMap_exists (hartogsNumber A)
  have hfun : IsFunction f := IsFunction.of_mem hf.1
  have hdom : domain f = internalCofinality (hartogsNumber A) := domain_eq_of_mem_function hf.1
  have hsub : hartogsNumber A ⊆ ⋃ˢ range f := by
    intro ξ hξ
    obtain ⟨i, hi, hle⟩ := hf.2 (succ ξ) (hartogsNumber_succ_mem hω hξ)
    exact mem_sUnion_iff.mpr ⟨f ‘ i, mem_range_of_kpair_mem (kpair_value_mem (hdom ▸ hi)),
      hle _ (mem_succ_self ξ)⟩
  have hsmall : ∀ i ∈ internalCofinality (hartogsNumber A), f ‘ i ≤# A :=
    fun i hi ↦ mem_hartogsNumber_cardLE (function_value_mem hf.1 hi)
  have h1 : hartogsNumber A ≤# internalCofinality (hartogsNumber A) ×ˢ A :=
    (cardLE_of_subset hsub).trans (sUnion_range_cardLE_prod hAC hdom hsmall)
  have hwo := wellOrderable_of_internalChoice hAC A
  have hlamA : wellOrderedCardinal A ≋ A := wellOrderedCardinal_cardEQ hwo
  have : IsOrdinal (wellOrderedCardinal A) := (wellOrderedCardinal_initial hwo).1
  have hωlam : (ω : V) ⊆ wellOrderedCardinal A :=
    (initialOrdinal_cardLE_iff ⟨IsOrdinal.ω, fun n hn ↦ omega_not_cardLE_natural hn⟩).mp
      (hω.trans hlamA.2)
  have h2 : internalCofinality (hartogsNumber A) ×ˢ A ≤# wellOrderedCardinal A :=
    prod_cardLE_of_cardLE_initial (wellOrderedCardinal_initial hwo) hωlam
      ((mem_hartogsNumber_cardLE hlt).trans hlamA.2) hlamA.2
  exact not_hartogsNumber_cardLE A ((h1.trans h2).trans hlamA.1)

end ZFVP
