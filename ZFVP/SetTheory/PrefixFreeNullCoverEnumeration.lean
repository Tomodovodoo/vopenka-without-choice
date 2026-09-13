import ZFVP.SetTheory.PrefixFreeNullCover

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A countable internal set has a bijective enumeration by a natural or by omega. -/
theorem prefixCover_countable_enumeration {E : V} (hc : IsInternallyCountable E) :
    ∃ n, (n ∈ (ω : V) ∨ n = (ω : V)) ∧ ∃ g ∈ E ^ n, Injective g ∧ range g = E := by
  let n := wellOrderedCardinal E
  have hn : IsOrdinal n := (wellOrderedCardinal_spec hc.wellOrderable).1
  have hnω : n ⊆ (ω : V) := by
    have h := wellOrderedCardinal_mono hc.wellOrderable (ordinal_wellOrderable (ω : V)) hc
    rwa [wellOrderedCardinal_of_initial (omega_regular (V := V)).1] at h
  have he : n ≋ E := wellOrderedCardinal_cardEQ hc.wellOrderable
  obtain ⟨g, hg, hi, hr⟩ := exists_bijection_of_cardEQ he
  refine ⟨n, ?_, g, hg, hi, hr⟩
  rcases (IsOrdinal.subset_iff (α := n) (β := (ω : V))).mp hnω with he | hm
  · exact Or.inr he
  · exact Or.inl hm

theorem prefixCover_finite_lengths_bounded {E : V} (hfin : IsInternallyFinite E)
    (hE : E ⊆ binarySequences V) : ∃ M ∈ (ω : V), ∀ s ∈ E, domain s ⊆ M := by
  let L := repl domain (by definability) E
  have hf : IsInternallyFinite L := internallyFinite_repl domain (by definability) hfin
  have hL : L ⊆ (ω : V) := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := (repl_spec (by definability)).mp hd
    exact binarySequence_domain_mem (hE s hs)
  obtain ⟨M, hM, hLM⟩ := internallyFinite_naturals_bounded hf hL
  refine ⟨M, hM, ?_⟩
  intro s hs
  have hdM := hLM (domain s) ((repl_spec (by definability)).mpr ⟨s, hs, rfl⟩)
  exact (IsTransitive.nat hM).transitive _ hdM

/-- Normalize the exact `IsNull` witness to a prefix-free cover with no repetitions.
The enumeration domain is a natural, including zero, or omega. All valid finite
initial sums obey the original dyadic bound. -/
theorem isNull_prefixFree_enumerated_cover {A m : V} (hA : A ⊆ cantorSpace V)
    (hnull : IsNull A) (hm : m ∈ (ω : V)) :
    ∃ E, E ⊆ binarySequences V ∧ BinaryPrefixFree E ∧
      ∃ n, (n ∈ (ω : V) ∨ n = (ω : V)) ∧
        ∃ g ∈ E ^ n, Injective g ∧ range g = E ∧
          (∀ x ∈ A, ∃ i ∈ n, (g ‘ i) ⊆ x) ∧
          ∀ k ∈ (ω : V), k ⊆ n →
            ¬InternalRationalLT (dyadicUnit m) (rationalPartialSum (prefixWeights g) k) := by
  obtain ⟨f, hf, hcover, hsmall⟩ := hnull m hm
  have : IsFunction f := IsFunction.of_mem hf
  let E := minimalPrefixCover (range f)
  have hF : range f ⊆ binarySequences V := range_subset_of_mem_function hf
  have hE : E ⊆ binarySequences V := fun s hs ↦ hF s (minimalPrefixCover_subset _ s hs)
  have hp : BinaryPrefixFree E := minimalPrefixCover_prefixFree _
  have hFc : IsInternallyCountable (range f) := by
    rw [← prefixInitial_eq_range hf]
    exact internallyCountable_repl (fun i ↦ f ‘ i) (by definability) internallyCountable_omega
  have hEc := internallyCountable_subset hFc (minimalPrefixCover_subset (range f))
  obtain ⟨n, hn, g, hg, hgi, hgr⟩ := prefixCover_countable_enumeration hEc
  have : IsFunction g := IsFunction.of_mem hg
  refine ⟨E, hE, hp, n, hn, g, hg, hgi, hgr, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hix⟩ := hcover x hx
    have hfi : f ‘ i ∈ range f := mem_range_iff.mpr
      ⟨i, kpair_value_mem (by rwa [domain_eq_of_mem_function hf])⟩
    have hfsub : (f ‘ i) ⊆ x := (subset_iff_restrict_eq (hA x hx) (hF _ hfi)).mpr hix
    obtain ⟨s, hs, hsx⟩ := minimalPrefixCover_covers hF (hA x hx) ⟨f ‘ i, hfi, hfsub⟩
    obtain ⟨j, hj⟩ := mem_range_iff.mp (hgr.symm ▸ hs)
    refine ⟨j, by simpa only [domain_eq_of_mem_function hg] using mem_domain_of_kpair_mem hj, ?_⟩
    rwa [value_eq_of_kpair_mem hj]
  · intro k hk hkn
    have hki : IsInternallyFinite k := internallyFinite_of_cardLE_natural hk (CardLE.refl _)
    have hfin : IsInternallyFinite (prefixInitial g k) := internallyFinite_repl _ _ hki
    have hsub : prefixInitial g k ⊆ E := by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := (mem_prefixInitial_iff _ _ _).mp hs
      exact function_value_mem hg (hkn i hi)
    obtain ⟨M, hM, hdom⟩ := prefixCover_finite_lengths_bounded hfin (fun s hs ↦ hE s (hsub s hs))
    have hsm : SmallMeasure (prefixInitial g k) m :=
      finite_subset_raw_smallMeasure hf hsmall hfin
        (fun s hs ↦ minimalPrefixCover_subset _ s (hsub s hs))
    apply prefixWeights_sum_smallMeasure hk hM hm ?_ ?_ ?_ hsm
    · intro i hi
      exact hE _ (function_value_mem hg (hkn i hi))
    · intro i hi
      exact hdom _ ((mem_prefixInitial_iff _ _ _).mpr ⟨i, hi, rfl⟩)
    · intro i hi j hj hne
      exact binaryPrefixFree_incompatible hE hp
        (function_value_mem hg (hkn i hi)) (function_value_mem hg (hkn j hj))
        (fun he ↦ hne (injective_value_eq hg hgi (hkn i hi) (hkn j hj) he))

end ZFVP
