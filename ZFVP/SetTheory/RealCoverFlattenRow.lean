import ZFVP.SetTheory.RealCoverFlattenPartition
import ZFVP.SetTheory.PrefixFreeNullCoverPadding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem flattenIndexImage_eq_range {h l J : V} (hh : h ∈ J ^ l) : rationalIndexImage h l = range h := by
  have : IsFunction h := IsFunction.of_mem hh
  apply mem_ext
  intro x
  rw [mem_rationalIndexImage_iff, mem_range_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, kpair_value_mem (by rwa [domain_eq_of_mem_function hh])⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by simpa only [domain_eq_of_mem_function hh] using mem_domain_of_kpair_mem hj,
      (value_eq_of_kpair_mem hj).symm⟩

/-- Contributions from one row of a finite injective list of pairs are bounded
by a sufficiently long partial sum of that row. -/
theorem flattenRow_sum_le {e w u k N i : V}
    (he : e ∈ ((ω : V) ×ˢ (ω : V)) ^ (ω : V)) (hei : Injective e)
    (hk : k ∈ (ω : V)) (hN : N ∈ (ω : V))
    (hw : ∀ j ∈ (ω : V), w ‘ j ∈ internalRationals V)
    (hu : ∀ j ∈ (ω : V), u ‘ j ∈ internalRationals V)
    (hupos : ∀ j ∈ (ω : V), ¬InternalRationalLT (u ‘ j) (rationalZero V))
    (hcols : ∀ j ∈ k, kpair.π₂ (e ‘ j) ∈ N)
    (hmatch : ∀ j ∈ k, kpair.π₁ (e ‘ j) = i → w ‘ j = u ‘ (kpair.π₂ (e ‘ j))) :
    ¬InternalRationalLT (rationalPartialSum u N)
      (rationalPartialSum (rationalMaskedWeights w (flattenRowIndices e i)) k) := by
  let J := k ∩ flattenRowIndices e i
  have hJk : J ⊆ k := fun j hj ↦ (mem_inter_iff.mp hj).1
  have hJfin : IsInternallyFinite J := internallyFinite_subset
    (internallyFinite_of_cardLE_natural hk (CardLE.refl _)) hJk
  obtain ⟨l, hl, hJl⟩ := hJfin
  obtain ⟨h, hh, hhi, hhr⟩ := exists_bijection_of_cardEQ hJl.symm
  have hhk : h ∈ k ^ l := mem_function_of_mem_function_of_subset hh hJk
  have hhval : ∀ j ∈ l, h ‘ j ∈ J := fun j hj ↦ function_value_mem hh hj
  have hhω : ∀ j ∈ l, h ‘ j ∈ (ω : V) :=
    fun j hj ↦ IsTransitive.ω.transitive k hk _ (hJk _ (hhval j hj))
  have hrow : ∀ j ∈ l, kpair.π₁ (e ‘ (h ‘ j)) = i :=
    fun j hj ↦ ((mem_flattenRowIndices_iff _ _ _).mp (mem_inter_iff.mp (hhval j hj)).2).2
  let v := definableGraph (ω : V) (fun j ↦ w ‘ (h ‘ j)) (by definability)
  have hv : ∀ j ∈ l, v ‘ j = w ‘ (h ‘ j) := by
    intro j hj
    exact value_definableGraph _ _ _ (IsTransitive.ω.transitive l hl j hj)
  have hvsum := rationalFiniteSum_injective_identity hl hk hhk hhi hw hv
  rw [flattenIndexImage_eq_range hh, hhr] at hvsum
  have hmask : rationalPartialSum (rationalMaskedWeights w J) k =
      rationalPartialSum (rationalMaskedWeights w (flattenRowIndices e i)) k := by
    apply prefixCover_sum_congr_initial hk
    intro j hj
    have hjω := IsTransitive.ω.transitive k hk j hj
    rw [rationalMaskedWeights_value _ _ hjω, rationalMaskedWeights_value _ _ hjω]
    by_cases hrowj : j ∈ flattenRowIndices e i
    · simp [rationalMaskedTerm, J, hj, hrowj]
    · simp [rationalMaskedTerm, J, hj, hrowj]
  rw [← hmask, ← hvsum]
  let q := definableGraph l (fun j ↦ kpair.π₂ (e ‘ (h ‘ j))) (by definability)
  have hq : q ∈ N ^ l := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun j hj ↦ hcols _ (hJk _ (hhval j hj)))
  have hqv : ∀ j ∈ l, q ‘ j = kpair.π₂ (e ‘ (h ‘ j)) :=
    fun j hj ↦ value_definableGraph _ _ _ hj
  have hqi : Injective q := by
    intro a b z ha hb
    obtain ⟨hal, hza⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp ha
    obtain ⟨hbl, hzb⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hb
    have hsecond := hza.symm.trans hzb
    have hfirst := (hrow a hal).trans (hrow b hbl).symm
    have hab : e ‘ (h ‘ a) = e ‘ (h ‘ b) := by
      obtain ⟨r, hr, s, hs, hra⟩ := mem_prod_iff.mp (function_value_mem he (hhω a hal))
      obtain ⟨t, ht, u, hu, htb⟩ := mem_prod_iff.mp (function_value_mem he (hhω b hbl))
      rw [hra, htb]
      rw [hra, htb] at hfirst hsecond
      simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hfirst hsecond
      rw [hfirst, hsecond]
    exact injective_value_eq hh hhi hal hbl (injective_value_eq he hei (hhω a hal) (hhω b hbl) hab)
  apply rationalFiniteSum_injective_le hl hN hq hqi hu hupos
  intro j hj
  rw [hv j hj, hqv j hj]
  exact hmatch _ (hJk _ (hhval j hj)) (hrow j hj)

end ZFVP
