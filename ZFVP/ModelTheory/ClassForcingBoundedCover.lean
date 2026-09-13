import ZFVP.ModelTheory.ClassForcingRefinementExtraction
import ZFVP.ModelTheory.ClassForcingQuotientWitnesses

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

/-- An internal bound for witnesses along an enumeration gives a ground
condition and a checked-table cover. A raw common extension with the initial
condition makes the resulting class comparison literal. -/
theorem boundedQuotient_cover_from_enumerated_bounds
    (A : ForcingContext V) {I i k c : V} [IsOrdinal i] [IsOrdinal k]
    (hP : A.P = T.P i) (hik : i ⊆ k)
    (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    {α e f q : A.Model}
    (he : e ∈ (A.check I) ^ α) (her : range e = A.check I)
    (hf : f ∈ (T.boundedQuotient A i k) ^ α)
    (hfD : ∀ β ∈ α,
      f ‘ β ∈ (A.check (T.boundedDenseFamily D hDdef I k)) ‘ (e ‘ β))
    (hq : q ∈ T.boundedQuotient A i k)
    (hqc : ⟨q, A.check c⟩ₖ ∈
      forcingSeparativeOrder (T.boundedQuotient A i k) (T.boundedQuotientOrder A i k))
    (hqf : ∀ β ∈ α, ⟨q, f ‘ β⟩ₖ ∈
      forcingSeparativeOrder (T.boundedQuotient A i k) (T.boundedQuotientOrder A i k)) :
    ∃ p ∈ T.P k, T.LE ⟨k, p⟩ₖ c ∧ (T.projection i k) ‘ p ∈ A.G ∧
      HasBoundedDenseQuotientCover
        (A.projectionQuotient (T.P k) (T.projection i k))
        (A.projectionQuotientOrder (T.P k) (T.R k) (T.projection i k))
        (A.check I) (A.check (T.boundedDenseFamily D hDdef I k))
        (A.check (T.boundedReduction k)) (A.check p) := by
  let X := T.boundedQuotient A i k
  let R := T.boundedQuotientOrder A i k
  have hR : IsForcingPreorder X R := T.boundedQuotient_preorder A hP
  have hS := forcingSeparativeOrder_preorder hR
  have hπ : T.boundedProjection i k ∈ A.P ^ (T.boundedConditions k) := by
    rw [hP]
    exact T.boundedProjection_maps i k
  have hE := T.boundedReduction_maps k
  let := IsFunction.of_mem he
  let := IsFunction.of_mem hE
  obtain ⟨u, hu, huq, huc⟩ := forcingSeparativeOrder_compatible hR hqc
  obtain ⟨b, hb, _, hub⟩ := (A.mem_projectionQuotient_iff hπ u).mp hu
  have hbQ : A.check b ∈ X := hub ▸ hu
  have hbG := ((T.check_mem_boundedQuotient_iff A hP).mp hbQ).2
  have hbc : T.LE b c := by
    rw [hub] at huc
    have hh := ((A.projectionQuotientOrder_pair_iff _ _ _ _ _).mp huc).1
    rw [← A.check_kpair, A.check_mem_iff] at hh
    exact ((T.pair_mem_boundedOrder k b c).mp hh).2.2
  let p := T.reduceCondition k b
  refine ⟨p, T.reduceCondition_mem hb,
    T.le_trans (T.reduceCondition_equivalent hb).1 hbc, ?_, ?_⟩
  · change (T.projection i k) ‘ (T.reduceCondition k b) ∈ A.G
    rwa [T.boundedProjection_reduce hik hb]
  · intro a ha
    obtain ⟨β, hβe⟩ := mem_range_iff.mp (her.symm ▸ ha)
    have hβα : β ∈ α := domain_eq_of_mem_function he ▸ mem_domain_of_kpair_mem hβe
    have heβ : e ‘ β = a := value_eq_of_kpair_mem hβe
    have hfv := function_value_mem hf hβα
    have hfd := hfD β hβα
    rw [heβ] at hfd
    obtain ⟨d, hd, _, hdf⟩ := (A.mem_projectionQuotient_iff hπ (f ‘ β)).mp hfv
    have hdQ : A.check d ∈ X := hdf ▸ hfv
    have hus : ⟨u, q⟩ₖ ∈ forcingSeparativeOrder X R := forcingOrder_subset_separative hR _ huq
    have huf := hS.2.2 u hu q hq (f ‘ β) hfv hus (hqf β hβα)
    rw [hub, hdf] at huf
    have hred := (T.boundedQuotient_checked_separative_iff A hP hik hb hd hbQ hdQ).mp huf
    refine ⟨f ‘ β, hfd, ?_⟩
    rw [hdf, A.check_value ((domain_eq_of_mem_function hE).symm ▸ hd), T.boundedReduction_value hd]
    exact hred

end DefinableForcingTower
end ZFVP
