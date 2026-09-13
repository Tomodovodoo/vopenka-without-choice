import ZFVP.ModelTheory.WoodinSparseSuccessor
import ZFVP.ModelTheory.WoodinSparseRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω k Q T m : V} [IsOrdinal k]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
variable (hm : ∀ i ∈ succ k, IsForcingIsomorphism
  ((forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode (succ k))) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T)
variable (hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k))

local notation "c" => forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m
local notation "δ" => woodinNormalizedSuccessorCutoff k

include hΩ hAC hk hm hT hQt hTt hQrank

theorem woodinSparseSuccessorCarrier_subset_hierarchy :
    woodinSparseSuccessorCarrier k c ⊆ hierarchy δ := by
  have he := woodinRecodedSuccessorCutoff_eq (k := k) (Q := Q) (T := T) (m := m)
    hΩ hAC hk hm hT hQt hTt
  obtain ⟨hd, _⟩ := woodinNormalizedSuccessorCutoff_bounds hΩ hAC hk
  let := hd.1
  unfold woodinSparseSuccessorCarrier woodinSparseSuccessorPool
  dsimp only
  rw [← he]
  apply sparsePairCarrier_subset_hierarchy hd.rankCriterion.2.2.1
    (ordinal_mem_hierarchy_iff.mpr (woodinSparseSuccessorCoordinate_mem hΩ hAC hk))
  · have hp : (forcingCodeP c) ‘ k ∈ hierarchy δ := by
      simpa only [forcingRecodedCode, forcingCodeP_code] using hQrank
    exact (hierarchy_transitive δ).transitive _ hp
  · exact sep_subset

theorem woodinSparseSuccessorCarrier_small {ξ : V}
    (hξ : IsChoicelessInaccessible ξ) (hδξ : (kpair.π₂ (woodinIterationRec (succ k))) ‘ (succ k) ∈ ξ) :
    woodinSparseSuccessorCarrier k c ∈ hierarchy ξ := by
  let := hξ.1
  obtain ⟨hd, _⟩ := woodinNormalizedSuccessorCutoff_bounds hΩ hAC hk
  let := hd.1
  apply subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 ?_
    (woodinSparseSuccessorCarrier_subset_hierarchy hΩ hAC hk hm hT hQt hTt hQrank)
  rw [mem_hierarchy_iff_rank_mem, rank_hierarchy, woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hk]
  exact hδξ

end ZFVP
