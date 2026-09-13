import ZFVP.SetTheory.WeaklyLSNoSmallCofinality
import ZFVP.SetTheory.SuccessorRegularityCriterion
import ZFVP.SetTheory.RankDomainCofinality

/-! Usuba Theorem 1.2(1): the successor of a singular weakly LS cardinal is
regular, and the rank Vκ cannot map cofinally into that successor. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWeaklyLSCardinal.singular_successor_regular {κ : V}
    (hκ : IsWeaklyLSCardinal κ) (hsing : internalCofinality κ ∈ κ) :
    IsRegularCardinal (hartogsNumber κ) := by
  let := hκ.1.1
  exact hartogsNumber_regular_of_singular_no_small_cofinalMap
    (IsOrdinal.toIsTransitive.transitive _ hκ.2.1) hsing
    (fun x hx f ↦ hκ.no_small_cofinalMap hx (subset_refl κ) hκ.1)

theorem IsWeaklyLSCardinal.singular_no_rank_cofinalMap {κ f : V}
    (hκ : IsWeaklyLSCardinal κ) (hsing : internalCofinality κ ∈ κ) :
    ¬IsCofinalMap (hartogsNumber κ) (hierarchy κ) f := by
  let := hκ.1.1
  exact no_hierarchy_cofinalMap_of_small_bounds (hκ.singular_successor_regular hsing)
    (ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl κ))
    (fun β hβ ↦ initial_succ_mem hκ.1 (IsOrdinal.toIsTransitive.transitive _ hκ.2.1) hβ)
    (fun β hβ f ↦ hκ.no_small_cofinalMap (hierarchy_mem hβ) (subset_refl κ) hκ.1) f

end ZFVP
