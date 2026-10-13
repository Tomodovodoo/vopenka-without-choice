module

public import ZFVP.SetTheory.SupercompactUltrapower
public import ZFVP.SetTheory.HartogsRegularChoice
public import ZFVP.SetTheory.ChoicelessInaccessibleRank
public import ZFVP.ModelTheory.LimitRankCriticalPoint

@[expose] public section

/-! Measure supercompactness gives inaccessibility through a rank-stage ultrapower. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsSupercompact.inaccessible {κ : V} (h : IsSupercompact κ)
    (hAC : InternalChoice V) : IsChoicelessInaccessible κ := by
  let := h.isOrdinal
  have hκθ : κ ∈ hartogsNumber κ := ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl κ)
  have hωκ : (ω : V) ⊆ κ := IsOrdinal.toIsTransitive.transitive _ h.2.1
  have hθ := hartogsNumber_regular hAC (cardLE_of_subset hωκ)
  obtain ⟨M, j, hM, _, hj, hcrit, _⟩ := supercompact_ultrapower_stage hAC h
    h.isOrdinal (subset_refl κ) (hωκ _ (by simp)) hθ hκθ hκθ
  let := hM
  apply limitRankEmbedding_criticalPoint_inaccessible
    (fun _ hβ ↦ regularCardinal_succ_closed hθ hβ) hj hcrit
  exact ordinal_mem_hierarchy_iff.mpr
    (IsOrdinal.toIsTransitive.mem_trans h.2.1 hκθ)

theorem IsSupercompact.regular {κ : V} (h : IsSupercompact κ)
    (hAC : InternalChoice V) : IsRegularCardinal κ :=
  (h.inaccessible hAC).regular

end ZFVP
