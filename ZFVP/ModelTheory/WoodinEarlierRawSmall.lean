import ZFVP.ModelTheory.WoodinInverseFirstCoordinates
import ZFVP.ModelTheory.WoodinInverseSourceCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinEarlierRaw_cutoff_data {δ θ j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (h0 : j ≠ ∅)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j))) :
    let s := woodinIterationPrefix j
    let γ := woodinLimitCardinal (woodinIterationCardinalPrefix j)
    let c := forcingInverseSourceCutoff j s γ
    γ ∈ c ∧ IsChoicelessInaccessible c ∧ forcingInverseCodePoset j s ∈ hierarchy c := by
  let := IsOrdinal.of_mem hj
  have h := woodinIterationPrefix_of_stages
    (fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj))
  let := h.limitCardinal_ordinal
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix j)
  let c := forcingInverseSourceCutoff j (woodinIterationPrefix j) γ
  have hrec := woodinIterationRec_inverse h0 hlim hinac
  have hnew : (kpair.π₂ (woodinIterationRec j)) ‘ j = c := by
    rw [hrec, kpair.π₂_kpair]
    simp only [woodinInverseCardinalNext, forcingFamilyNext_new, c, γ]
  have hci : IsChoicelessInaccessible c := hnew ▸ (hs j hj).inaccessible j (mem_succ_self j)
  have hγc : γ ∈ c := by
    have hsub : γ ⊆ c := by
      intro x hx
      obtain ⟨k, hk, hxk⟩ := h.limitCardinal_cofinal hx
      have hkc := (hs j hj).increasing k (mem_succ_iff.mpr (Or.inr hk)) j (mem_succ_self j) hk
      rw [hnew, hrec, kpair.π₂_kpair] at hkc
      simp only [woodinInverseCardinalNext, forcingFamilyNext_old hk] at hkc
      exact hci.1.toIsTransitive.mem_trans hxk hkc
    rcases IsOrdinal.subset_iff.mp hsub with he | hlt
    · have hh : IsChoicelessInaccessible γ := he.symm ▸ hci
      exact (hinac hh).elim
    · exact hlt
  exact ⟨hγc, hci, (h.inverse_small_above_limit (ordinal_limit_of_not_successor hlim) hci hγc).1⟩

end ZFVP
