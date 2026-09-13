import ZFVP.ModelTheory.WoodinInverseFirstCoordinates
import ZFVP.ModelTheory.WoodinDirectTailSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinDirect_lift_value {δ θ j i a b : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (ha : a ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i) :
    ((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ =
      forcingThreadSplice j (forcingCodeπ (woodinIterationPrefix j))
        (forcingCodeL (woodinIterationPrefix j)) a i b := by
  let := IsOrdinal.of_mem hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hrec := woodinIterationRec_direct h0 hlim hinac
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hc := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hb' : b ∈ (forcingCodeP (woodinIterationPrefix j)) ‘ i := by
    rw [hc.tableP.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableP
      (woodinIterationPrefix_extends hsub).subP hi]
    exact hb
  have ha' := ha
  rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair] at ha'
  simp only [forcingDirectCode, forcingThreadCode_poset] at ha'
  rw [woodinIterationPrefix_lift_value hs hj (mem_succ_iff.mpr (Or.inr hi))
    (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeL_code,
    forcingMatrixNext_column hi, forcingLimitLiftColumn_value hi, forcingLimitLift_value ha' hb']

theorem woodinDirect_projection_value {δ θ j k a : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l))) (hj : j ∈ θ) (hk : k ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (ha : a ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, j⟩ₖ) ‘ a = a ‘ k := by
  let := IsOrdinal.of_mem hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hk
  have hrec := woodinIterationRec_direct h0 hlim hinac
  rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self _), hrec, kpair.π₁_kpair] at ha
  simp only [forcingDirectCode, forcingThreadCode_poset] at ha
  rw [woodinIterationPrefix_projection_value hs hj (mem_succ_iff.mpr (Or.inr hk))
    (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hk, forcingLimitProjectionColumn_value hk]
  exact forcingThreadCoordinate_value ha

end ZFVP
