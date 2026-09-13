import ZFVP.ModelTheory.WoodinConstruction
import ZFVP.ModelTheory.WoodinDirectIndex

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- At a limit endpoint the increasing bounded cardinal table is cofinal. -/
theorem IsWoodinIteration.limitCardinal_eq_endpoint {δ s K : V} [IsOrdinal δ]
    (h : IsWoodinIteration δ δ s K) (hlim : ∀ i ∈ δ, succ i ∈ δ) :
    woodinLimitCardinal K = δ := by
  apply SetTheory.subset_antisymm
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := h.limitCardinal_cofinal hx
    exact IsOrdinal.toIsTransitive.mem_trans hxi (h.bounded i hi)
  · exact h.index_subset_limit hlim

/-- The actual endpoint recursion chooses the direct-limit branch. -/
theorem woodinIteration_endpoint_direct {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    woodinIterationRec δ = ⟨forcingDirectCode δ (woodinIterationPrefix δ),
      forcingFamilyNext δ (woodinIterationCardinalPrefix δ) δ⟩ₖ := by
  let := hδ.inaccessible.1
  have hlim : ∀ i ∈ δ, succ i ∈ δ :=
    fun _ hi ↦ regularCardinal_succ_closed hδ.inaccessible.regular hi
  have he := (woodinIterationExit hδ hAC).2.2.1.limitCardinal_eq_endpoint hlim
  have h0 : δ ≠ ∅ := by
    intro he
    exact not_mem_empty (he ▸ hδ.inaccessible.2.1)
  have hs : δ ≠ succ (⋃ˢ δ) := by
    intro he
    have hm : ⋃ˢ δ ∈ δ := (congrArg (fun x : V ↦ (⋃ˢ δ) ∈ x) he).mpr (mem_succ_self (⋃ˢ δ))
    have hn := hlim _ hm
    rw [← he] at hn
    exact mem_irrefl _ hn
  have hi : IsChoicelessInaccessible
      (woodinLimitCardinal (woodinIterationCardinalPrefix δ)) := he.symm ▸ hδ.inaccessible
  simpa only [he] using woodinIterationRec_direct h0 hs hi

/-- The cardinal assigned to this direct endpoint is literally the endpoint. -/
theorem woodinIteration_endpoint_cardinal {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    (kpair.π₂ (woodinIterationRec δ)) ‘ δ = δ := by
  rw [woodinIteration_endpoint_direct hδ hAC, kpair.π₂_kpair]
  exact forcingFamilyNext_new _ _ _

/-- Increasing the outer bound leaves every forcing and cardinal unchanged. -/
theorem IsWoodinIteration.enlarge_bound {δ ε θ s K : V}
    (h : IsWoodinIteration δ θ s K) (hδε : δ ⊆ ε) : IsWoodinIteration ε θ s K :=
  ⟨h.code, h.cardinals, h.stage, h.small, h.inaccessible,
    fun i hi ↦ hδε _ (h.bounded i hi), h.increasing⟩

/-- Validity and closure include the endpoint itself. The outer bound is enlarged
only to accommodate its cardinal, which is equal to the original endpoint. -/
theorem woodinIteration_endpoint_valid {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    IsWoodinIteration (succ δ) (succ δ) (kpair.π₁ (woodinIterationRec δ))
      (kpair.π₂ (woodinIterationRec δ)) ∧
    HasWoodinQuotientClosure (succ δ) (kpair.π₁ (woodinIterationRec δ))
      (kpair.π₂ (woodinIterationRec δ)) := by
  let := hδ.inaccessible.1
  have h := (woodinIterationExit hδ hAC).2.2.1
  have hc := (woodinIterationExit hδ hAC).2.2.2
  have hlim : ∀ i ∈ δ, succ i ∈ δ :=
    fun _ hi ↦ regularCardinal_succ_closed hδ.inaccessible.regular hi
  have he := h.limitCardinal_eq_endpoint hlim
  have h0 : (∅ : V) ∈ δ := IsOrdinal.toIsTransitive.mem_trans (by simp) hδ.inaccessible.2.1
  have hi : IsChoicelessInaccessible
      (woodinLimitCardinal (woodinIterationCardinalPrefix δ)) := he.symm ▸ hδ.inaccessible
  have hv := (h.enlarge_bound (show δ ⊆ succ δ from fun _ hx ↦ mem_succ_iff.mpr (Or.inr hx))).direct_of_limit_below
    hc (he.symm ▸ mem_succ_self δ) h0 hlim hi
  have hcl := hc.direct h hlim hi h0
  rw [woodinIteration_endpoint_direct hδ hAC, kpair.π₁_kpair, kpair.π₂_kpair]
  exact ⟨by simpa only [he] using hv, by simpa only [he] using hcl⟩

end ZFVP
