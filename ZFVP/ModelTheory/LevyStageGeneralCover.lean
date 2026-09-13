import ZFVP.ModelTheory.LevyGroundStages
import ZFVP.ModelTheory.GroundCoverGeneral
import ZFVP.SetTheory.Hessenberg

/-! Cover and approximation for checks of arbitrary members of a rank stage.

`LevyGroundStages` proves the cover and approximation properties of `(V_λ)ˇ` for subsets of `θ̌`
under the hypothesis `θ ∈ λ`. The proofs never use more than `θ ∈ V_λ`, so the same statements hold
with that weaker hypothesis and apply to sets that are not ordinals, for instance `λ ×ˢ λ`.

This file also proves the bounded cover property: a subset of `θ̌` of size at most `(κ⁺)ˇ` is
contained in a set of `(V_λ)ˇ` that injects into `(κ⁺)ˇ` itself, not merely into a member of it.
That is the form Laver's uniqueness argument needs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  {θ lam : V} [IsOrdinal lam]

include hAC hU hc hω hκ in
/-- The `δ`-cover property of the checked rank stage for subsets of `θ̌`, with `δ = (κ⁺)ˇ`, for
any `θ` in the stage rather than only for ordinals below `λ`. -/
theorem levy_stage_hasSmallCover_of_mem (hlim : ∀ β ∈ lam, succ β ∈ lam)
    (hθ : θ ∈ hierarchy lam) (hκlam : κ ∈ lam) :
    HasSmallCover ((levyContext κ hG).check (hierarchy lam))
      ((levyContext κ hG).check (hartogsNumber κ)) ((levyContext κ hG).check θ) := by
  have hθH : θ ∈ hierarchy lam := hθ
  have hκH : κ ∈ hierarchy lam := ordinal_subset_hierarchy lam κ hκlam
  intro A hA hsmall
  obtain ⟨μ, hμ, hAμ⟩ := hsmall
  have hAP : A ≤# (levyContext κ hG).check (levyContext κ hG).P :=
    hAμ.trans (levy_check_hartogs_cardLE_poset hU hc hω hκ hG hμ)
  obtain ⟨y, hyθ, hyP, hAy⟩ := (levyContext κ hG).cover hAC θ hA hAP
  have hyκ : y ≤# κ := levy_prod_cardLE hAC hU hc hω hκ hyP
  have hyH : y ∈ hierarchy lam := mem_hierarchy_of_subset hθH hyθ
  obtain ⟨g, hgH, hgf, hginj⟩ := exists_injection_mem_hierarchy hlim hyH hκH hyκ
  refine ⟨(levyContext κ hG).check y, ((levyContext κ hG).check_mem_iff _ _).mpr hyH, hAy,
    ((levyContext κ hG).checkEmbedding.subset_iff _ _).mpr hyθ, ?_⟩
  refine ⟨(levyContext κ hG).check κ, ((levyContext κ hG).check_mem_iff _ _).mpr
    (ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl κ)),
    (levyContext κ hG).check y, ((levyContext κ hG).check_mem_iff _ _).mpr hyH,
    subset_refl _, (levyContext κ hG).check g,
    ((levyContext κ hG).check_mem_iff _ _).mpr hgH, ?_, ?_⟩
  · exact ((levyContext κ hG).checkEmbedding.function_iff g y κ).mpr hgf
  · exact ((levyContext κ hG).checkEmbedding.injective_iff g).mpr hginj

include hAC hU hc hω hκ in
/-- The `δ`-approximation property of the checked rank stage for subsets of `θ̌`, with
`δ = (κ⁺)ˇ`, for any `θ` in the stage rather than only for ordinals below `λ`. -/
theorem levy_stage_hasApproximation_of_mem (hlim : ∀ β ∈ lam, succ β ∈ lam)
    (hθ : θ ∈ hierarchy lam) (hκlam : κ ∈ lam) :
    HasApproximation ((levyContext κ hG).check (hierarchy lam))
      ((levyContext κ hG).check (hartogsNumber κ)) ((levyContext κ hG).check θ) := by
  have hθH : θ ∈ hierarchy lam := hθ
  have hκH : κ ∈ hierarchy lam := ordinal_subset_hierarchy lam κ hκlam
  intro A hA hint
  have hkey : ∀ x ∈ smallSubsets θ (levyContext κ hG).P, ∃ B : V, B ⊆ θ ∧
      A ∩ (levyContext κ hG).check x = (levyContext κ hG).check B := by
    intro x hx
    obtain ⟨hxθ, hxP⟩ := (mem_smallSubsets_iff _ _ _).mp hx
    have hxκ : x ≤# κ := hxP.trans (levyCollapse_cardLE_self hAC hU hc hω hκ)
    have hxH : x ∈ hierarchy lam := mem_hierarchy_of_subset hθH hxθ
    obtain ⟨g, hgH, hgf, hginj⟩ := exists_injection_mem_hierarchy hlim hxH hκH hxκ
    have hxsub : (levyContext κ hG).check x ⊆ (levyContext κ hG).check θ :=
      ((levyContext κ hG).checkEmbedding.subset_iff _ _).mpr hxθ
    have hmem := hint ((levyContext κ hG).check x)
      (((levyContext κ hG).check_mem_iff _ _).mpr hxH) hxsub
      ⟨(levyContext κ hG).check κ, ((levyContext κ hG).check_mem_iff _ _).mpr
        (ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl κ)),
        (levyContext κ hG).check x, ((levyContext κ hG).check_mem_iff _ _).mpr hxH,
        subset_refl _, (levyContext κ hG).check g,
        ((levyContext κ hG).check_mem_iff _ _).mpr hgH,
        ((levyContext κ hG).checkEmbedding.function_iff g x κ).mpr hgf,
        ((levyContext κ hG).checkEmbedding.injective_iff g).mpr hginj⟩
    obtain ⟨B₀, hB₀, heq⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hmem
    have hsub : (levyContext κ hG).check B₀ ⊆ (levyContext κ hG).check θ := by
      rw [← heq]
      exact fun z hz ↦ hxsub z (mem_inter_iff.mp hz).2
    exact ⟨B₀, ((levyContext κ hG).checkEmbedding.subset_iff B₀ θ).mp hsub, heq⟩
  obtain ⟨B₁, hB₁θ, rfl⟩ := (levyContext κ hG).approximation hAC θ hA hkey
  exact ((levyContext κ hG).check_mem_iff _ _).mpr (mem_hierarchy_of_subset hθH hB₁θ)

include hAC hU hc hω hκ in
/-- The bounded cover property: a subset of `θ̌` of size at most `(κ⁺)ˇ` sits inside a set of the
checked rank stage that injects into `(κ⁺)ˇ` itself, by an injection in the stage. -/
theorem levy_stage_boundedCover (hlim : ∀ β ∈ lam, succ β ∈ lam) (hθ : θ ∈ hierarchy lam)
    (hHlam : hartogsNumber κ ∈ lam)
    {A : (levyContext κ hG).Model} (hA : A ⊆ (levyContext κ hG).check θ)
    (hcard : A ≤# (levyContext κ hG).check (hartogsNumber κ)) :
    MBounded ((levyContext κ hG).check (hierarchy lam))
      ((levyContext κ hG).check (hartogsNumber κ)) A := by
  obtain ⟨y, hyθ, hyP, hAy⟩ :=
    (levyContext κ hG).cover_of_cardLE hAC θ (hartogsNumber κ) hA hcard
  -- the Hartogs number of `κ` is an initial ordinal containing `ω` and `κ`
  have hHinit : IsInitialOrdinal (hartogsNumber κ) := hartogsNumber_initial κ
  have : IsOrdinal (hartogsNumber κ) := hHinit.1
  have hκH : κ ∈ hartogsNumber κ :=
    ordinal_cardLE_iff_mem_hartogsNumber.mp (CardLE.refl κ)
  have hκsub : κ ⊆ hartogsNumber κ :=
    IsOrdinal.toIsTransitive.transitive _ hκH
  have hωH : (ω : V) ⊆ hartogsNumber κ :=
    IsOrdinal.toIsTransitive.transitive _ (hκsub _ hω)
  -- so the Levy poset, its square, and `κ⁺ ×ˢ (P ×ˢ P)` all have size at most `κ⁺`
  have hPH : levyCollapse κ ≤# hartogsNumber κ :=
    (levyCollapse_cardLE_self hAC hU hc hω hκ).trans (cardLE_of_subset hκsub)
  have hPPH : levyCollapse κ ×ˢ levyCollapse κ ≤# hartogsNumber κ :=
    prod_cardLE_of_cardLE_initial hHinit hωH hPH hPH
  have hyH : y ≤# hartogsNumber κ :=
    hyP.trans (prod_cardLE_of_cardLE_initial hHinit hωH (CardLE.refl _) hPPH)
  -- and `y` together with the injection lives in the rank stage
  have hymem : y ∈ hierarchy lam := mem_hierarchy_of_subset hθ hyθ
  have hHmem : hartogsNumber κ ∈ hierarchy lam := ordinal_subset_hierarchy lam _ hHlam
  obtain ⟨g, hgH, hgf, hginj⟩ := exists_injection_mem_hierarchy hlim hymem hHmem hyH
  exact ⟨(levyContext κ hG).check y, ((levyContext κ hG).check_mem_iff _ _).mpr hymem, hAy,
    (levyContext κ hG).check g, ((levyContext κ hG).check_mem_iff _ _).mpr hgH,
    ((levyContext κ hG).checkEmbedding.function_iff g y (hartogsNumber κ)).mpr hgf,
    ((levyContext κ hG).checkEmbedding.injective_iff g).mpr hginj⟩

end

end ZFVP
