import ZFVP.ModelTheory.LevyRangeCover
import ZFVP.ModelTheory.GroundApproximation
import ZFVP.ModelTheory.GroundCover
import ZFVP.SetTheory.RankBounds
import ZFVP.SetTheory.RegularUnions
import ZFVP.SetTheory.FiniteCardinalArithmetic
import ZFVP.SetTheory.GroundUniqueness

/-! The rank stages of the ground model inside the Levy extension. In the extension by the Levy
collapse of a measurable `κ`, the check of a rank stage `V_λ` of the ground model is transitive,
closed under intersections, and has the cover and approximation properties for subsets of `θ̌`
with respect to `δ = (κ⁺)ˇ`, where `θ` and `κ` lie below the limit ordinal `λ`. These are the
hypotheses of Laver's uniqueness lemma. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A subset of a member of a rank stage is a member of that stage. -/
theorem mem_hierarchy_of_subset {lam x C : V} [IsOrdinal lam] (hC : C ∈ hierarchy lam)
    (h : x ⊆ C) : x ∈ hierarchy lam := by
  have hrC : rank C ∈ lam := (mem_hierarchy_iff_rank_mem C lam).mp hC
  have : IsOrdinal (rank x) := (rank_spec x).1
  have : IsOrdinal (rank C) := (rank_spec C).1
  rcases IsOrdinal.subset_iff.mp (rank_mono h) with he | hlt
  · exact (mem_hierarchy_iff_rank_mem x lam).mpr (he ▸ hrC)
  · exact (mem_hierarchy_iff_rank_mem x lam).mpr
      (IsOrdinal.toIsTransitive.transitive _ hrC _ hlt)

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hU hc hω hκ in
/-- Every condition of the full Levy collapse already lies in a subcollapse below `κ`. -/
theorem levyCollapse_mem_stage {p : V} (hp : p ∈ levyCollapse κ) :
    ∃ β ∈ κ, p ∈ levyCollapse β := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  obtain ⟨n, hn, heq⟩ := ordinalSupport_finite hp
  have hnκ : n ∈ κ := IsOrdinal.toIsTransitive.transitive _ hω n hn
  obtain ⟨ξ, hξ, hsub⟩ :=
    regular_small_subset_bounded hreg (ordinalSupport_subset hp) hnκ heq.1
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  refine ⟨ξ, hξ, ?_⟩
  have h := levyCut_mem (β := ξ) hp
  rwa [levyCut_eq_of_support hp hsub] at h

include hAC hU hc hω hκ in
/-- Below a measurable, the full Levy collapse has size at most `κ`. -/
theorem levyCollapse_cardLE_self : levyCollapse κ ≤# κ := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hgd : domain (definableGraph κ (levyCollapse : V → V) inferInstance) = κ :=
    domain_definableGraph _ _ _
  have hsub : levyCollapse κ ⊆
      ⋃ˢ range (definableGraph κ (levyCollapse : V → V) inferInstance) := by
    intro p hp
    obtain ⟨β, hβ, hpβ⟩ := levyCollapse_mem_stage hU hc hω hκ hp
    refine mem_sUnion_iff.mpr ⟨levyCollapse β, ?_, hpβ⟩
    rw [range_definableGraph]
    exact (repl_spec _).mpr ⟨β, hβ, rfl⟩
  refine (cardLE_of_subset hsub).trans ?_
  refine sUnion_range_cardLE_of_regular hAC hreg hgd (cardLE_of_subset (fun x hx ↦ hx)) ?_
  intro ξ hξ
  rw [value_definableGraph _ _ _ hξ]
  obtain ⟨μ, hμ, hle⟩ := levyCollapse_small hAC hU hc hω hκ hξ
  exact hle.trans (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive μ hμ))

include hU hc hω hκ in
/-- The full Levy collapse has at least `κ` conditions. -/
theorem cardLE_levyCollapse : κ ≤# levyCollapse κ := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hF : ℒₛₑₜ-function₁ (fun x : V ↦ ({⟨⟨(∅ : V), succ x⟩ₖ, x⟩ₖ} : V)) := by definability
  refine cardLE_of_injective_map _ hF ?_ ?_
  · intro α hα
    have hαo : IsOrdinal α := IsOrdinal.of_mem hα
    have hs : succ α ∈ κ := regularCardinal_succ_closed hreg hα
    have hins := levyCollapse_insert (κ := κ) (empty_mem_levyCollapse κ) empty_mem_ω hs
      (mem_succ_self α) (fun δ h ↦ not_mem_empty h)
    have he : ({⟨⟨(∅ : V), succ α⟩ₖ, α⟩ₖ} : V) = insert ⟨⟨(∅ : V), succ α⟩ₖ, α⟩ₖ ∅ := by
      apply mem_ext
      intro z
      rw [mem_singleton_iff, mem_insert]
      exact ⟨Or.inl, fun h ↦ h.elim id (fun h ↦ (not_mem_empty h).elim)⟩
    rw [he]
    exact hins
  · intro α hα β hβ h
    have hmem : ⟨⟨(∅ : V), succ α⟩ₖ, α⟩ₖ ∈ ({⟨⟨(∅ : V), succ β⟩ₖ, β⟩ₖ} : V) := by
      rw [← h]
      exact mem_singleton_iff.mpr rfl
    exact (kpair_inj (mem_singleton_iff.mp hmem)).2

end

/-- An injection witnessing `y ≤# ν` can be found inside a limit rank stage holding `y` and
`ν`. -/
theorem exists_injection_mem_hierarchy {lam y ν : V} [IsOrdinal lam]
    (hlim : ∀ β ∈ lam, succ β ∈ lam) (hy : y ∈ hierarchy lam) (hν : ν ∈ hierarchy lam)
    (h : y ≤# ν) : ∃ g ∈ hierarchy lam, g ∈ ν ^ y ∧ Injective g := by
  obtain ⟨g, hg, hinj⟩ := h
  refine ⟨g, mem_hierarchy_of_subset (prod_mem_hierarchy_limit hlim hy hν)
    (fun z hz ↦ subset_prod_of_mem_function hg z hz), hg, hinj⟩

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- A set of size at most `|P × P|` has size at most `κ`. -/
theorem levy_prod_cardLE {y : V} (h : y ≤# levyCollapse κ ×ˢ levyCollapse κ) : y ≤# κ := by
  have hP := levyCollapse_cardLE_self hAC hU hc hω hκ
  have h2 : levyCollapse κ ×ˢ levyCollapse κ ≤# κ ×ˢ κ := prod_cardLE_prod hP hP
  have h3 : κ ×ˢ κ ≤# κ ∪ (ω : V) := ordinal_prod_cardLE_union_omega κ
  rw [ordinal_union_omega_eq (IsOrdinal.toIsTransitive.transitive _ hω)] at h3
  exact (h.trans h2).trans h3

include hU hc hω hκ in
/-- An element of the checked Hartogs number of `κ` is injected by `κ̌`, hence by the checked
forcing. -/
theorem levy_check_hartogs_cardLE_poset {μ : (levyContext κ hG).Model}
    (hμ : μ ∈ (levyContext κ hG).check (hartogsNumber κ)) :
    μ ≤# (levyContext κ hG).check (levyCollapse κ) := by
  obtain ⟨μ₀, hμ₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hμ
  exact (levyContext κ hG).checkEmbedding.map_cardLE
    ((cardLE_of_mem_hartogsNumber hμ₀).trans (cardLE_levyCollapse hU hc hω hκ))

variable {θ lam : V} [IsOrdinal lam]

/-- The check of a rank stage is closed under intersections. -/
theorem levy_stage_interClosed :
    InterClosed ((levyContext κ hG).check (hierarchy lam)) := by
  intro x hx y hy
  obtain ⟨x₀, hx₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hy
  rw [← (levyContext κ hG).check_inter]
  exact ((levyContext κ hG).check_mem_iff _ _).mpr
    (mem_hierarchy_of_subset hx₀ (fun z hz ↦ (mem_inter_iff.mp hz).1))

/-- The check of a rank stage is transitive. -/
theorem levy_stage_transitive :
    IsTransitive ((levyContext κ hG).check (hierarchy lam)) := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨x₀, hx₀, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hx
  exact ((levyContext κ hG).checkEmbedding.subset_iff _ _).mpr
    ((hierarchy_transitive lam).transitive x₀ hx₀)

include hAC hU hc hω hκ in
/-- The `δ`-cover property of the checked rank stage for subsets of `θ̌`, with
`δ = (κ⁺)ˇ`. -/
theorem levy_stage_hasSmallCover (hlim : ∀ β ∈ lam, succ β ∈ lam) (hθ : θ ∈ lam)
    (hκlam : κ ∈ lam) :
    HasSmallCover ((levyContext κ hG).check (hierarchy lam))
      ((levyContext κ hG).check (hartogsNumber κ)) ((levyContext κ hG).check θ) := by
  have hθH : θ ∈ hierarchy lam := ordinal_subset_hierarchy lam θ hθ
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
`δ = (κ⁺)ˇ`. -/
theorem levy_stage_hasApproximation (hlim : ∀ β ∈ lam, succ β ∈ lam) (hθ : θ ∈ lam)
    (hκlam : κ ∈ lam) :
    HasApproximation ((levyContext κ hG).check (hierarchy lam))
      ((levyContext κ hG).check (hartogsNumber κ)) ((levyContext κ hG).check θ) := by
  have hθH : θ ∈ hierarchy lam := ordinal_subset_hierarchy lam θ hθ
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

end

end ZFVP
