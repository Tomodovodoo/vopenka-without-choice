import ZFVP.ModelTheory.LevyGroundStageLike
import ZFVP.SetTheory.ClosedRankStages
import ZFVP.SetTheory.GroundLikeFormulas

/-! Choosing the rank stage used by the ground model definability argument.

The coding argument needs a stage `hierarchy lam` of the ground model that holds a given finite
list of parameters, is closed under successor and under `β ↦ hartogsNumber (hierarchy β)`, and
whose check computes the power sets of `(κ⁺)ˇ` and of `(κ⁺)ˇ ×ˢ (κ⁺)ˇ` correctly.

`exists_closed_stage_containing` is the plain set-theoretic half: above any set there is a closed
stage containing all of its members. `exists_levy_good_stage` adds the four parameters of the Levy
argument. The remaining three theorems record what such a stage gives: the two parameter
agreements of the uniqueness lemma, and the ground-like property in the flat form
`IsGroundLike`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An ordinal that lies in a rank stage lies in the index of that stage. -/
theorem ordinal_mem_of_mem_hierarchy {lam α : V} [IsOrdinal lam] [IsOrdinal α]
    (h : α ∈ hierarchy lam) : α ∈ lam := by
  have hr := (mem_hierarchy_iff_rank_mem α lam).mp h
  rwa [rank_of_ordinal α] at hr

/-- Every set sits inside a rank stage whose index is closed under successor and under
`β ↦ hartogsNumber (hierarchy β)`. -/
theorem exists_closed_stage_containing (s : V) :
    ∃ lam : V, IsOrdinal lam ∧ (∀ β ∈ lam, succ β ∈ lam) ∧
      (∀ β ∈ lam, hartogsNumber (hierarchy β) ∈ lam) ∧ ∀ y ∈ s, y ∈ hierarchy lam := by
  obtain ⟨lam, hlamO, hγ, hsucc, hclosed⟩ := exists_closed_limit_ordinal (succ (rank s))
  have := hlamO
  refine ⟨lam, hlamO, hsucc, hclosed, ?_⟩
  intro y hy
  have hrs : rank s ∈ lam := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self _) hγ
  have hry : rank y ∈ lam := IsOrdinal.toIsTransitive.mem_trans (rank_mem hy) hrs
  exact (mem_hierarchy_iff_rank_mem y lam).mpr hry

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- A closed rank stage holding the members of `s`, the ordinals `κ` and `κ⁺`, and the two power
sets the coding argument reads its parameters off. -/
theorem exists_levy_good_stage (s : V) :
    ∃ lam : V, IsOrdinal lam ∧ (∀ β ∈ lam, succ β ∈ lam) ∧
      (∀ β ∈ lam, hartogsNumber (hierarchy β) ∈ lam) ∧
      (∀ y ∈ s, y ∈ hierarchy lam) ∧ κ ∈ lam ∧ hartogsNumber κ ∈ lam ∧
      ℘ (hartogsNumber κ ×ˢ hartogsNumber κ) ∈ hierarchy lam ∧
      ℘ (hartogsNumber κ) ∈ hierarchy lam := by
  obtain ⟨lam, hlamO, hsucc, hclosed, hmem⟩ :=
    exists_closed_stage_containing
      (s ∪ ({κ, hartogsNumber κ, ℘ (hartogsNumber κ ×ˢ hartogsNumber κ),
        ℘ (hartogsNumber κ)} : V))
  have := hlamO
  have hright : ∀ y : V,
      y ∈ ({κ, hartogsNumber κ, ℘ (hartogsNumber κ ×ˢ hartogsNumber κ),
        ℘ (hartogsNumber κ)} : V) → y ∈ hierarchy lam :=
    fun y hy ↦ hmem y (mem_union_iff.mpr (Or.inr hy))
  refine ⟨lam, hlamO, hsucc, hclosed,
    fun y hy ↦ hmem y (mem_union_iff.mpr (Or.inl hy)), ?_, ?_, ?_, ?_⟩
  · exact ordinal_mem_of_mem_hierarchy (hright κ (by simp))
  · exact ordinal_mem_of_mem_hierarchy (hright (hartogsNumber κ) (by simp))
  · exact hright _ (by simp)
  · exact hright _ (by simp)

/-- Parameter agreement for the product parameter: a subset of `(κ⁺)ˇ ×ˢ (κ⁺)ˇ` lies in the
checked stage exactly when it lies in the check of `℘ (κ⁺ ×ˢ κ⁺)`. -/
theorem levy_stage_param_prod {lam : V} [IsOrdinal lam] (hlim : ∀ β ∈ lam, succ β ∈ lam)
    (hpow : ℘ (hartogsNumber κ ×ˢ hartogsNumber κ) ∈ hierarchy lam)
    (X : (levyContext κ hG).Model)
    (hX : X ⊆ (levyContext κ hG).check (hartogsNumber κ) ×ˢ
      (levyContext κ hG).check (hartogsNumber κ)) :
    X ∈ (levyContext κ hG).check (hierarchy lam) ↔
      X ∈ (levyContext κ hG).check (℘ (hartogsNumber κ ×ˢ hartogsNumber κ)) := by
  have hprod : (levyContext κ hG).check (hartogsNumber κ ×ˢ hartogsNumber κ) =
      (levyContext κ hG).check (hartogsNumber κ) ×ˢ
        (levyContext κ hG).check (hartogsNumber κ) :=
    (levyContext κ hG).checkEmbedding.map_prod _ _
  rw [← hprod] at hX
  exact check_stage_subset_iff hG hlim hpow X hX

/-- Parameter agreement for the single parameter: a subset of `(κ⁺)ˇ` lies in the checked stage
exactly when it lies in the check of `℘ κ⁺`. -/
theorem levy_stage_param_single {lam : V} [IsOrdinal lam] (hlim : ∀ β ∈ lam, succ β ∈ lam)
    (hpow : ℘ (hartogsNumber κ) ∈ hierarchy lam) (X : (levyContext κ hG).Model)
    (hX : X ⊆ (levyContext κ hG).check (hartogsNumber κ)) :
    X ∈ (levyContext κ hG).check (hierarchy lam) ↔
      X ∈ (levyContext κ hG).check (℘ (hartogsNumber κ)) :=
  check_stage_subset_iff hG hlim hpow X hX

include hAC hU hc hω hκ in
/-- The check of a closed rank stage is ground-like, stated with the flat predicate
`IsGroundLike`. -/
theorem levy_stage_isGroundLike {θ lam : V} [IsOrdinal lam] (hlim : ∀ β ∈ lam, succ β ∈ lam)
    (hclosed : ∀ β ∈ lam, hartogsNumber (hierarchy β) ∈ lam) (hθ : θ ∈ hierarchy lam)
    (hHlam : hartogsNumber κ ∈ lam) (hκlam : κ ∈ lam) :
    IsGroundLike ((levyContext κ hG).check (hierarchy lam))
      ((levyContext κ hG).check (hartogsNumber κ)) ((levyContext κ hG).check θ) :=
  (isGroundLike_iff _ _ _).mpr
    (levy_stage_groundLike hAC hU hc hω hκ hG hlim hclosed hθ hHlam hκlam)

end

end ZFVP
