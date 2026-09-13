import ZFVP.ModelTheory.ForcingLeastRankNormalization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A bounded equivalent name bounds every globally minimal representative. -/
theorem forcingLeastNameFamily_subset_hierarchy {P R p τ ν δ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ)
    (hν : IsForcingName P ν) (he : p ∈ atomicEquality P R τ ν)
    (hνδ : ν ∈ hierarchy δ) : forcingLeastNameFamily P R p τ ⊆ hierarchy δ := by
  intro σ hσ
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  exact ordinal_mem_of_subset_mem
    ((forcingLeastNameFamily_spec hR hp hτ).rank_minimal hσ ⟨hν, he⟩)
    ((mem_hierarchy_iff_rank_mem _ _).mp hνδ)

/-- A local Scott computation agrees with the global family whenever its domain
contains all globally minimal representatives. -/
theorem forcingLeastNameFamily_eq_localScottSet {U P R p τ X : V} [hU : IsTransitive U]
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ)
    (hbound : forcingLeastNameFamily P R p τ ⊆ U)
    (hX : IsLocalScottSet U (ForcingScottRelated P R p) τ X) :
    forcingLeastNameFamily P R p τ = X := by
  have hF := forcingLeastNameFamily_spec hR hp hτ
  obtain ⟨ν, hν⟩ := hF.nonempty.nonempty
  apply mem_ext
  intro σ
  constructor
  · intro hσ
    exact (hX.2.2 σ (hbound σ hσ)).mpr
      ⟨hF.witness hσ, fun μ _ hμ ↦ hF.rank_minimal hσ hμ⟩
  · intro hσ
    have hs := (hX.2.2 σ (hU.mem_trans hσ hX.1)).mp hσ
    exact (hF.mem_iff_minimal σ).mpr ⟨hs.1, fun μ hμ ↦
      SetTheory.subset_trans (hs.2 ν (hbound ν hν) (hF.witness hν))
        (hF.rank_minimal hν hμ)⟩

theorem forcingLeastRankName_eq_localScottUnion {U P R p τ X : V} [IsTransitive U]
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ)
    (hbound : forcingLeastNameFamily P R p τ ⊆ U)
    (hX : IsLocalScottSet U (ForcingScottRelated P R p) τ X) :
    forcingLeastRankName P R p τ = ⋃ˢ X :=
  congrArg sUnion (forcingLeastNameFamily_eq_localScottSet hR hp hτ hbound hX)

/-- The internal family, interpreted in the ambient model, is a local Scott set. -/
theorem forcingLeastNameFamily_val_localScottSet {U : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (P R p τ : SetDomain U) (hR : IsForcingPreorder P.val R.val)
    (hp : p.val ∈ P.val) (hτ : IsForcingName P.val τ.val) :
    IsLocalScottSet U (ForcingScottRelated P.val R.val p.val) τ.val
      (forcingLeastNameFamily P R p τ).val := by
  have hiR := (TransitiveZF.forcingPreorder_iff U P R).mpr hR
  have hiτ := (TransitiveZF.forcingName_iff U P τ).mpr hτ
  have hF := forcingLeastNameFamily_spec hiR hp hiτ
  have hr (x : SetDomain U) : ForcingScottRelated P R p τ x ↔
      ForcingScottRelated P.val R.val p.val τ.val x.val := by
    unfold ForcingScottRelated
    rw [TransitiveZF.forcingName_iff U P x]
    change (_ ∧ p.val ∈ (atomicEquality P R τ x).val) ↔ _
    rw [TransitiveZF.atomicEquality_val U]
  obtain ⟨ν, hν⟩ := hF.nonempty.nonempty
  refine ⟨(forcingLeastNameFamily P R p τ).property, ⟨ν.val, hν⟩, ?_⟩
  intro σ hσ
  let σ' : SetDomain U := ⟨σ, hσ⟩
  have hm := hF.mem_iff_minimal σ'
  change σ ∈ (forcingLeastNameFamily P R p τ).val ↔ _ at hm
  rw [hm, hr σ']
  apply and_congr_right
  intro _
  have hsub (μ : SetDomain U) : rank σ' ⊆ rank μ ↔ rank σ ⊆ rank μ.val := by
    have hh := (setDomainEndExtension U).subset_iff (rank σ') (rank μ)
    change (rank σ').val ⊆ (rank μ).val ↔ _ at hh
    rw [TransitiveZF.rank_val U σ', TransitiveZF.rank_val U μ] at hh
    exact hh.symm
  constructor
  · intro h μ hμ hmμ
    exact (hsub ⟨μ, hμ⟩).mp (h ⟨μ, hμ⟩ ((hr ⟨μ, hμ⟩).mpr hmμ))
  · intro h μ hmμ
    exact (hsub μ).mpr (h μ.val μ.property ((hr μ).mp hmμ))

theorem TransitiveZF.forcingLeastNameFamily_val_rank (δ : V) [IsOrdinal δ]
    [Nonempty (SetDomain (hierarchy δ))] [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (P R p τ : SetDomain (hierarchy δ)) (hR : IsForcingPreorder P.val R.val)
    (hp : p.val ∈ P.val) (hτ : IsForcingName P.val τ.val) :
    (forcingLeastNameFamily P R p τ).val = forcingLeastNameFamily P.val R.val p.val τ.val := by
  let := hierarchy_transitive δ
  apply Eq.symm
  exact forcingLeastNameFamily_eq_localScottSet hR hp hτ
    (forcingLeastNameFamily_subset_hierarchy hR hp hτ hτ
      (by rwa [atomicEquality_refl hR]) τ.property)
    (forcingLeastNameFamily_val_localScottSet P R p τ hR hp hτ)

theorem TransitiveZF.forcingLeastRankName_val_rank (δ : V) [IsOrdinal δ]
    [Nonempty (SetDomain (hierarchy δ))] [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (P R p τ : SetDomain (hierarchy δ)) (hR : IsForcingPreorder P.val R.val)
    (hp : p.val ∈ P.val) (hτ : IsForcingName P.val τ.val) :
    (forcingLeastRankName P R p τ).val = forcingLeastRankName P.val R.val p.val τ.val := by
  let := hierarchy_transitive δ
  unfold forcingLeastRankName
  rw [TransitiveZF.sUnion_val, TransitiveZF.forcingLeastNameFamily_val_rank δ P R p τ hR hp hτ]

end ZFVP
