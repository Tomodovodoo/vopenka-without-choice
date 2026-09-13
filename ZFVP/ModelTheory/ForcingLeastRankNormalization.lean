import ZFVP.ModelTheory.ForcingScottSets

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- All globally least-rank names forced equal to the input at the supplied
condition. The input rank supplies a set bound, not a choice of representative. -/
noncomputable def forcingLeastNameFamily (P R p τ : V) : V :=
  {σ ∈ hierarchy (succ (rank τ)) ; ForcingScottRelated P R p τ σ ∧
    ∀ ν, ForcingScottRelated P R p τ ν → rank σ ⊆ rank ν}

instance forcingLeastNameFamily_definable (P R p : V) :
    ℒₛₑₜ-function₁[V] (forcingLeastNameFamily P R p) := by
  have hh : ℒₛₑₜ-relation (fun X τ : V ↦ ∀ σ, σ ∈ X ↔
    σ ∈ hierarchy (succ (rank τ)) ∧ ForcingScottRelated P R p τ σ ∧
      ∀ ν, ForcingScottRelated P R p τ ν → rank σ ⊆ rank ν) := by definability
  apply Language.Definable.of_iff hh
  intro v
  change v 0 = forcingLeastNameFamily P R p (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [forcingLeastNameFamily, mem_sep_iff]

theorem forcingLeastNameFamily_spec {P R p τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ) :
    IsLeastRankWitnessSet (ForcingScottRelated P R p) τ (forcingLeastNameFamily P R p τ) := by
  have ht : ForcingScottRelated P R p τ τ := ⟨hτ, by rwa [atomicEquality_refl hR]⟩
  obtain ⟨X, hX, _⟩ := leastRankWitnessSet_existsUnique (ForcingScottRelated P R p)
    (by infer_instance) τ ⟨τ, ht⟩
  have he : forcingLeastNameFamily P R p τ = X := by
    apply mem_ext
    intro σ
    rw [forcingLeastNameFamily, mem_sep_iff, hX.mem_iff_minimal]
    constructor
    · exact And.right
    · intro hσ
      refine ⟨?_, hσ⟩
      apply (mem_hierarchy_iff_rank_mem _ _).mpr
      exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (hσ.2 τ ht))
  exact he ▸ hX

noncomputable def forcingLeastRankName (P R p τ : V) : V :=
  ⋃ˢ (forcingLeastNameFamily P R p τ)

instance forcingLeastRankName_definable (P R p : V) :
    ℒₛₑₜ-function₁[V] (forcingLeastRankName P R p) := by
  unfold forcingLeastRankName
  definability

theorem forcingLeastRankName_isName {P R p τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ) :
    IsForcingName P (forcingLeastRankName P R p τ) :=
  sUnion_forcingName (fun _ hσ ↦ ((forcingLeastNameFamily_spec hR hp hτ).witness hσ).1)

theorem forcingLeastRankName_forced_equal {P R p τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ) :
    p ∈ atomicEquality P R τ (forcingLeastRankName P R p τ) :=
  atomicEquality_sUnion (forcingLeastNameFamily_spec hR hp hτ).nonempty
    (fun _ hσ ↦ ((forcingLeastNameFamily_spec hR hp hτ).witness hσ).2)

theorem forcingLeastRankName_rank_minimal {P R p τ ν : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ)
    (hν : ForcingScottRelated P R p τ ν) :
    rank (forcingLeastRankName P R p τ) ⊆ rank ν := by
  have hX := forcingLeastNameFamily_spec hR hp hτ
  apply rank_minimal _ _ inferInstance
  intro z hz
  obtain ⟨σ, hσ, hzσ⟩ := mem_sUnion_iff.mp hz
  exact hierarchy_mono (hX.rank_minimal hσ hν) z (subset_hierarchy_rank σ z hzσ)

/-- The union itself has least rank and is one of the names in the full family. -/
theorem forcingLeastRankName_mem_family {P R p τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ) :
    forcingLeastRankName P R p τ ∈ forcingLeastNameFamily P R p τ := by
  apply ((forcingLeastNameFamily_spec hR hp hτ).mem_iff_minimal _).mpr
  exact ⟨⟨forcingLeastRankName_isName hR hp hτ, forcingLeastRankName_forced_equal hR hp hτ⟩,
    fun _ hν ↦ forcingLeastRankName_rank_minimal hR hp hτ hν⟩

theorem forcingLeastNameFamily_congr {P R p σ τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (he : p ∈ atomicEquality P R σ τ) :
    forcingLeastNameFamily P R p σ = forcingLeastNameFamily P R p τ := by
  have hr (ν : V) : ForcingScottRelated P R p σ ν ↔ ForcingScottRelated P R p τ ν := by
    apply and_congr_right
    intro _
    exact ⟨fun h ↦ atomicEquality_trans hR τ σ ν p ((atomicEquality_symm P R σ τ) ▸ he) h,
      fun h ↦ atomicEquality_trans hR σ τ ν p he h⟩
  apply mem_ext
  intro ν
  rw [(forcingLeastNameFamily_spec hR hp hσ).mem_iff_minimal,
    (forcingLeastNameFamily_spec hR hp hτ).mem_iff_minimal, hr ν]
  apply and_congr Iff.rfl
  exact forall_congr' fun υ ↦ imp_congr_left (hr υ)

theorem forcingLeastRankName_congr {P R p σ τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P)
    (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (he : p ∈ atomicEquality P R σ τ) :
    forcingLeastRankName P R p σ = forcingLeastRankName P R p τ :=
  congrArg sUnion (forcingLeastNameFamily_congr hR hp hσ hτ he)

theorem forcingLeastRankName_idempotent {P R p τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ) :
    forcingLeastRankName P R p (forcingLeastRankName P R p τ) = forcingLeastRankName P R p τ := by
  exact (forcingLeastRankName_congr hR hp hτ (forcingLeastRankName_isName hR hp hτ)
    (forcingLeastRankName_forced_equal hR hp hτ)).symm

theorem forcingLeastRankName_rank_le {P R p τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ) :
    rank (forcingLeastRankName P R p τ) ⊆ rank τ :=
  forcingLeastRankName_rank_minimal hR hp hτ ⟨hτ, by rwa [atomicEquality_refl hR]⟩

theorem forcingLeastRankName_empty {P R p : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) : forcingLeastRankName P R p ∅ = ∅ := by
  have hr := forcingLeastRankName_rank_le hR hp (empty_forcingName P)
  rw [rank_empty] at hr
  have he := subset_empty_iff_eq_empty.mp hr
  have hs := subset_hierarchy_rank (forcingLeastRankName P R p ∅)
  rw [he, hierarchy_empty] at hs
  exact subset_empty_iff_eq_empty.mp hs

theorem forcingLeastRankName_empty_of_forced {P R p τ : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ)
    (he : p ∈ atomicEquality P R τ ∅) : forcingLeastRankName P R p τ = ∅ :=
  (forcingLeastRankName_congr hR hp hτ (empty_forcingName P) he).trans
    (forcingLeastRankName_empty hR hp)

/-- Any bounded equivalent name bounds the canonical representative. -/
theorem forcingLeastRankName_mem_hierarchy_of_equiv {P R p τ ν δ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (hp : p ∈ P) (hτ : IsForcingName P τ)
    (hν : IsForcingName P ν) (he : p ∈ atomicEquality P R τ ν) (hνδ : ν ∈ hierarchy δ) :
    forcingLeastRankName P R p τ ∈ hierarchy δ := by
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  exact ordinal_mem_of_subset_mem (forcingLeastRankName_rank_minimal hR hp hτ ⟨hν, he⟩)
    ((mem_hierarchy_iff_rank_mem _ _).mp hνδ)

end ZFVP
