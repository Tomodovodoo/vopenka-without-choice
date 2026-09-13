import ZFVP.ModelTheory.WoodinSparseCodeCompatibility
import ZFVP.ModelTheory.WoodinSparseStageRules
import ZFVP.ModelTheory.WoodinSparseDirectRank
import ZFVP.ModelTheory.WoodinFixedPointDirect

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ : V} [IsOrdinal γ]

 theorem woodinSparseStageCode_rows_subset_at_direct
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (hinac : IsChoicelessInaccessible γ)
    (hpref : IsWoodinIteration γ γ (woodinIterationPrefix γ) (woodinIterationCardinalPrefix γ)) :
    ∀ i ∈ succ γ, (forcingCodeP (woodinSparseStageCode γ)) ‘ i ⊆ hierarchy γ := by
  have hlim : ∀ i ∈ γ, succ i ∈ γ := fun _ hi ↦ regularCardinal_succ_closed hinac.regular hi
  have hrows : ∀ i ∈ γ, (forcingCodeP (woodinSparsePrefixCode γ)) ‘ i ∈ hierarchy γ := by
    intro i hi
    apply woodinSparsePrefixCode_small hΩ hAC hγ hi hinac
    rw [← woodinIterationCardinalPrefix_value hΩ hAC hγ hi]
    exact hpref.bounded i hi
  intro i hi
  rcases mem_succ_iff.mp hi with heq | hi
  · subst i
    have hz : γ ≠ ∅ := by
      intro he
      exact not_mem_empty (he ▸ hinac.2.1)
    have hn : γ ≠ succ (⋃ˢ γ) := by
      intro he
      have hm : ⋃ˢ γ ∈ γ := (congrArg (fun x : V ↦ (⋃ˢ γ) ∈ x) he).mpr (mem_succ_self (⋃ˢ γ))
      have hh := hlim _ hm
      rw [← he] at hh
      exact mem_irrefl _ hh
    have he := hpref.limitCardinal_eq_endpoint hlim
    rw [(woodinSparseStageCode_direct hz hn (he.symm ▸ hinac)).1]
    exact woodinSparseDirectBase_subset_hierarchy_of_rows (woodinSparsePrefixCode_valid hΩ hAC hγ) hrows
  · rw [← (woodinSparsePrefixCode_valid hΩ hAC hγ).tableP.value_of_subset
      (woodinSparseStageCode_valid hΩ hAC hγ).tableP (woodinSparseStageCode_extends hΩ hAC hγ).subP hi]
    exact fun _ hx ↦ (hierarchy_transitive γ).mem_trans hx (hrows i hi)

 theorem woodinSparseStageCode_rows_subset_at_fixedPoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ∈ Ω)
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    ∀ i ∈ succ γ, (forcingCodeP (woodinSparseStageCode γ)) ‘ i ⊆ hierarchy γ := by
  let := hΩ.inaccessible.1
  exact woodinSparseStageCode_rows_subset_at_direct hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hγ)
    (woodinIteration_fixedPoint_inaccessible hΩ hAC hγ hfix)
    (woodinIteration_fixedPoint_prefix hΩ hAC hγ hfix)

 theorem woodinSparseStageCode_rows_subset_at_endpoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ i ∈ succ Ω, (forcingCodeP (woodinSparseStageCode Ω)) ‘ i ⊆ hierarchy Ω := by
  let := hΩ.inaccessible.1
  exact woodinSparseStageCode_rows_subset_at_direct hΩ hAC (subset_refl Ω)
    hΩ.inaccessible (woodinIterationExit hΩ hAC).2.2.1

theorem woodinSparseSourceStageCode_rows_subset_at_direct
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ⊆ Ω)
    (hinac : IsChoicelessInaccessible γ)
    (hpref : IsWoodinIteration γ γ (woodinIterationPrefix γ) (woodinIterationCardinalPrefix γ)) :
    ∀ i ∈ succ (woodinSourceIndex γ),
      (forcingCodeP (woodinSparseSourceStageCode γ)) ‘ i ⊆ hierarchy γ := by
  intro i hi
  have hi' : i ∈ woodinSourceIndex (succ γ) := by simpa only [woodinSourceIndex_successor] using hi
  rcases woodinSourceIndex_cases hi' with he | ⟨j, hj, rfl⟩
  · subst i
    rw [(woodinSparseSourceStageCode_seed (θ := γ)).1]
    intro x hx
    rw [mem_singleton_iff.mp hx]
    apply (mem_hierarchy_iff_of_ordinal γ ∅).mpr
    exact ⟨∅, IsOrdinal.toIsTransitive.mem_trans (show (∅ : V) ∈ ω from by simp) hinac.2.1, empty_subset _⟩
  · rw [(woodinSparseSourceStageCode_row hj).1]
    exact woodinSparseStageCode_rows_subset_at_direct hΩ hAC hγ hinac hpref j hj

theorem woodinSparseSourceStageCode_rows_subset_at_fixedPoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hγ : γ ∈ Ω)
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    ∀ i ∈ succ (woodinSourceIndex γ),
      (forcingCodeP (woodinSparseSourceStageCode γ)) ‘ i ⊆ hierarchy γ := by
  let := hΩ.inaccessible.1
  exact woodinSparseSourceStageCode_rows_subset_at_direct hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hγ)
    (woodinIteration_fixedPoint_inaccessible hΩ hAC hγ hfix)
    (woodinIteration_fixedPoint_prefix hΩ hAC hγ hfix)

theorem woodinSparseSourceStageCode_rows_subset_at_endpoint
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ i ∈ succ (woodinSourceIndex Ω),
      (forcingCodeP (woodinSparseSourceStageCode Ω)) ‘ i ⊆ hierarchy Ω := by
  let := hΩ.inaccessible.1
  exact woodinSparseSourceStageCode_rows_subset_at_direct hΩ hAC (subset_refl Ω)
    hΩ.inaccessible (woodinIterationExit hΩ hAC).2.2.1

end ZFVP



