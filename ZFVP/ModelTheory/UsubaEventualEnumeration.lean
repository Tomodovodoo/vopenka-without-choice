import ZFVP.ModelTheory.UsubaStageDCAll
import ZFVP.ModelTheory.UsubaEnumerationBounds
import ZFVP.ModelTheory.ClassForcingTowerSubsetStabilization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaStage_successor_enumeration [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V} (hG : IsGenericForDefinableDenseClasses (T).Condition (T).LE G)
    (k : V) [IsOrdinal k] (hAC : ¬InternalChoice ((T).stageContext hG k).Model)
    {X : ((T).stageContext hG k).Model}
    (hX : X ⊆ hierarchy (usubaLeastTarget woodinSeedCardinal)) :
    let hks : k ⊆ succ k := IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)
    ∃ γ : ((T).stageContext hG (succ k)).Model, IsOrdinal γ ∧
      InternalDependentChoiceAt γ ∧
      ∃ e ∈ ((T).stageInclusion hG hks X) ^ γ, range e = (T).stageInclusion hG hks X := by
  let hks : k ⊆ succ k := IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)
  let hH := (T).stageFilter_generic hG (succ k)
  have hA : (T).stageContext hG k =
      usubaStageContext k (UsubaSuccessorStage.projected_generic k hH) := by
    apply ForcingContext.eq_of_data_eq <;> try rfl
    exact ((T).stageFilter_projection hG.1 hks).symm
  have hfirst := hA.trans (UsubaSuccessorStage.first_context_eq k hH)
  have htotal := UsubaSuccessorStage.total_context_eq k hH
  obtain ⟨γ, hγ, _, hDC, he⟩ := UsubaSuccessorModel.enumeration_congr
    ((T).order k inferInstance) ((T).top_spec k inferInstance)
    (UsubaSuccessorStage.twoStep_generic k hH) hVP
    ((T).stageContext hG k) ((T).stageContext hG (succ k)) hfirst htotal
    ((T).stageInclusion hG hks) ((T).stageInclusion_check hG hks) hAC hX
  exact ⟨γ, hγ, hDC, he⟩

/-- Every set in a stage extension is eventually enumerated by an ordinal at
which that later stage satisfies dependent choice. -/
theorem usubaStageSetsHaveDCEnumerations [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V} (hG : IsGenericForDefinableDenseClasses (T).Condition (T).LE G) :
    (T).StageSetsHaveDCEnumerations hG := by
  intro i hi x
  obtain ⟨ρ, hρ, hrank⟩ := (T).stage_rank_checked hG i x
  let := hρ
  let k := i ∪ ρ
  have : IsOrdinal k := ordinal_union_ordinal _ _
  have hik : i ⊆ k := subset_union_left _ _
  let X := (T).stageInclusion hG hik x
  let A := (T).stageContext hG k
  by_cases hAC : InternalChoice A.Model
  · obtain ⟨α, hα, hDC, e, he, hr⟩ := A.dcEnumeration_of_choice hAC X
    exact ⟨k, inferInstance, hik, α, hα, hDC, e, he, hr⟩
  · have hDC : ∀ β ∈ A.check k, InternalDependentChoiceAt β :=
      usubaStageDCBelow_semantics (usubaStageDCBelow_all hVP k) ((T).stageFilter_generic hG k)
    have hX : rank X ⊆ A.check k := by
      rw [hrank k hik]
      exact (A.checkEmbedding.subset_iff _ _).mpr (subset_union_right i ρ)
    have htarget := A.usuba_rank_target_bound hVP hAC k hDC hX
    obtain ⟨γ, hγ, hdcγ, e, he, her⟩ := usubaStage_successor_enumeration hVP hG k hAC htarget
    let := hγ
    let B := (T).stageContext hG (succ k)
    obtain ⟨α, hα, rfl⟩ := B.ordinal_eq_check γ
    let := hα
    have hks : k ⊆ succ k := IsOrdinal.toIsTransitive.transitive _ (mem_succ_self k)
    refine ⟨succ k, inferInstance, subset_trans hik hks, α, hα, hdcγ, e, ?_, ?_⟩
    · simpa only [X, (T).stageInclusion_comp hG hik hks] using he
    · simpa only [X, (T).stageInclusion_comp hG hik hks] using her

theorem usubaSubsetsStabilize [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V} (hG : IsGenericForDefinableDenseClasses (T).Condition (T).LE G) :
    (T).SubsetsStabilize hG := by
  apply (T).subsetsStabilize_of_enumerations hG (usubaStageSetsHaveDCEnumerations hVP hG)
  intro j k hj hk hjk α hα hDC
  exact usubaQuotient_closedThrough hjk ((T).stageFilter_generic hG j) hDC

end ZFVP
