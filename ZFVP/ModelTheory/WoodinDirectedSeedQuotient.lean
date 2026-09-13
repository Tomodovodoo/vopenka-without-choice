import ZFVP.ModelTheory.WoodinDirectedSparseQuotient
import ZFVP.ModelTheory.WoodinDirectedClosureComposition
import ZFVP.ModelTheory.WoodinSparseSeedQuotient
import ZFVP.ModelTheory.SaturatedQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
theorem saturatedWoodin_quotient_directedClosedAt (A : ForcingContext V) {κ δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R regularCardinalFormula
      (standardTuple ![checkName A.one κ]))
    {α : A.Model} (hα : α ∈ A.check κ) (hDC : InternalDependentChoiceAt α) :
    IsForcingDirectedClosedAt
      (A.projectionQuotient (twoStepConditions A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅)
        (twoStepProjection A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅)
          (twoStepProjection A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅))
        (A.projectionQuotientOrder
          (twoStepConditions A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅)
          (twoStepOrder A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ)
            (saturatedWoodinPrefixOrderName A.P A.R A.one κ δ) ∅)
          (twoStepProjection A.P A.R (saturatedWoodinPrefixPosetName A.P A.R A.one κ δ) ∅))) α := by
  have h := saturatedWoodinPrefix_iterand A.order A.top hδ hP hκδ hκ
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hreg : IsRegularCardinal (A.check κ) :=
    (Defined.eval_iff _).mp ((A.formula_truth regularCardinalFormula
      ![⟨checkName A.one κ, checkName_isName A.top.1 κ⟩]).mpr
        ⟨p, hp, hκ p (A.generic.1.1 p hp)⟩)
  exact A.twoStepCollapseQuotient_separative_directedClosedAt h hreg hα hDC
    (A.saturatedWoodinPosetName_value hδ hP hκδ) (A.saturatedWoodinOrderName_value hδ hP hκδ)





theorem woodinInitial_seed_directedClosedBelow (A : ForcingContext V) {Ω π : V}
    (hΩ : IsWoodinSupercompact Ω)
    (hP : A.P = woodinStagePoset (woodinSeedStage : V))
    (hR : A.R = woodinStageOrder (woodinSeedStage : V))
    (ho : A.one = woodinStageTop (woodinSeedStage : V))
    (hπ : π ∈ A.P ^ woodinStagePoset (woodinInitialStage : V)) :
    ∀ α ∈ A.check (woodinSeedCardinal : V),
      IsForcingDirectedClosedAt (A.projectionQuotient (woodinStagePoset (woodinInitialStage : V)) π)
        (forcingSeparativeOrder (A.projectionQuotient (woodinStagePoset (woodinInitialStage : V)) π)
          (A.projectionQuotientOrder (woodinStagePoset (woodinInitialStage : V))
            (woodinStageOrder (woodinInitialStage : V)) π)) α := by
  have hs := woodinSeedStage_stage (V := V)
  let : IsOrdinal (woodinStageCardinal (woodinSeedStage : V)) := hs.2.2.1
  have hn := woodinSuccessorStep_preserves_below_supercompact hs woodinSeedStage_small hΩ
    (by simpa only [woodinSeedStage, woodinStageCardinal_code] using woodinSeedCardinal_lt hΩ)
  have hc : IsChoicelessInaccessible (woodinStageCardinal (woodinInitialStage : V)) := hn.2.2.1
  let := hc.1
  have hκc := hn.2.2.2.1
  have hκ : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R regularCardinalFormula
      (standardTuple ![checkName A.one (woodinStageCardinal (woodinSeedStage : V))]) := by
    simpa only [hP, hR, ho] using hs.2.2.2.1
  have hDC : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R dependentChoiceBelowFormula
      (standardTuple ![checkName A.one (woodinStageCardinal (woodinSeedStage : V))]) := by
    simpa only [hP, hR, ho] using hs.2.2.2.2
  let N := saturatedWoodinPrefixPosetName A.P A.R A.one
    (woodinStageCardinal (woodinSeedStage : V)) (woodinStageCardinal (woodinInitialStage : V))
  let T := saturatedWoodinPrefixOrderName A.P A.R A.one
    (woodinStageCardinal (woodinSeedStage : V)) (woodinStageCardinal (woodinInitialStage : V))
  have hQ : woodinStagePoset (woodinInitialStage : V) = twoStepConditions A.P A.R N ∅ := by
    simp only [N, hP, hR, ho, woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt,
      woodinStagePoset_code, woodinStageCardinal_code]
  have hS : woodinStageOrder (woodinInitialStage : V) = twoStepOrder A.P A.R N T ∅ := by
    simp only [N, T, hP, hR, ho, woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt,
      woodinStageOrder_code, woodinStageCardinal_code]
  have hπeq : π = twoStepProjection A.P A.R N ∅ := by
    apply functions_into_singleton_eq (a := (∅ : V))
    · simpa only [hQ, hP, woodinSeedStage, woodinStagePoset_code] using hπ
    · simpa only [hP, woodinSeedStage, woodinStagePoset_code] using
        twoStepProjection_maps A.P A.R N (∅ : V)
  intro α hα
  have hα' : α ∈ A.check (woodinStageCardinal (woodinSeedStage : V)) := by
    simpa only [woodinSeedStage, woodinStageCardinal_code] using hα
  have hd : InternalDependentChoiceAt α := by
    obtain ⟨p, hp⟩ := A.generic.1.2.1
    have hd := (Defined.eval_iff _).mp ((A.formula_truth dependentChoiceBelowFormula
      ![⟨checkName A.one (woodinStageCardinal (woodinSeedStage : V)),
        checkName_isName A.top.1 _⟩]).mpr ⟨p, hp, hDC p (A.generic.1.1 p hp)⟩)
    exact hd α hα'
  rw [hQ, hS, hπeq]
  exact A.saturatedWoodin_quotient_directedClosedAt hc
    (hP.symm ▸ woodinSeedStage_small _ hc hκc)
    (IsOrdinal.toIsTransitive.transitive _ hκc) hκ hα' hd


theorem woodinSparseInitial_seed_directedClosedBelow (A : ForcingContext V) {Ω ρ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hP : A.P = ({∅} : V)) (hR : A.R = (({∅} : V) ×ˢ {∅})) (ho : A.one = ∅)
    (hρ : ρ ∈ A.P ^ ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅)) :
    ∀ α ∈ A.check (woodinSeedCardinal : V),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅) ρ)
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅) ρ)
          (A.projectionQuotientOrder ((forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅)
            ((forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅) ρ)) α := by
  let Q := (forcingCodeP (kpair.π₁ (woodinIterationRec (∅ : V)))) ‘ ∅
  let S := (forcingCodeR (kpair.π₁ (woodinIterationRec (∅ : V)))) ‘ ∅
  let π := definableGraph Q (fun _ : V ↦ (∅ : V)) (by definability)
  have hπ : π ∈ A.P ^ Q := by
    rw [hP]
    exact definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦ by simp)
  have hclosed : ∀ α ∈ A.check (woodinSeedCardinal : V),
      IsForcingDirectedClosedAt (A.projectionQuotient Q π)
        (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α := by
    have hπ' : π ∈ A.P ^ woodinStagePoset (woodinInitialStage : V) := by
      simpa only [Q, woodinIterationRec_initial, kpair.π₁_kpair, woodinInitialCode, forcingInitialCode,
        forcingCodeP_code, forcingFamilyNext_new] using hπ
    have hp' : A.P = woodinStagePoset (woodinSeedStage : V) := by
      simpa only [woodinSeedStage, woodinStagePoset_code] using hP
    have hr' : A.R = woodinStageOrder (woodinSeedStage : V) := by
      simpa only [woodinSeedStage, woodinStageOrder_code] using hR
    have ho' : A.one = woodinStageTop (woodinSeedStage : V) := by
      simpa only [woodinSeedStage, woodinStageTop_code] using ho
    simpa only [Q, S, woodinIterationRec_initial, kpair.π₁_kpair, woodinInitialCode, forcingInitialCode,
      forcingCodeP_code, forcingCodeR_code, forcingFamilyNext_new] using
      A.woodinInitial_seed_directedClosedBelow hΩ hp' hr' ho' hπ'
  exact A.projectionQuotient_equivalence_directedClosedBelow_check A (Equiv.refl _)
    (fun _ _ ↦ Iff.rfl) (fun _ ↦ rfl) hπ hρ
    (woodinSparseRealizationMap_projection hΩ hAC (empty_subset Ω)).maps
    (woodinSparseRealizationInverse_maps hΩ hAC (empty_subset Ω))
    (fun p hp ↦ by
      have h1 := function_value_mem hρ
        (function_value_mem (woodinSparseRealizationMap_projection hΩ hAC (empty_subset Ω)).maps hp)
      have h2 := function_value_mem hπ hp
      rw [hP] at h1 h2
      rw [mem_singleton_iff.mp h1, mem_singleton_iff.mp h2])
    (fun _ hq ↦ woodinSparseRealizationMap_right_inverse hΩ hAC (empty_subset Ω) hq)
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC (empty_subset Ω) hp hq).symm)
    woodinSeedCardinal hclosed


/-- The inserted trivial seed has cutoff mu, the least DC failure. Its bounds
come from the actual first collapse and compose with the restored-row bounds. -/
theorem woodinSparseSource_seed_directedClosedBelow [Countable V]
    (A : ForcingContext V) {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hP : A.P = ({∅} : V)) (hR : A.R = (({∅} : V) ×ˢ {∅})) (ho : A.one = ∅) :
    ∀ α ∈ A.check (woodinSeedCardinal : V),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
          ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨∅, woodinSourceIndex θ⟩ₖ))) α := by
  let s := woodinSparseSourceStageCode θ
  have hs := woodinSparseSourceStageCode_valid hΩ hAC hθ
  have hz : (∅ : V) ∈ succ (woodinSourceIndex θ) := by
    apply mem_succ_iff.mpr
    exact IsOrdinal.subset_iff.mp (empty_subset _)
  have h0θ : (∅ : V) ∈ succ θ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset _))
  have hi : woodinSourceIndex (∅ : V) ∈ succ (woodinSourceIndex θ) := by
    rw [← woodinSourceIndex_successor]
    exact woodinSourceIndex_mem_iff.mpr h0θ
  have hj := mem_succ_self (woodinSourceIndex θ)
  have hirow : (forcingCodeP s) ‘ (woodinSourceIndex (∅ : V)) =
      (forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅ ∧
      (forcingCodeR s) ‘ (woodinSourceIndex (∅ : V)) =
      (forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅ := by
    rw [(woodinSparseSourceStageCode_row h0θ).1, (woodinSparseSourceStageCode_row h0θ).2]
    exact woodinSparseStage_old_row h0θ
  have hseedP : (forcingCodeP s) ‘ ∅ = A.P := (woodinSparseSourceStageCode_seed (θ := θ)).1.trans hP.symm
  have hseedR : (forcingCodeR s) ‘ ∅ = A.R := (woodinSparseSourceStageCode_seed (θ := θ)).2.1.trans hR.symm
  have hτ := hs.system.splitProjection hz hi (empty_subset _)
  rw [hseedP, hseedR] at hτ
  have hiμ := woodinSeedCardinal_lt_initial hΩ
  have hn := woodinSuccessorStep_preserves_below_supercompact (woodinSeedStage_stage (V := V))
    woodinSeedStage_small hΩ
    (by simpa only [woodinSeedStage, woodinStageCardinal_code] using woodinSeedCardinal_lt hΩ)
  let : IsOrdinal (woodinStageCardinal (woodinInitialStage : V)) := hn.2.2.1.1
  have hμ : IsOrdinal (woodinSeedCardinal : V) := by
    simpa only [woodinSeedStage, woodinStageCardinal_code] using (woodinSeedStage_stage (V := V)).2.2.1
  let := hμ
  intro α hα
  let := IsOrdinal.of_mem hα
  rcases IsOrdinal.subset_iff.mp (empty_subset θ) with hθ0 | h0
  · subst θ
    rw [(woodinSparseSourceStageCode_row (mem_succ_self (∅ : V))).1,
      (woodinSparseSourceStageCode_row (mem_succ_self (∅ : V))).2]
    have hpmap := hτ.projection.maps
    rw [(woodinSparseSourceStageCode_row (mem_succ_self (∅ : V))).1] at hpmap
    exact A.woodinSparseInitial_seed_directedClosedBelow hΩ hAC hP hR ho hpmap α hα
  · have hij : woodinSourceIndex (∅ : V) ⊆ woodinSourceIndex θ := ordinalAdd_mono_right 1 (empty_subset θ)
    have hπ := hs.system.projection hz hj (empty_subset _)
    rw [hseedP, hseedR] at hπ
    apply A.quotient_separative_directedClosedAt_comp_countable hτ
      (hs.system.order.preorder _ hi) (hs.system.tops.top _ hi)
      (hs.system.order.preorder _ hj) hπ.maps (hs.system.projection hi hj hij)
      (hs.system.split.projComp _ hz _ hi _ hj (empty_subset _) hij) α
    · have hρ := hτ.projection.maps
      rw [hirow.1] at hρ
      have hh := A.woodinSparseInitial_seed_directedClosedBelow hΩ hAC hP hR ho hρ α hα
      rwa [← hirow.1, ← hirow.2] at hh
    · intro H hH hA
      let C : ForcingContext V := ⟨_, _, _, H, hs.system.order.preorder _ hi, hs.system.tops.top _ hi, hH⟩
      have hcP : C.P = (forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅ := hirow.1
      have hcR : C.R = (forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅ := hirow.2
      have hco : C.one = ∅ := woodinSparseSourceStageCode_top hΩ hAC hθ hi
      have hκ : (kpair.π₂ (woodinIterationRec (∅ : V))) ‘ ∅ =
          woodinStageCardinal (woodinInitialStage : V) := by
        simp only [woodinIterationRec_initial, kpair.π₂_kpair, woodinInitialCardinals, forcingFamilyNext_new]
      have hcut : A.projectionInclusion C hτ hA α ∈ C.check ((kpair.π₂ (woodinIterationRec (∅ : V))) ‘ ∅) := by
        rw [hκ]
        have hm := (A.projectionInclusion C hτ hA).mem_iff α (A.check (woodinSeedCardinal : V)) |>.mpr hα
        rw [A.projectionInclusion_check C hτ hA] at hm
        have hk := (C.check_mem_iff _ _).mpr hiμ
        exact IsOrdinal.toIsTransitive.mem_trans hm hk
      have hh := C.woodinSparse_quotient_directedClosedBelow hΩ hAC hθ h0 hcP hcR hco _ hcut
      rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).1,
        (woodinSparseSourceStageCode_row (mem_succ_self θ)).2,
        (woodinSparseSourceStageCode_matrices h0θ (mem_succ_self θ)).1]
      exact hh


theorem identityQuotient_separative_directedClosedAt (A : ForcingContext V) {π : V}
    (hπ : π ∈ A.P ^ A.P) (he : ∀ p ∈ A.P, π ‘ p = p) (α : A.Model) :
    IsForcingDirectedClosedAt (A.projectionQuotient A.P π)
      (forcingSeparativeOrder (A.projectionQuotient A.P π)
        (A.projectionQuotientOrder A.P A.R π)) α := by
  intro f hf
  obtain ⟨p, hpG⟩ := A.generic.1.2.1
  have hp := A.generic.1.1 p hpG
  have hp' := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hp, (he p hp).symm ▸ hpG⟩
  exact ⟨A.check p, hp', fun i hi ↦
    A.identityQuotient_separative hπ he hp' (function_value_mem hf.1 hi)⟩

/-- All completed source prefixes, including the inserted seed, have directed
bounds below their actual source cutoff. The final completed row is allowed. -/
theorem woodinSparseSource_all_quotient_directedClosedBelow [Countable V]
    (A : ForcingContext V) {Ω θ j : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hj : j ∈ succ (woodinSourceIndex θ))
    (hP : A.P = (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ j)
    (hR : A.R = (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ j) (ho : A.one = ∅) :
    ∀ α ∈ A.check ((woodinSparseSourceStageCardinals θ) ‘ j),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
          ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j, woodinSourceIndex θ⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j, woodinSourceIndex θ⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
            ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨j, woodinSourceIndex θ⟩ₖ))) α := by
  rcases mem_succ_iff.mp hj with rfl | hj
  · intro α _
    have hs := woodinSparseSourceStageCode_valid hΩ hAC hθ
    rw [← hP, ← hR]
    apply A.identityQuotient_separative_directedClosedAt
    · rw [hP]
      exact (hs.system.projection (mem_succ_self _) (mem_succ_self _) (subset_refl _)).maps
    · intro p hp
      exact hs.system.split.projId (mem_succ_self _) (hP ▸ hp)
  · rcases woodinSourceIndex_cases hj with rfl | ⟨i, hi, rfl⟩
    · rw [(woodinSparseSourceStageCode_seed (θ := θ)).1] at hP
      rw [(woodinSparseSourceStageCode_seed (θ := θ)).2.1] at hR
      rw [woodinSparseSourceStageCardinals, woodinSourceCardinals_seed]
      exact A.woodinSparseSource_seed_directedClosedBelow hΩ hAC hθ hP hR ho
    · let := IsOrdinal.of_mem hi
      have hi' := mem_succ_iff.mpr (Or.inr hi)
      have hisub : i ⊆ Ω := subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hθ
      rw [(woodinSparseSourceStageCode_row hi').1, (woodinSparseStage_old_row hi').1] at hP
      rw [(woodinSparseSourceStageCode_row hi').2, (woodinSparseStage_old_row hi').2] at hR
      have hP' : A.P = (forcingCodeP (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i) := by
        rwa [(woodinSparseSourceStageCode_row (mem_succ_self i)).1]
      have hR' : A.R = (forcingCodeR (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i) := by
        rwa [(woodinSparseSourceStageCode_row (mem_succ_self i)).2]
      rw [woodinSparseSourceStageCardinals_value hΩ hAC hθ hi',
        ← woodinSparseSourceStageCardinals_value hΩ hAC hisub (mem_succ_self i)]
      exact A.woodinSparseSource_quotient_directedClosedBelow hΩ hAC hθ hi hP' hR' ho

end ForcingContext
end ZFVP
