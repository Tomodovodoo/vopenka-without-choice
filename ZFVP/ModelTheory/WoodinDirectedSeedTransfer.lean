import ZFVP.ModelTheory.WoodinDirectedActualTransfer
import ZFVP.ModelTheory.WoodinDirectedSeedQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The countable seed construction expressed on the raw completed row. The
normalization comparison reflects the same quotient order in both directions. -/
theorem ForcingContext.woodinRaw_seed_directedClosedBelow_countable [Countable V]
    (A : ForcingContext V) {Ω θ π : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hP : A.P = ({∅} : V)) (hR : A.R = (({∅} : V) ×ˢ {∅})) (ho : A.one = ∅)
    (hπ : π ∈ A.P ^ ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)) :
    ∀ α ∈ A.check (woodinSeedCardinal : V),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π)
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π)
          (A.projectionQuotientOrder ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π)) α := by
  have hs := woodinSparseSourceStageCode_valid hΩ hAC hθ
  have hz : (∅ : V) ∈ succ (woodinSourceIndex θ) :=
    mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (empty_subset _))
  have hρ := (hs.system.projection hz (mem_succ_self _) (empty_subset _)).maps
  rw [(woodinSparseSourceStageCode_seed (θ := θ)).1, ← hP,
    (woodinSparseSourceStageCode_row (mem_succ_self θ)).1] at hρ
  have hc := A.woodinSparseSource_seed_directedClosedBelow hΩ hAC hθ hP hR ho
  rw [(woodinSparseSourceStageCode_row (mem_succ_self θ)).1,
    (woodinSparseSourceStageCode_row (mem_succ_self θ)).2] at hc
  intro α hα
  apply (A.projectionQuotient_equivalence_directedClosedAt_iff A (Equiv.refl _)
    (fun _ _ ↦ Iff.rfl) (fun _ ↦ rfl) hπ hρ
    (woodinSparseRealizationMap_projection hΩ hAC hθ).maps
    (woodinSparseRealizationInverse_maps hΩ hAC hθ)
    (fun p hp ↦ ?_) (fun _ hq ↦ woodinSparseRealizationMap_right_inverse hΩ hAC hθ hq)
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).symm) α).mpr
  · exact hc α hα
  · have h1 := function_value_mem hρ
      (function_value_mem (woodinSparseRealizationMap_projection hΩ hAC hθ).maps hp)
    have h2 := function_value_mem hπ hp
    rw [hP] at h1 h2
    rw [mem_singleton_iff.mp h1, mem_singleton_iff.mp h2]


def woodinRawSeedDirectedQuotientFormula : SetTheorySemisentence 3 :=
  f“Ω θ π. !IsOrdinal.dfn θ ∧ !woodinSupercompactFormula Ω ∧ ¬!choiceFunctionSentence ∧ θ ⊆ Ω ∧
    π ∈ !function.dfn (!singleton.dfn (!isEmpty))
      (!value.dfn (!forcingCodePFormula (!kpair.π₁.dfn (!woodinIterationRecFormula θ))) θ) →
    !allProjectionQuotientDirectedClosedBelowFormula
      (!singleton.dfn (!isEmpty)) (!prod.dfn (!singleton.dfn (!isEmpty)) (!singleton.dfn (!isEmpty))) (!isEmpty)
      (!value.dfn (!forcingCodePFormula (!kpair.π₁.dfn (!woodinIterationRecFormula θ))) θ)
      (!value.dfn (!forcingCodeRFormula (!kpair.π₁.dfn (!woodinIterationRecFormula θ))) θ)
      π (!woodinSeedCardinalFormula)”

instance woodinRawSeedDirectedQuotientFormula_defined : Defined
    (fun v : Fin 3 → V ↦ IsOrdinal (v 1) → IsWoodinSupercompact (v 0) → ¬InternalChoice V →
      v 1 ⊆ v 0 → v 2 ∈ ({∅} : V) ^ ((forcingCodeP (kpair.π₁ (woodinIterationRec (v 1)))) ‘ (v 1)) →
      ForcesProjectionQuotientDirectedClosedBelow ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅
        ((forcingCodeP (kpair.π₁ (woodinIterationRec (v 1)))) ‘ (v 1))
        ((forcingCodeR (kpair.π₁ (woodinIterationRec (v 1)))) ‘ (v 1)) (v 2) woodinSeedCardinal)
      woodinRawSeedDirectedQuotientFormula :=
  ⟨fun v ↦ by simp [woodinRawSeedDirectedQuotientFormula]⟩

theorem woodinRaw_seed_directedQuotient_forced_countable [Countable V]
    {Ω θ π : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hπ : π ∈ ({∅} : V) ^ ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)) :
    ForcesProjectionQuotientDirectedClosedBelow ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅
      ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π woodinSeedCardinal := by
  have hS := (woodinIterationStageCode_valid_le hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)
  apply projectionQuotient_directedClosedBelow_forced_of_generics
    (singletonForcing_preorder (∅ : V)) (singletonForcing_top (∅ : V))
    (forcingProjection_to_singleton hS hπ) hS
  intro G hG
  let A : ForcingContext V := ⟨_, _, _, G, singletonForcing_preorder ∅, singletonForcing_top ∅, hG⟩
  exact A.woodinRaw_seed_directedClosedBelow_countable hΩ hAC hθ rfl rfl rfl hπ

/-- The seed assertion is transferred as a fixed raw-row sentence. Its
countable proof includes the first collapse, normalization and composition. -/
theorem woodinRaw_seed_directedQuotient_forced
    {Ω θ π : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hπ : π ∈ ({∅} : V) ^ ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)) :
    ForcesProjectionQuotientDirectedClosedBelow ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅
      ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π woodinSeedCardinal := by
  have hv : woodinRawSeedDirectedQuotientFormula.Evalb ![Ω, θ, π] := by
    apply eval_of_countable_zf woodinRawSeedDirectedQuotientFormula
    intro W _ _ _ _ w
    apply (Defined.eval_iff _).mpr
    intro hθord hΩ hAC hθ hπ
    let := hθord
    exact woodinRaw_seed_directedQuotient_forced_countable hΩ hAC hθ hπ
  exact (Defined.eval_iff _).mp hv (show IsOrdinal θ from inferInstance) hΩ hAC hθ hπ

theorem ForcingContext.woodinRaw_seed_directedClosedBelow_zf
    (A : ForcingContext V) {Ω θ π : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hP : A.P = ({∅} : V)) (hR : A.R = (({∅} : V) ×ˢ {∅})) (ho : A.one = ∅)
    (hπ : π ∈ A.P ^ ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)) :
    ∀ α ∈ A.check (woodinSeedCardinal : V),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π)
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π)
          (A.projectionQuotientOrder ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π)) α := by
  have hS := (woodinIterationStageCode_valid_le hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)
  have hπ' : π ∈ ({∅} : V) ^ ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ) := hP ▸ hπ
  have hp : IsForcingProjection A.P A.R
      ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ) π := by
    rw [hP, hR]
    exact forcingProjection_to_singleton hS hπ'
  apply A.projectionQuotient_directedClosedBelow_of_forced hp hS
  simpa only [ForcesProjectionQuotientDirectedClosedBelow, hP, hR, ho] using
    woodinRaw_seed_directedQuotient_forced hΩ hAC hθ hπ'

end ZFVP
