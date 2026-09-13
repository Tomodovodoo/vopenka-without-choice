import ZFVP.ModelTheory.WoodinDirectedForcingClosure
import ZFVP.ModelTheory.WoodinSparseQuotientInputs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinActualDirectedQuotientFormula : SetTheorySemisentence 3 :=
  f“Ω i j. !IsOrdinal.dfn i ∧ !IsOrdinal.dfn j ∧ !woodinSupercompactFormula Ω ∧
    ¬!choiceFunctionSentence ∧ i ⊆ j ∧ j ⊆ Ω →
    !allProjectionQuotientDirectedClosedBelowFormula
      (!value.dfn (!forcingCodePFormula (!kpair.π₁.dfn (!woodinIterationRecFormula i))) i)
      (!value.dfn (!forcingCodeRFormula (!kpair.π₁.dfn (!woodinIterationRecFormula i))) i)
      (!value.dfn (!forcingCodetFormula (!kpair.π₁.dfn (!woodinIterationRecFormula i))) i)
      (!value.dfn (!forcingCodePFormula (!kpair.π₁.dfn (!woodinIterationRecFormula j))) j)
      (!value.dfn (!forcingCodeRFormula (!kpair.π₁.dfn (!woodinIterationRecFormula j))) j)
      (!value.dfn (!forcingCodeπFormula (!kpair.π₁.dfn (!woodinIterationRecFormula j))) (!kpair.dfn i j))
      (!value.dfn (!kpair.π₂.dfn (!woodinIterationRecFormula i)) i)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinActualDirectedQuotientFormula_defined : Defined
    (fun v : Fin 3 → V ↦ IsOrdinal (v 1) → IsOrdinal (v 2) → IsWoodinSupercompact (v 0) →
      ¬InternalChoice V → v 1 ⊆ v 2 → v 2 ⊆ v 0 →
      ForcesProjectionQuotientDirectedClosedBelow
        ((forcingCodeP (kpair.π₁ (woodinIterationRec (v 1)))) ‘ (v 1))
        ((forcingCodeR (kpair.π₁ (woodinIterationRec (v 1)))) ‘ (v 1))
        ((forcingCodet (kpair.π₁ (woodinIterationRec (v 1)))) ‘ (v 1))
        ((forcingCodeP (kpair.π₁ (woodinIterationRec (v 2)))) ‘ (v 2))
        ((forcingCodeR (kpair.π₁ (woodinIterationRec (v 2)))) ‘ (v 2))
        ((forcingCodeπ (kpair.π₁ (woodinIterationRec (v 2)))) ‘ ⟨v 1, v 2⟩ₖ)
        ((kpair.π₂ (woodinIterationRec (v 1))) ‘ (v 1))) woodinActualDirectedQuotientFormula :=
  ⟨fun v ↦ by simp [woodinActualDirectedQuotientFormula]⟩

theorem woodinActual_directedQuotient_forced_countable [Countable V]
    {Ω i j : V} [IsOrdinal i] [IsOrdinal j]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hij : i ⊆ j) (hjΩ : j ⊆ Ω) :
    ForcesProjectionQuotientDirectedClosedBelow
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec j))) ‘ j)
      ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ)
      ((kpair.π₂ (woodinIterationRec i)) ‘ i) := by
  have hsi := woodinIterationStageCode_valid_le hΩ hAC (subset_trans hij hjΩ)
  have hsj := woodinIterationStageCode_valid_le hΩ hAC hjΩ
  have hπ : IsForcingProjection
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec j))) ‘ j)
      ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ) := by
    rcases IsOrdinal.subset_iff.mp hij with rfl | hij
    · exact hsj.system.projection (mem_succ_self _) (mem_succ_self _) (subset_refl _)
    · exact woodinIterationStage_projection_to_row hΩ hAC hjΩ hij
  apply projectionQuotient_directedClosedBelow_forced_of_generics
    (hsi.system.order.preorder i (mem_succ_self i)) (hsi.system.tops.top i (mem_succ_self i))
    hπ (hsj.system.order.preorder j (mem_succ_self j))
  intro G hG
  let A : ForcingContext V := ⟨_, _, _, G,
    hsi.system.order.preorder i (mem_succ_self i), hsi.system.tops.top i (mem_succ_self i), hG⟩
  exact A.woodinActual_quotient_directedClosedBelow hΩ hAC hij hjΩ rfl rfl rfl

/-- A fixed sentence for the actual raw recurrence removes the countability
restriction. No formula for a separately chosen presentation is used. -/
theorem woodinActual_directedQuotient_forced
    {Ω i j : V} [IsOrdinal i] [IsOrdinal j]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hij : i ⊆ j) (hjΩ : j ⊆ Ω) :
    ForcesProjectionQuotientDirectedClosedBelow
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec j))) ‘ j)
      ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ)
      ((kpair.π₂ (woodinIterationRec i)) ‘ i) := by
  have hv : woodinActualDirectedQuotientFormula.Evalb ![Ω, i, j] := by
    apply eval_of_countable_zf woodinActualDirectedQuotientFormula
    intro W _ _ _ _ w
    apply (Defined.eval_iff _).mpr
    intro hi hj hΩ hAC hij hjΩ
    let := hi
    let := hj
    exact woodinActual_directedQuotient_forced_countable hΩ hAC hij hjΩ
  exact (Defined.eval_iff _).mp hv (show IsOrdinal i from inferInstance) (show IsOrdinal j from inferInstance) hΩ hAC hij hjΩ

theorem ForcingContext.woodinActual_quotient_directedClosedBelow_zf
    (A : ForcingContext V) {Ω i j : V} [IsOrdinal i] [IsOrdinal j]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hij : i ⊆ j) (hjΩ : j ⊆ Ω)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) :
    ∀ β ∈ A.check ((kpair.π₂ (woodinIterationRec i)) ‘ i),
      IsForcingDirectedClosedAt
        (A.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
          ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ))
        (forcingSeparativeOrder
          (A.projectionQuotient ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
            ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ))
          (A.projectionQuotientOrder ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
            ((forcingCodeR (kpair.π₁ (woodinIterationRec j))) ‘ j)
            ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ))) β := by
  have hsj := woodinIterationStageCode_valid_le hΩ hAC hjΩ
  have hπ : IsForcingProjection A.P A.R
      ((forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ j)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec j))) ‘ j)
      ((forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨i, j⟩ₖ) := by
    rw [hP, hR]
    rcases IsOrdinal.subset_iff.mp hij with rfl | hij
    · exact hsj.system.projection (mem_succ_self _) (mem_succ_self _) (subset_refl _)
    · exact woodinIterationStage_projection_to_row hΩ hAC hjΩ hij
  apply A.projectionQuotient_directedClosedBelow_of_forced hπ (hsj.system.order.preorder j (mem_succ_self j))
  simpa only [ForcesProjectionQuotientDirectedClosedBelow, hP, hR, ho] using woodinActual_directedQuotient_forced hΩ hAC hij hjΩ

end ZFVP

