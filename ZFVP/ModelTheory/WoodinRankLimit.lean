import ZFVP.ModelTheory.ProjectionRankLimit
import ZFVP.ModelTheory.WoodinRankCoherence
import ZFVP.ModelTheory.WoodinConstructionCountable

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.limit_rankEnumerations [Countable V] {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ (succ θ) s K)
    (hc : HasWoodinQuotientClosure (succ θ) s K)
    (hl : ∀ i ∈ θ, succ i ∈ θ) (hr : ∀ i ∈ θ, WoodinRankStage i s K) :
    WoodinRankStage θ s K := by
  let := (h.inaccessible θ (mem_succ_self θ)).1
  let P := (forcingCodeP s) ‘ θ
  let R := (forcingCodeR s) ‘ θ
  let t := (forcingCodet s) ‘ θ
  have hR : IsForcingPreorder P R := h.code.system.order.preorder θ (mem_succ_self θ)
  have ht : IsForcingTop P R t := h.code.system.tops.top θ (mem_succ_self θ)
  apply (all_forces_iff_all_generics hR ht shortRankEnumerationsFormula
    ![⟨checkName t θ, checkName_isName ht.1 θ⟩,
      ⟨checkName t (K ‘ θ), checkName_isName ht.1 (K ‘ θ)⟩]).mpr
  intro G hG
  let B : ForcingContext V := ⟨P, R, t, G, hR, ht, hG⟩
  apply (Defined.eval_iff _).mpr
  change HasShortRankEnumerations (B.check θ) (B.check (K ‘ θ))
  let π := definableGraph θ (fun i ↦ (forcingCodeπ s) ‘ ⟨i, θ⟩ₖ) (by definability)
  let E := definableGraph θ (fun i ↦ (forcingCodeE s) ‘ ⟨i, θ⟩ₖ) (by definability)
  have hi' (i : V) (hi : i ∈ θ) : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  apply B.projected_limit_rankEnumerations (P := forcingCodeP s) (R := forcingCodeR s)
    (t := forcingCodet s) (K := K) (π := π) (E := E) hl
    (fun i hi ↦ h.increasing i (hi' i hi) θ (mem_succ_self θ) hi)
    (fun i hi ↦ h.code.system.order.preorder i (hi' i hi))
    (fun i hi ↦ h.code.system.tops.top i (hi' i hi))
  · intro i hi
    simp only [π, E, value_definableGraph _ _ _ hi]
    exact h.code.system.splitProjection (hi' i hi) (mem_succ_self θ)
      (IsOrdinal.toIsTransitive.transitive _ hi)
  · intro i hi p hp
    have hs := h.stage i (hi' i hi)
    simp only [IsWoodinStage, woodinIterationStage, woodinStagePoset_code,
      woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code] at hs
    rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff]
    exact ⟨hs.2.2.2.1 p hp, hs.2.2.2.2 p hp⟩
  · intro i hi
    simp only [π, value_definableGraph _ _ _ hi]
    exact hc i (hi' i hi) θ (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi)
  · exact hr

theorem woodinIterationRec_rankStage_limit [Countable V] {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (hl : ∀ i ∈ θ, succ i ∈ θ)
    (hr : ∀ i ∈ θ, WoodinRankStage i (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i))) :
    WoodinRankStage θ (kpair.π₁ (woodinIterationRec θ)) (kpair.π₂ (woodinIterationRec θ)) := by
  let := hδ.inaccessible.1
  have hall := woodinIteration_stages_countable hδ
  have hs := fun i hi ↦ (hall i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1
  apply (hall θ hθ).1.limit_rankEnumerations (hall θ hθ).2 hl
  intro i hi
  exact (woodinIterationRec_rankStage_previous hs (hall θ hθ).1 hi).mp (hr i hi)

end ZFVP
