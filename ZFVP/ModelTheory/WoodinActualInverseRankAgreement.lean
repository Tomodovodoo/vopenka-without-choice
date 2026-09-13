import ZFVP.ModelTheory.WoodinInverseCodeRankAgreement
import ZFVP.ModelTheory.WoodinRawInverseSingular
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Completed inverse-code agreement with preservation inputs derived from the actual recursion. -/
theorem woodinIteration_eventually_rank_inverseSourceCode_eq {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hθ : θ ∈ δ) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    ∃ η ∈ δ, woodinLimitCardinal (woodinIterationCardinalPrefix θ) ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ t u C : SetDomain (hierarchy ξ), t.val = θ → u.val = woodinIterationPrefix θ → C.val = woodinIterationCardinalPrefix θ →
        (woodinInverseSourceCode t u C).val = woodinInverseSourceCode θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) ∧
          (woodinInverseCardinalNext t u C).val = woodinInverseCardinalNext θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) := by
  let := hδ.inaccessible.1
  have hx := woodinIterationExit hδ hAC
  have h := woodinIterationPrefix_of_stages
    (fun i hi ↦ (hx.2.1 i (IsOrdinal.toIsTransitive.mem_trans hi hθ)).1)
  have hzero : θ ≠ ∅ := by
    intro he
    rw [he] at h0
    simp at h0
  have hf := woodinRawInverseSingular hδ hθ hzero hlim hn
  have c := h.code.system.inverseColumn h0 h.code.subset_universe
  have hR := c.order.preorder
  have ht := c.tops.top
  let τ : ForcingName (forcingInverseCodePoset θ (woodinIterationPrefix θ)) :=
    ⟨checkName (forcingInverseCodeTop θ (woodinIterationPrefix θ))
      (woodinLimitCardinal (woodinIterationCardinalPrefix θ)), checkName_isName ht.1 _⟩
  apply h.eventually_rank_inverseSourceCode_eq hδ hθ h0 hlim
  · intro p hp
    apply forcingFormula_entailment singularLimitStageFormula
      (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_ hR ht hp ![τ] (hf p hp)
    intro W _ _ _ v hv
    have hh : IsLimitOfRegularCardinals (v 0) ∧ InternalDependentChoiceAt (v 0) :=
      (Defined.eval_iff _).mp hv
    change regularCardinalFormula.Evalb v ∨ limitOfRegularCardinalsFormula.Evalb v
    exact Or.inr ((Defined.eval_iff _).mpr hh.1)
  · intro p hp
    have hh := hf p hp
    rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.2
end ZFVP
