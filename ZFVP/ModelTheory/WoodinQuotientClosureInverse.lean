import ZFVP.ModelTheory.InverseSourceQuotientClosure
import ZFVP.ModelTheory.WoodinInverseStagePreservation
import ZFVP.ModelTheory.WoodinHistoryQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem HasWoodinQuotientClosure.inverse_source {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ)
    (hc : HasWoodinQuotientClosure θ s K) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hraw : ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ s) i θ (K ‘ i)) :
    HasWoodinQuotientClosure (succ θ) (woodinInverseSourceCode θ s K)
      (woodinInverseCardinalNext θ s K) := by
  have hn := h.inverse_source hδ hθ h0 hlim hγ hDC
  obtain ⟨_, hcut⟩ := h.inverse_sourceCutoff hδ hθ h0 hγ hDC
  have hs := h.inverse_small_above_limit hlim hcut.2.1 hcut.1
  have col := h.code.system.inverseColumn h0 h.code.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := col.tops.top
  let ν : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K), checkName_isName ht.1 _⟩
  have hκ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        regularCardinalFormula (standardTuple ![forcingInverseHartogsName θ s (woodinLimitCardinal K)]) :=
    fun p hp ↦ hartogsNumberName_forces_regular col.order.preorder ht hp ν (hγ p hp) (hDC p hp)
  intro i hi j hj hij
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases mem_succ_iff.mp hj with rfl | hj
  · rcases mem_succ_iff.mp hi with rfl | hi
    · exact hn.code.diagonal_quotient_closedBelow (mem_succ_self _) _
    · rw [show (woodinInverseCardinalNext _ s K) ‘ i = K ‘ i from forcingFamilyNext_old hi]
      let := (h.inaccessible i hi).1
      let := h.limitCardinal_ordinal
      apply inverseSourceCollapseCode_quotient_closedBelow h.code h0 hi hcut.2.1 hs.1 hcut.1 hκ
        (IsOrdinal.toIsTransitive.transitive _ (h.cardinal_mem_limit hlim hi)) ?_ (hraw i hi)
      simpa only [woodinIterationStage, woodinStagePoset_code, woodinStageOrder_code,
        woodinStageTop_code, woodinStageCardinal_code] using (h.stage i hi).2.2.2.2
  · have hiold : i ∈ θ := ordinal_mem_of_subset_mem hij hj
    rw [show (woodinInverseCardinalNext θ s K) ‘ i = K ‘ i from forcingFamilyNext_old hiold]
    exact (hc i hiold j hj hij).of_code_extension h.code hn.code
      (forcingInverseSourceCollapseCode_extends h.code _ _) hiold hj

theorem HasWoodinQuotientClosure.inverse_source_of_raw_closure {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ)
    (hc : HasWoodinQuotientClosure θ s K) (h0 : ∅ ∈ θ) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal K))
    (hraw : ∀ i ∈ θ, IterationQuotientClosedBelow (forcingInverseCode θ s) i θ (K ‘ i)) :
    HasWoodinQuotientClosure (succ θ) (woodinInverseSourceCode θ s K)
      (woodinInverseCardinalNext θ s K) := by
  have hf := h.inverse_stage_forced_of_quotient_closure h0 hlim hn hraw
  have col := h.code.system.inverseColumn h0 h.code.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := col.tops.top
  let ν : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K), checkName_isName ht.1 _⟩
  apply hc.inverse_source h hδ hθ h0 hlim ?_ ?_ hraw
  · intro p hp
    apply forcingFormula_entailment singularLimitStageFormula
      (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_ col.order.preorder ht hp ![ν] (hf p hp)
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
