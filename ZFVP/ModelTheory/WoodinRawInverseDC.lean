import ZFVP.ModelTheory.WoodinConstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinRawInverseDCFormula : SetTheorySemisentence 1 :=
  f“θ. ∀ p ∈ !forcingInverseCodePosetFormula θ (!woodinIterationPrefixFormula θ),
    !(namedUnaryForcingFormula woodinStageCardinalFormula)
      (!forcingInverseCodePosetFormula θ (!woodinIterationPrefixFormula θ))
      (!forcingInverseCodeOrderFormula θ (!woodinIterationPrefixFormula θ)) p
      (!forcingInverseHartogsNameFormula θ (!woodinIterationPrefixFormula θ)
        (!woodinLimitCardinalFormula (!woodinIterationCardinalPrefixFormula θ)))”

@[irreducible] def woodinRawInverseDCTransferFormula : SetTheorySemisentence 2 :=
  f“δ θ. !woodinSupercompactFormula δ → θ ∈ δ → θ ≠ !isEmpty →
    (∀ i ∈ θ, !succ.dfn i ∈ θ) →
    ¬!choicelessInaccessibleFormula (!woodinLimitCardinalFormula (!woodinIterationCardinalPrefixFormula θ)) →
    !woodinRawInverseDCFormula θ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The raw inverse limit forces regularity and DC below its own extension's
Hartogs successor, before the additional collapse. -/
def WoodinRawInverseDC (θ : V) : Prop :=
  ∀ p ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
    p ∈ forcingFormula (forcingInverseCodePoset θ (woodinIterationPrefix θ))
      (forcingInverseCodeOrder θ (woodinIterationPrefix θ)) woodinStageCardinalFormula
      (standardTuple ![forcingInverseHartogsName θ (woodinIterationPrefix θ)
        (woodinLimitCardinal (woodinIterationCardinalPrefix θ))])

instance woodinRawInverseDCFormula_defined : ℒₛₑₜ-predicate[V] WoodinRawInverseDC
    via woodinRawInverseDCFormula :=
  ⟨fun v ↦ by simp [woodinRawInverseDCFormula, WoodinRawInverseDC]⟩

theorem woodinRawInverseDC_countable [Countable V] {δ θ : V}
    (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : θ ≠ ∅)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    WoodinRawInverseDC θ := by
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hθ
  have hs := woodinIteration_stages_countable hδ
  have h := woodinIterationPrefix_of_stages
    (fun k hk ↦ (hs k (IsOrdinal.toIsTransitive.mem_trans hk hθ)).1)
  let := h.limitCardinal_ordinal
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left
    (fun he ↦ h0 he.symm)
  have hf := h.inverse_stage_forced_of_quotient_closure hzero hlim hn
    (fun i hi ↦ woodinRawInverse_code_quotient_closedBelow
      (fun k hk ↦ (hs k (IsOrdinal.toIsTransitive.mem_trans hk hθ)).1)
      (fun k hk ↦ (hs k (IsOrdinal.toIsTransitive.mem_trans hk hθ)).2) hi)
  have col := h.code.system.inverseColumn hzero h.code.subset_universe
  let τ : ForcingName (forcingInverseCodePoset θ (woodinIterationPrefix θ)) :=
    ⟨checkName (forcingInverseCodeTop θ (woodinIterationPrefix θ))
      (woodinLimitCardinal (woodinIterationCardinalPrefix θ)), checkName_isName col.tops.top.1 _⟩
  intro p hp
  have hsing := hf p hp
  have hdc := hsing
  rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hdc
  rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff]
  refine ⟨?_, hartogsNumberName_forces_dependentChoiceBelow col.order.preorder col.tops.top hp τ
    (forces_checked_ordinal col.order.preorder col.tops.top inferInstance hp) hdc.2⟩
  apply hartogsNumberName_forces_regular col.order.preorder col.tops.top hp τ ?_ hdc.2
  apply forcingFormula_entailment singularLimitStageFormula
    (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_ col.order.preorder col.tops.top hp ![τ] hsing
  intro W _ _ _ v hv
  have hh : IsLimitOfRegularCardinals (v 0) ∧ InternalDependentChoiceAt (v 0) :=
    (Defined.eval_iff _).mp hv
  change regularCardinalFormula.Evalb v ∨ limitOfRegularCardinalsFormula.Evalb v
  exact Or.inr ((Defined.eval_iff _).mpr hh.1)

instance woodinRawInverseDCTransferFormula_defined : Defined
    (fun v : Fin 2 → V ↦ IsWoodinSupercompact (v 0) → v 1 ∈ v 0 → v 1 ≠ ∅ →
      (∀ i ∈ v 1, succ i ∈ v 1) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (v 1))) →
      WoodinRawInverseDC (v 1)) woodinRawInverseDCTransferFormula :=
  ⟨fun v ↦ by simp [woodinRawInverseDCTransferFormula]⟩

/-- The raw-stage assertion holds over arbitrary internal ZF grounds. -/
theorem woodinRawInverseDC {δ θ : V}
    (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : θ ≠ ∅)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    WoodinRawInverseDC θ := by
  have hv : woodinRawInverseDCTransferFormula.Evalb (![δ, θ] : Fin 2 → V) := by
    apply eval_of_countable_zf woodinRawInverseDCTransferFormula
    intro W _ _ _ _ w
    exact (Defined.eval_iff _).mpr (fun hδ hθ h0 hlim hn ↦ woodinRawInverseDC_countable hδ hθ h0 hlim hn)
  exact (Defined.eval_iff _).mp hv hδ hθ h0 hlim hn

end ZFVP
