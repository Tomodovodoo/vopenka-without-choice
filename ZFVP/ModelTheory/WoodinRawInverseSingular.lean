import ZFVP.ModelTheory.WoodinConstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinRawInverseSingularFormula : SetTheorySemisentence 1 :=
  f“θ. ∀ p ∈ !forcingInverseCodePosetFormula θ (!woodinIterationPrefixFormula θ),
    !(checkedUnaryForcingFormula singularLimitStageFormula)
      (!forcingInverseCodePosetFormula θ (!woodinIterationPrefixFormula θ))
      (!forcingInverseCodeOrderFormula θ (!woodinIterationPrefixFormula θ))
      (!forcingInverseCodeTopFormula θ (!woodinIterationPrefixFormula θ)) p
      (!woodinLimitCardinalFormula (!woodinIterationCardinalPrefixFormula θ))”

@[irreducible] def woodinRawInverseSingularTransferFormula : SetTheorySemisentence 2 :=
  f“δ θ. !woodinSupercompactFormula δ → θ ∈ δ → θ ≠ !isEmpty →
    (∀ i ∈ θ, !succ.dfn i ∈ θ) →
    ¬!choicelessInaccessibleFormula (!woodinLimitCardinalFormula (!woodinIterationCardinalPrefixFormula θ)) →
    !woodinRawInverseSingularFormula θ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Preservation at the checked limit cardinal before the completed inverse collapse. -/
def WoodinRawInverseSingular (θ : V) : Prop :=
  ∀ p ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
    p ∈ forcingFormula (forcingInverseCodePoset θ (woodinIterationPrefix θ))
      (forcingInverseCodeOrder θ (woodinIterationPrefix θ)) singularLimitStageFormula
      (standardTuple ![checkName (forcingInverseCodeTop θ (woodinIterationPrefix θ))
        (woodinLimitCardinal (woodinIterationCardinalPrefix θ))])

instance woodinRawInverseSingularFormula_defined : ℒₛₑₜ-predicate[V] WoodinRawInverseSingular
    via woodinRawInverseSingularFormula :=
  ⟨fun v ↦ by simp [woodinRawInverseSingularFormula, WoodinRawInverseSingular]⟩

theorem woodinRawInverseSingular_countable [Countable V] {δ θ : V}
    (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : θ ≠ ∅)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    WoodinRawInverseSingular θ := by
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
  exact hf

instance woodinRawInverseSingularTransferFormula_defined : Defined
    (fun v : Fin 2 → V ↦ IsWoodinSupercompact (v 0) → v 1 ∈ v 0 → v 1 ≠ ∅ →
      (∀ i ∈ v 1, succ i ∈ v 1) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (v 1))) →
      WoodinRawInverseSingular (v 1)) woodinRawInverseSingularTransferFormula :=
  ⟨fun v ↦ by simp [woodinRawInverseSingularTransferFormula]⟩

/-- The raw-stage assertion holds over arbitrary internal ZF grounds. -/
theorem woodinRawInverseSingular {δ θ : V}
    (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : θ ≠ ∅)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    WoodinRawInverseSingular θ := by
  have hv : woodinRawInverseSingularTransferFormula.Evalb (![δ, θ] : Fin 2 → V) := by
    apply eval_of_countable_zf woodinRawInverseSingularTransferFormula
    intro W _ _ _ _ w
    exact (Defined.eval_iff _).mpr (fun hδ hθ h0 hlim hn ↦ woodinRawInverseSingular_countable hδ hθ h0 hlim hn)
  exact (Defined.eval_iff _).mp hv hδ hθ h0 hlim hn

end ZFVP
