import ZFVP.ModelTheory.SigmaThreeWoodinRecursion
import ZFVP.ModelTheory.WoodinRawInverseSingular

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

@[irreducible] def woodinRecursionComplexityTransferFormula
    (σ π σH πH : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“δ θ. !woodinSupercompactFormula δ → θ ∈ δ → ∀ z,
    ((!σ z θ ↔ z = !woodinIterationRecFormula θ) ∧
      (!π z θ ↔ z = !woodinIterationRecFormula θ) ∧
      (!σH z θ ↔ z = !woodinIterationHistoryFormula θ) ∧
      (!πH z θ ↔ z = !woodinIterationHistoryFormula θ))”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinRecursionComplexityTransferFormula_defined (σ π σH πH : SetTheorySemisentence 2) :
    Defined (fun v : Fin 2 → V ↦ IsWoodinSupercompact (v 0) → v 1 ∈ v 0 → ∀ z : V,
      (σ.Evalb ![z, v 1] ↔ z = woodinIterationRec (v 1)) ∧
      (π.Evalb ![z, v 1] ↔ z = woodinIterationRec (v 1)) ∧
      (σH.Evalb ![z, v 1] ↔ z = woodinIterationHistory (v 1)) ∧
      (πH.Evalb ![z, v 1] ↔ z = woodinIterationHistory (v 1)))
      (woodinRecursionComplexityTransferFormula σ π σH πH) :=
  ⟨fun v ↦ by simp [woodinRecursionComplexityTransferFormula, Semiformula.Evalb]⟩

/-- Uniform Delta-three definitions of the actual recursion and its history below
any Woodin supercompact cardinal. The construction supplies every inverse input. -/
theorem woodinRecursion_deltaThree_uniform :
    ∃ σ π σH πH : SetTheorySemisentence 2,
      IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧ IsSigmaFormula 3 σH ∧ IsPiFormula 3 πH ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ θ : V,
        IsWoodinSupercompact δ → θ ∈ δ → ∀ z,
          (σ.Evalb ![z, θ] ↔ z = woodinIterationRec θ) ∧
          (π.Evalb ![z, θ] ↔ z = woodinIterationRec θ) ∧
          (σH.Evalb ![z, θ] ↔ z = woodinIterationHistory θ) ∧
          (πH.Evalb ![z, θ] ↔ z = woodinIterationHistory θ) := by
  obtain ⟨σ, π, σH, πH, hσ, hπ, hσH, hπH, he⟩ :=
    woodinRecursion_deltaThree_on_prefixes_of_inverse_forcing.{u}
  refine ⟨σ, π, σH, πH, hσ, hπ, hσH, hπH, ?_⟩
  intro V _ _ _ δ θ hδ hθ
  have hv : (woodinRecursionComplexityTransferFormula σ π σH πH).Evalb (![δ, θ] : Fin 2 → V) := by
    apply eval_of_countable_zf
    intro W _ _ _ _ v
    apply (Defined.eval_iff _).mpr
    intro hδ hθ
    let := hδ.inaccessible.1
    let := IsOrdinal.of_mem hθ
    have hstages := woodinIteration_stages_countable hδ
    have hbelow : ∀ β ∈ succ (v 1), β ∈ v 0 := by
      intro β hβ
      rcases mem_succ_iff.mp hβ with rfl | hb
      · exact hθ
      · exact IsOrdinal.toIsTransitive.mem_trans hb hθ
    have hvalid : ∀ β ∈ succ (v 1), IsWoodinIteration (v 0) β
        (woodinIterationPrefix β) (woodinIterationCardinalPrefix β) := by
      intro β hβ
      let := IsOrdinal.of_mem hβ
      exact woodinIterationPrefix_of_stages
        (fun k hk ↦ (hstages k (IsOrdinal.toIsTransitive.mem_trans hk (hbelow β hβ))).1)
    have hraw : ∀ β ∈ succ (v 1), β ≠ ∅ → β ≠ succ (⋃ˢ β) →
        ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix β)) →
        ∀ p ∈ forcingInverseCodePoset β (woodinIterationPrefix β),
          p ∈ forcingFormula (forcingInverseCodePoset β (woodinIterationPrefix β))
            (forcingInverseCodeOrder β (woodinIterationPrefix β)) singularLimitStageFormula
            (standardTuple ![checkName (forcingInverseCodeTop β (woodinIterationPrefix β))
              (woodinLimitCardinal (woodinIterationCardinalPrefix β))]) := by
      intro β hβ hz hs hn
      let := IsOrdinal.of_mem hβ
      exact woodinRawInverseSingular_countable hδ (hbelow β hβ) hz
        (ordinal_limit_of_not_successor hs) hn
    apply he W (v 0) (v 1) inferInstance hδ hθ hvalid
    · intro β hβ hz hs hn p hp
      let := IsOrdinal.of_mem hβ
      have h0 : (∅ : W) ∈ β := (IsOrdinal.subset_iff.mp (empty_subset β)).resolve_left
        (fun hzero ↦ hz hzero.symm)
      have hc := (hvalid β hβ).code.system.inverseColumn h0 (hvalid β hβ).code.subset_universe
      let τ : ForcingName (forcingInverseCodePoset β (woodinIterationPrefix β)) :=
        ⟨checkName (forcingInverseCodeTop β (woodinIterationPrefix β))
          (woodinLimitCardinal (woodinIterationCardinalPrefix β)), checkName_isName hc.tops.top.1 _⟩
      apply forcingFormula_entailment singularLimitStageFormula
        (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_
        hc.order.preorder hc.tops.top hp ![τ] (hraw β hβ hz hs hn p hp)
      intro U _ _ _ a ha
      have hh : IsLimitOfRegularCardinals (a 0) ∧ InternalDependentChoiceAt (a 0) :=
        (Defined.eval_iff _).mp ha
      change regularCardinalFormula.Evalb a ∨ limitOfRegularCardinalsFormula.Evalb a
      exact Or.inr ((Defined.eval_iff _).mpr hh.1)
    · intro β hβ hz hs hn p hp
      have hh := hraw β hβ hz hs hn p hp
      rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hh
      exact hh.2
  exact (Defined.eval_iff _).mp hv hδ hθ

end ZFVP
