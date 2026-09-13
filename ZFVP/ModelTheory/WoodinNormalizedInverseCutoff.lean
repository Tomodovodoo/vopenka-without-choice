import ZFVP.ModelTheory.WoodinNormalizedInverseBase

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinNormalizedInverseCutoff (θ : V) : V :=
  let P := woodinNormalizedInverseBase θ
  let R := woodinNormalizedInverseOrder θ
  let one := forcingInverseCodeTop θ (woodinIterationPrefix θ)
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ))

instance woodinNormalizedInverseCutoff_definable : ℒₛₑₜ-function₁[V] woodinNormalizedInverseCutoff := by
  unfold woodinNormalizedInverseCutoff
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

variable {Ω θ : V} [IsOrdinal θ]
local notation "s" => woodinIterationPrefix θ
local notation "K" => woodinIterationCardinalPrefix θ
local notation "m" => woodinNormalizationHistory θ
local notation "P" => forcingInverseCodePoset θ s
local notation "R" => forcingInverseCodeOrder θ s
local notation "o" => forcingInverseCodeTop θ s
local notation "γ" => woodinLimitCardinal K
local notation "c" => forcingInverseSourceCutoff θ s γ
local notation "N" => woodinNormalizedInverseBase θ
local notation "T" => woodinNormalizedInverseOrder θ
local notation "d" => woodinNormalizedInverseCutoff θ

theorem woodinNormalizedInverseCutoff_eq
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (h0 : ∅ ∈ θ) :
    d = c := by
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC hθ
  obtain ⟨hr, ho, he⟩ := forcingNormalizationInverse_base hs.code hn h0
  have col := hs.code.system.inverseColumn h0 hs.code.subset_universe
  have ht : IsForcingTop P R o := col.tops.top
  have hT := forcingOrderRestriction_preorder col.order.preorder hr.inclusion
  have hone : o ∈ forcingMapFixedPoints P (forcingNormalizationInverseMap θ s m) :=
    mem_sep_iff.mpr ⟨ht.1, ho⟩
  have hh := hr.hartogs_prefix_cutoff col.order.preorder hT he ht hone γ
  obtain ⟨hb, hrel⟩ := woodinNormalized_inverse_base_dictionary hΩ hAC hθ
  rw [hb, hrel] at hh
  exact hh.symm

theorem woodinNormalizedInverseCutoff_bounds
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible γ) :
    d ∈ Ω ∧ IsChoicelessInaccessible d ∧ θ ∈ d ∧ N ∈ hierarchy d := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hx := woodinIterationExit hΩ hAC
  have hs := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hsub i hi)).1)
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hf := woodinRawInverseSingular hΩ hθ h0 hl hn
  have col := hs.code.system.inverseColumn hz hs.code.subset_universe
  let τ : ForcingName P := ⟨checkName o γ, checkName_isName col.tops.top.1 _⟩
  have hγ : ∀ p ∈ P, p ∈ forcingFormula P R (regularCardinalFormula.or limitOfRegularCardinalsFormula)
      (standardTuple ![τ.val]) := by
    intro p hp
    apply forcingFormula_entailment singularLimitStageFormula
      (regularCardinalFormula.or limitOfRegularCardinalsFormula) ?_
      col.order.preorder col.tops.top hp ![τ] (hf p hp)
    intro W _ _ _ v hv
    have hh : IsLimitOfRegularCardinals (v 0) ∧ InternalDependentChoiceAt (v 0) := (Defined.eval_iff _).mp hv
    change regularCardinalFormula.Evalb v ∨ limitOfRegularCardinalsFormula.Evalb v
    exact Or.inr ((Defined.eval_iff _).mpr hh.1)
  have hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![τ.val]) := by
    intro p hp
    have hh := hf p hp
    rw [singularLimitStageFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.2
  obtain ⟨hcΩ, hc⟩ := hs.inverse_sourceCutoff hΩ hθ hz hγ hDC
  let := hc.2.1.1
  let := hs.limitCardinal_ordinal
  have hP := (hs.inverse_small_above_limit hl hc.2.1 hc.1).1
  have hN : N ⊆ P := by
    rw [← (woodinNormalized_inverse_base_dictionary hΩ hAC hsub).1]
    exact sep_subset
  rw [woodinNormalizedInverseCutoff_eq hΩ hAC hsub hz]
  exact ⟨hcΩ, hc.2.1, ordinal_mem_of_subset_mem (hs.index_subset_limit hl) hc.1,
    subset_mem_hierarchy_limit hc.2.1.rankCriterion.2.2.1 hP hN⟩

end ZFVP
