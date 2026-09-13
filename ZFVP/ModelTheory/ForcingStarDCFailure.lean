import ZFVP.ModelTheory.ClosedModelForcingReflection
import ZFVP.ModelTheory.ForcingCnOneTruth
import ZFVP.SetTheory.BoundedStarDependentChoiceBelow

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def closedModelRankData (P R one α θ : V) : V :=
  ⟨⟨P, R⟩ₖ, ⟨one, ⟨forcingNameHierarchy P α, hierarchy θ⟩ₖ⟩ₖ⟩ₖ

theorem ForcingContext.closedModelRankData_properties (A : ForcingContext V) {U α θ : V}
    [IsOrdinal α] (ht : IsTransitive U) (hm : IsInternalZFModel U)
    (hc : IsRankFunctionClosed θ U) (hd : closedModelRankData A.P A.R A.one α θ ∈ U)
    (hsub : forcingNameHierarchy A.P α ×ˢ A.P ⊆ hierarchy θ) :
    IsRankFunctionClosed (A.check α) (A.closedModelDomain U) ∧
      hierarchy (A.check α) ∈ A.closedModelDomain U ∧ IsTransitive (A.closedModelDomain U) ∧
        IsFunctionRestrictionClosed (A.closedModelDomain U) := by
  let := ht
  let : Nonempty (SetDomain U) := ⟨⟨_, hd⟩⟩
  let := hm.models_zf
  obtain ⟨hPR, hoH⟩ := kpair_components_mem_transitive hd
  obtain ⟨hP, hR⟩ := kpair_components_mem_transitive hPR
  obtain ⟨ho, hHθ⟩ := kpair_components_mem_transitive hoH
  obtain ⟨hH, hθ⟩ := kpair_components_mem_transitive hHθ
  let H : SetDomain U := ⟨forcingNameHierarchy A.P α, hH⟩
  let P : SetDomain U := ⟨A.P, hP⟩
  have hD : forcingNameHierarchy A.P α ×ˢ A.P ∈ U := TransitiveZF.prod_val U H P ▸ (H ×ˢ P).property
  have hclosed := TransitiveZF.rankFunctionClosed_on hc hθ hD hsub
  let := A.closedModelDomain_transitive U
  let := A.closedModelDomain_models_zf hP hR ho
  exact ⟨A.closedModelDomain_rankFunctionClosed hP hR ho α hH hclosed,
    A.hierarchy_mem_closedModelDomain hP hR ho α hH, inferInstance,
    TransitiveZF.functionRestrictionClosed _⟩

theorem boundedDCFailure_of_counterexample {κ B C R : V} [IsOrdinal κ]
    (ht : IsTransitive B) (hr : IsFunctionRestrictionClosed B)
    (hκ : κ ∈ B) (hc : B ^ κ ⊆ B) (hC : C ∈ B) (hR : R ∈ B) (hne : IsNonempty C)
    (hs : ∀ s ∈ shorterSequences κ C, ∃ x ∈ C, ⟨s, x⟩ₖ ∈ R)
    (hno : ∀ f ∈ C ^ κ, ∃ β ∈ κ, ⟨f ↾ β, f ‘ β⟩ₖ ∉ R) :
    IsBoundedDependentChoiceFailure κ B := by
  have hshort := closedContainer_shortFunctions ht hr hκ hc
  refine ⟨C, hC, R, hR, hne, ?_, ?_⟩
  · intro β hβ s _ hsf
    exact hs s ((mem_shorterSequences _ _ _).mpr ⟨β, hβ, hsf⟩)
  · intro f _ hpath
    have hp := (boundedDependentChoicePath_iff
      (fun β hβ r hrf ↦ hshort C hC β (mem_succ_iff.mpr (Or.inr hβ)) r hrf)).mp hpath
    obtain ⟨β, hβ, hn⟩ := hno f hp.1
    exact hn (hp.2 β hβ)

theorem ForcingContext.starDC_failure_witness_at (A : ForcingContext V)
    {δ γ α κ : V} (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ)
    (hP : A.P ∈ hierarchy γ) (hα : α ∈ γ) (hκ : κ ∈ α)
    (hfail : ¬InternalDependentChoiceAt (A.check κ)) :
    ∃ B ∈ hierarchy (A.check γ), IsRankFunctionClosed (A.check α) B ∧
      hierarchy (A.check α) ∈ B ∧ A.check κ ∈ B ∧ IsTransitive B ∧
        IsFunctionRestrictionClosed B ∧ IsBoundedDependentChoiceFailure (A.check κ) B := by
  classical
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hκ
  let D := forcingNameHierarchy A.P α ×ˢ A.P
  let θ := succ (rank D)
  have hDγ : D ∈ hierarchy γ := prod_mem_hierarchy_limit hγ.1.successor_closed
    (hγ.1.forcingNameHierarchy_closed hP hα) hP
  have hθγ : θ ∈ γ := hγ.1.successor_closed _ ((mem_hierarchy_iff_rank_mem _ _).mp hDγ)
  have hDθ : D ⊆ hierarchy θ := (hierarchy_transitive θ).transitive D
    ((mem_hierarchy_iff_rank_mem _ _).mpr (by simp [θ]))
  have hRγ : A.R ∈ hierarchy γ := subset_mem_hierarchy_limit hγ.1.successor_closed
    (prod_mem_hierarchy_limit hγ.1.successor_closed hP hP) A.order.1
  have hoγ : A.one ∈ hierarchy γ := (hierarchy_transitive γ).mem_trans A.top.1 hP
  have hθV : hierarchy θ ∈ hierarchy γ := hγ.1.hierarchy_closed inferInstance (ordinal_mem_hierarchy_iff.mpr hθγ)
  let d := closedModelRankData A.P A.R A.one α θ
  have hdγ : d ∈ hierarchy γ := kpair_mem_hierarchy_limit hγ.1.successor_closed
    (kpair_mem_hierarchy_limit hγ.1.successor_closed hP hRγ)
    (kpair_mem_hierarchy_limit hγ.1.successor_closed hoγ
      (kpair_mem_hierarchy_limit hγ.1.successor_closed (hγ.1.forcingNameHierarchy_closed hP hα) hθV))
  have hκγ : κ ∈ hierarchy γ := ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hκ hα)
  unfold InternalDependentChoiceAt at hfail
  push Not at hfail
  obtain ⟨C, R, hne, hs, hno⟩ := hfail
  obtain ⟨σ, rfl⟩ := A.ofName_surjective C
  obtain ⟨τ, rfl⟩ := A.ofName_surjective R
  obtain ⟨U, hc, hp, ht, hm⟩ := hδ.exists_rankClosed_internalZFModel θ ⟨d, ⟨σ.val, τ.val⟩ₖ⟩ₖ
  let := ht
  let : Nonempty (SetDomain U) := ⟨⟨_, hp⟩⟩
  let := hm.models_zf
  obtain ⟨hdU, hστ⟩ := kpair_components_mem_transitive hp
  obtain ⟨hσ, hτ⟩ := kpair_components_mem_transitive hστ
  have hprops := A.closedModelRankData_properties ht hm hc hdU hDθ
  have hkB : A.check κ ∈ A.closedModelDomain U := hprops.2.2.1.mem_trans
    (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff κ α).mpr hκ)) hprops.2.1
  have hcκ : (A.closedModelDomain U) ^ A.check κ ⊆ A.closedModelDomain U := by
    intro f hf
    exact hprops.2.2.2.function_mem hprops.1 hprops.2.1 hkB
      ((hierarchy_transitive (A.check α)).transitive _ (ordinal_mem_hierarchy_iff.mpr
        ((A.check_mem_iff κ α).mpr hκ))) ⟨A.check κ, hkB⟩ hf
  have hfB := boundedDCFailure_of_counterexample hprops.2.2.1 hprops.2.2.2 hkB hcκ
    ((A.mem_closedModelDomain U _).mpr ⟨σ, hσ, rfl⟩)
    ((A.mem_closedModelDomain U _).mpr ⟨τ, hτ, rfl⟩) hne hs hno
  let ν : ForcingName A.P := ⟨closedModelName A.P A.one U, closedModelName_isName A.top.1⟩
  let k : ForcingName A.P := ⟨checkName A.one κ, checkName_isName A.top.1 κ⟩
  have hev : boundedDependentChoiceFailureFormula.Evalb (A.ofName ∘ ![k, ν]) := by
    have hh : IsBoundedDependentChoiceFailure (A.ofName k) (A.ofName ν) := by
      rw [show A.ofName ν = A.closedModelDomain U from A.closedModelName_value U]
      exact hfB
    simpa [Function.comp_def] using (boundedDependentChoiceFailureFormula_defined.iff ![A.ofName k, A.ofName ν]).mpr hh
  obtain ⟨p, hpG, hpf⟩ := (A.formula_truth boundedDependentChoiceFailureFormula ![k, ν]).mp hev
  obtain ⟨U', hU', hc', hd', ht', hm', hf'⟩ := hγ.reflect_closedModel_forcing hδ hθγ hP hRγ hoγ
    ((hierarchy_transitive γ).mem_trans (A.generic.1.1 p hpG) hP) hκγ hdγ A.order A.top
    boundedDependentChoiceFailureFormula_bounded ⟨U, hc, hdU, ht, hm, hpf⟩
  have hprops' := A.closedModelRankData_properties ht' hm' hc' hd' hDθ
  have hkB' : A.check κ ∈ A.closedModelDomain U' := hprops'.2.2.1.mem_trans
    (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff κ α).mpr hκ)) hprops'.2.1
  let ν' : ForcingName A.P := ⟨closedModelName A.P A.one U', closedModelName_isName A.top.1⟩
  have hv := (A.formula_truth boundedDependentChoiceFailureFormula ![k, ν']).mpr ⟨p, hpG, hf'⟩
  have hfB' : IsBoundedDependentChoiceFailure (A.check κ) (A.closedModelDomain U') := by
    have hh : boundedDependentChoiceFailureFormula.Evalb ![A.ofName k, A.ofName ν'] := by
      simpa [Function.comp_def] using hv
    have ht' := (boundedDependentChoiceFailureFormula_defined.iff _).mp hh
    rwa [show A.ofName ν' = A.closedModelDomain U' from A.closedModelName_value U'] at ht'
  exact ⟨A.closedModelDomain U', A.closedModelDomain_mem_rank hγ.1 hP hU',
    hprops'.1, hprops'.2.1, hkB', hprops'.2.2.1, hprops'.2.2.2, hfB'⟩

theorem ForcingContext.boundedStarDC_iff_at (A : ForcingContext V)
    {δ γ α κ : V} (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ)
    (hP : A.P ∈ hierarchy γ) (hα : α ∈ γ) (hκ : κ ∈ α) :
    boundedStarDCFormula.Evalb ![A.check κ, hierarchy (A.check α), hierarchy (A.check γ)] ↔
      InternalDependentChoiceAt (A.check κ) := by
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hκ
  have hcn := A.cn_one_check hγ.1 hP
  have hD : hierarchy (A.check α) ∈ hierarchy (A.check γ) := hcn.hierarchy_closed inferInstance
    (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff _ _).mpr hα))
  rw [eval_boundedStarDCFormula]
  constructor
  · intro h
    by_contra hn
    obtain ⟨B, hB, hc, hDB, hκB, ht, hr, hf⟩ := A.starDC_failure_witness_at hδ hγ hP hα hκ hn
    exact h B hB ((boundedFunctionClosed_rank_iff hcn hD hB).mpr hc) hκB hDB ht hr hf
  · intro hDC B hB hc hκB hDB ht hr hf
    have hcD := (boundedFunctionClosed_rank_iff hcn hD hB).mp hc
    have hκD : A.check κ ⊆ hierarchy (A.check α) := (hierarchy_transitive (A.check α)).transitive _
      (ordinal_mem_hierarchy_iff.mpr ((A.check_mem_iff κ α).mpr hκ))
    have hcκ : B ^ A.check κ ⊆ B := fun f hff ↦ hr.function_mem hcD hDB hκB hκD ⟨A.check κ, hκB⟩ hff
    exact hf.not_dependentChoice (closedContainer_shortFunctions ht hr hκB hcκ) hDC

theorem ForcingContext.boundedStarDCBelow_iff_at (A : ForcingContext V)
    {δ γ α κ : V} (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ)
    (hP : A.P ∈ hierarchy γ) (hα : α ∈ γ) (hκ : κ ∈ α) :
    boundedStarDCBelowFormula.Evalb ![A.check κ, hierarchy (A.check α), hierarchy (A.check γ)] ↔
      ∀ η ∈ A.check κ, InternalDependentChoiceAt η := by
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  rw [eval_boundedStarDCBelowFormula]
  constructor
  · intro h η hη
    obtain ⟨ξ, hξ, rfl⟩ := (A.mem_check_iff κ η).mp hη
    exact (A.boundedStarDC_iff_at hδ hγ hP hα (IsOrdinal.toIsTransitive.mem_trans hξ hκ)).mp
      (h _ ((A.check_mem_iff _ _).mpr hξ))
  · intro h η hη
    obtain ⟨ξ, hξ, rfl⟩ := (A.mem_check_iff κ η).mp hη
    exact (A.boundedStarDC_iff_at hδ hγ hP hα (IsOrdinal.toIsTransitive.mem_trans hξ hκ)).mpr
      (h _ ((A.check_mem_iff _ _).mpr hξ))

end ZFVP
