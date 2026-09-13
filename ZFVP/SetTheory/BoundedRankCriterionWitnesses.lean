import ZFVP.ModelTheory.LimitRankEmbedding

/-! Bounded witnesses to the failure of earlier rank criteria can all be placed below the candidate height. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedLowRankCofinalWitnessFormula : SetTheorySemisentence 2 :=
  “W η. ∃ a ∈ W, ∃ f ∈ W, ∃ r ∈ η, ∃ T ∈ W, ∃ R ∈ W, ∃ g ∈ W,
    !IsTransitive.dfn T ∧ a ∈ T ∧ !boundedRankTableFormula T R g ∧
    !boundedPairMemberFormula g a r ∧ !boundedCofinalMapFormula η a f”

def boundedNoEarlierRankCriterionMatrix : SetTheorySemisentence 3 :=
  “W θ b. ∀ η ∈ θ, b ∈ η →
    (¬!limitAboveOmegaFormula η ∨ !boundedLowRankCofinalWitnessFormula W η)”

theorem boundedLowRankCofinalWitnessFormula_bounded : IsBoundedSetFormula boundedLowRankCofinalWitnessFormula := by
  repeat' first
    | exact isTransitiveFormula_bounded.subst _
    | exact boundedRankTableFormula_bounded.subst _
    | exact boundedPairMemberFormula_bounded.subst _
    | exact boundedCofinalMapFormula_bounded.subst _
    | exact IsBoundedSetFormula.rel _ _
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and

theorem boundedNoEarlierRankCriterionMatrix_bounded : IsBoundedSetFormula boundedNoEarlierRankCriterionMatrix :=
  .all (.bvar 1) (.or (.nrel _ _) (.or (limitAboveOmegaFormula_bounded.subst _).neg
    (boundedLowRankCofinalWitnessFormula_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedLowRankCofinalWitnessFormula (W η : V) :
    boundedLowRankCofinalWitnessFormula.Evalb ![W, η] ↔
      ∃ a ∈ W, ∃ f ∈ W, ∃ r ∈ η, ∃ T ∈ W, ∃ R ∈ W, ∃ g ∈ W,
        IsTransitive T ∧ a ∈ T ∧ boundedRankTableFormula.Evalb ![T, R, g] ∧
          ⟨a, r⟩ₖ ∈ g ∧ IsCofinalMap η a f := by
  simp [boundedLowRankCofinalWitnessFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def]

theorem boundedLowRankCofinalWitnessFormula_sound {W η : V} [IsOrdinal η]
    (h : boundedLowRankCofinalWitnessFormula.Evalb ![W, η]) : ¬NoLowRankCofinalMaps η := by
  obtain ⟨a, _, f, _, r, hr, T, _, R, _, g, _, hT, ha, hg, hp, hf⟩ :=
    (eval_boundedLowRankCofinalWitnessFormula W η).mp h
  let := hT
  have htable := (eval_boundedRankTableFormula R g).mp hg
  let := IsFunction.of_mem htable.1
  have he : rank a = r := (rankTable_correct htable a ha).symm.trans (value_eq_of_kpair_mem hp)
  intro hn
  exact hn a ((mem_hierarchy_iff_rank_mem a η).mpr (he.symm ▸ hr)) f hf

theorem boundedLowRankCofinalWitnessFormula_complete {θ η : V} [IsOrdinal θ]
    (hs : ∀ β ∈ θ, succ β ∈ θ) (hη : η ∈ θ) (hn : ¬NoLowRankCofinalMaps η) :
    boundedLowRankCofinalWitnessFormula.Evalb ![hierarchy θ, η] := by
  let : IsOrdinal η := IsOrdinal.of_mem hη
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  simp only [NoLowRankCofinalMaps, not_forall, not_not] at hn
  obtain ⟨a, ha, f, hf⟩ := hn
  have hT : hierarchy η ∈ hierarchy θ := hierarchy_mem hη
  have haθ := (hierarchy_transitive θ).mem_trans ha hT
  have hηθ : η ∈ hierarchy θ := ordinal_subset_hierarchy θ η hη
  have hfθ := (hierarchy_transitive θ).mem_trans hf.1 (function_mem_hierarchy_limit hs haθ hηθ)
  obtain ⟨g, hgθ, hg⟩ := rankTable_exists_in_limit hs hT
  have hRθ : rank (hierarchy η) ∈ hierarchy θ := by simpa only [rank_hierarchy] using hηθ
  have he : g ‘ a = rank a := rankTable_correct hg a ha
  let := IsFunction.of_mem hg.1
  apply (eval_boundedLowRankCofinalWitnessFormula _ _).mpr
  refine ⟨a, haθ, f, hfθ, rank a, (mem_hierarchy_iff_rank_mem a η).mp ha,
    hierarchy η, hT, rank (hierarchy η), hRθ, g, hgθ, inferInstance, ha,
    (eval_boundedRankTableFormula _ _).mpr hg, ?_, hf⟩
  exact kpair_mem_iff_value.mpr ⟨by simpa only [domain_eq_of_mem_function hg.1] using ha, he⟩

theorem eval_boundedNoEarlierRankCriterionMatrix (W θ b : V) :
    boundedNoEarlierRankCriterionMatrix.Evalb ![W, θ, b] ↔
      ∀ η ∈ θ, b ∈ η →
        ¬(IsOrdinal η ∧ (ω : V) ∈ η ∧ ∀ x ∈ η, succ x ∈ η) ∨
          boundedLowRankCofinalWitnessFormula.Evalb ![W, η] := by
  simp [boundedNoEarlierRankCriterionMatrix, eval_limitAboveOmegaFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem boundedNoEarlierRankCriterionMatrix_sound {W θ b : V}
    (h : boundedNoEarlierRankCriterionMatrix.Evalb ![W, θ, b]) :
    ∀ η ∈ θ, b ∈ η → ¬IsRankCriterionHeight η := by
  intro η hη hb hc
  let := hc.1
  rcases (eval_boundedNoEarlierRankCriterionMatrix W θ b).mp h η hη hb with hn | hw
  · exact hn ⟨hc.1, hc.2.1, hc.2.2.1⟩
  · exact boundedLowRankCofinalWitnessFormula_sound hw hc.2.2.2

theorem boundedNoEarlierRankCriterionMatrix_complete {θ b : V} [IsOrdinal θ]
    (hs : ∀ β ∈ θ, succ β ∈ θ) (hn : ∀ η ∈ θ, b ∈ η → ¬IsRankCriterionHeight η) :
    boundedNoEarlierRankCriterionMatrix.Evalb ![hierarchy θ, θ, b] := by
  apply (eval_boundedNoEarlierRankCriterionMatrix _ _ _).mpr
  intro η hη hb
  by_cases hl : IsOrdinal η ∧ (ω : V) ∈ η ∧ ∀ x ∈ η, succ x ∈ η
  · refine Or.inr (boundedLowRankCofinalWitnessFormula_complete hs hη ?_)
    intro hc
    exact hn η hη hb ⟨hl.1, hl.2.1, hl.2.2, hc⟩
  · exact Or.inl hl

end ZFVP
