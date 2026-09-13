import ZFVP.ModelTheory.DerivedUltrafilter

/-! Completeness of the derived ultrafilter for every internal ordinal index below the critical point. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedIntersectionAtFormula : SetTheorySemisentence 4 :=
  “z I P g. ∀ i ∈ I, ∃ Y ∈ P, !boundedPairMemberFormula g i Y ∧ z ∈ Y”

def boundedIndexedIntersectionFormula : SetTheorySemisentence 5 :=
  “X K I P g. ∀ z ∈ K, z ∈ X ↔ !boundedIntersectionAtFormula z I P g”

theorem boundedIntersectionAtFormula_bounded : IsBoundedSetFormula boundedIntersectionAtFormula :=
  .all (.bvar 1) (.exs (.bvar 3)
    (.and (boundedPairMemberFormula_bounded.subst _) (.rel _ _)))

theorem boundedIndexedIntersectionFormula_bounded : IsBoundedSetFormula boundedIndexedIntersectionFormula :=
  .all (.bvar 1) (.and
    (.or (.nrel _ _) (boundedIntersectionAtFormula_bounded.subst _))
    (.or (boundedIntersectionAtFormula_bounded.subst _).neg (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedIntersectionAtFormula {I P g : V} (hf : g ∈ P ^ I) (z : V) :
    boundedIntersectionAtFormula.Evalb ![z, I, P, g] ↔ ∀ i ∈ I, z ∈ g ‘ i := by
  let := IsFunction.of_mem hf
  simp [boundedIntersectionAtFormula]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  constructor
  · rintro ⟨Y, _, hp, hz⟩
    exact (value_eq_of_kpair_mem hp).symm ▸ hz
  · intro hz
    exact ⟨g ‘ i, function_value_mem hf hi,
      kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hi), hz⟩

theorem boundedIndexedIntersectionFormula_holds (K : V) {I P g : V} (hf : g ∈ P ^ I) :
    boundedIndexedIntersectionFormula.Evalb ![indexedIntersection K I g, K, I, P, g] := by
  simp (config := { contextual := true })
    [boundedIndexedIntersectionFormula, eval_boundedIntersectionAtFormula hf]

theorem derivedUltrafilter_complete {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B] (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : IsOrdinalComplete κ (derivedUltrafilter κ f) := by
  let := hκ.ordinal
  let := hierarchy_transitive δ
  intro α hα g hg
  have hαδ := (hierarchy_transitive δ).mem_trans hα hκ.mem_domain
  have hP : ℘ κ ∈ hierarchy δ := power_mem_hierarchy_limit hδ hκ.mem_domain
  have hgp : g ∈ (℘ κ) ^ α := mem_function_of_mem_function_of_subset hg
    (derivedUltrafilter_isUltrafilter hδ h hκ).1
  have hgδ := (hierarchy_transitive δ).mem_trans hgp
    (function_mem_hierarchy_limit hδ hαδ hP)
  have hsub : indexedIntersection κ α g ⊆ κ :=
    fun z hz ↦ (mem_indexedIntersection_iff _ _ _ _ |>.mp hz).1
  have hX : indexedIntersection κ α g ∈ hierarchy δ :=
    subset_mem_hierarchy_limit hδ hκ.mem_domain hsub
  refine (mem_derivedUltrafilter_iff _ _ _).mpr ⟨hsub, ?_⟩
  have he := (h.bounded_formula_iff boundedIndexedIntersectionFormula_bounded
    ![indexedIntersection κ α g, κ, α, ℘ κ, g]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hX, hκ.mem_domain, hαδ, hP, hgδ])).mp
      (boundedIndexedIntersectionFormula_holds κ hgp)
  simp [boundedIndexedIntersectionFormula, boundedIntersectionAtFormula] at he
  apply (he κ (hκ.lt_value h)).mpr
  intro i hi
  rw [hκ.fixed_below hα] at hi
  have hiκ := IsOrdinal.toIsTransitive.mem_trans hi hα
  have hgiP := function_value_mem hgp hi
  have hgiδ := (hierarchy_transitive δ).mem_trans hgiP hP
  have hmap := h.value_function hgδ hαδ hP hgp
  let := IsFunction.of_mem hmap
  have hv := h.value_apply hgδ hαδ (IsFunction.of_mem hgp)
    (domain_eq_of_mem_function hgp) hi
  rw [hκ.fixed_below hiκ] at hv
  refine ⟨f ‘ (g ‘ i), (h.value_mem_iff hgiδ hP).mpr hgiP, ?_, ?_⟩
  · apply kpair_mem_iff_value.mpr
    refine ⟨?_, hv⟩
    rw [domain_eq_of_mem_function hmap, hκ.fixed_below hα]
    exact hi
  · exact ((mem_derivedUltrafilter_iff _ _ _).mp (function_value_mem hg hi)).2

theorem limitRankEmbedding_criticalPoint_measurable {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B] (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) (hω : (ω : V) ∈ κ) : IsMeasurableOrdinal κ :=
  ⟨limitRankEmbedding_criticalPoint_initial hδ h hκ, hω, derivedUltrafilter κ f,
    derivedUltrafilter_nonprincipal hδ h hκ, derivedUltrafilter_complete hδ h hκ⟩

end ZFVP
