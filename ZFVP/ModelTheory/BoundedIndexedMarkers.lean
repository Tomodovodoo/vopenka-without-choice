import ZFVP.ModelTheory.IndexedMarkerMembership
import ZFVP.ModelTheory.BoundedMarkerFunctions

/-! Bounded checks for the marker symbol set and its constant interpretations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedMarkerIndexSetFormula : SetTheorySemisentence 3 :=
  “I B n. (∀ i ∈ I, i ∈ B ∨ ∃ j ∈ n, !boundedKpairFormula i B j) ∧
    (∀ i ∈ B, i ∈ I) ∧ ∀ j ∈ n, !boundedPairMemberFormula I B j”

def boundedIndexedMarkerValueFormula : SetTheorySemisentence 5 :=
  “y B n c i. (i ∈ B ∧ y = i) ∨
    (i ∉ B ∧ ∃ j ∈ n, !boundedKpairFormula i B j ∧ !boundedPairMemberFormula c j y)”

def boundedIndexedMarkerFunctionFormula : SetTheorySemisentence 7 :=
  “g X B n c i A. ∃ y ∈ A, !boundedIndexedMarkerValueFormula y B n c i ∧
    !boundedConstantGraphFormula g X y”

def boundedIndexedMarkerFunctionsFormula : SetTheorySemisentence 8 :=
  “U F I X B n c A. (∀ p ∈ F, ∃ i ∈ I, ∃ g ∈ U,
    !boundedKpairFormula p i g ∧ !boundedIndexedMarkerFunctionFormula g X B n c i A) ∧
    ∀ i ∈ I, ∃ g ∈ U, !boundedPairMemberFormula F i g ∧ !boundedIndexedMarkerFunctionFormula g X B n c i A”

theorem boundedMarkerIndexSetFormula_bounded : IsBoundedSetFormula boundedMarkerIndexSetFormula := by
  repeat' first
    | exact boundedKpairFormula_bounded.subst _
    | exact boundedPairMemberFormula_bounded.subst _
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | exact .rel _ _

theorem boundedIndexedMarkerValueFormula_bounded : IsBoundedSetFormula boundedIndexedMarkerValueFormula := by
  repeat' first
    | exact boundedKpairFormula_bounded.subst _
    | exact boundedPairMemberFormula_bounded.subst _
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or
    | apply IsBoundedSetFormula.exs
    | exact .rel _ _
    | exact .nrel _ _

theorem boundedIndexedMarkerFunctionFormula_bounded : IsBoundedSetFormula boundedIndexedMarkerFunctionFormula :=
  .exs (.bvar 6) (.and (boundedIndexedMarkerValueFormula_bounded.subst _)
    (boundedConstantGraphFormula_bounded.subst _))

theorem boundedIndexedMarkerFunctionsFormula_bounded : IsBoundedSetFormula boundedIndexedMarkerFunctionsFormula :=
  .and (.all (.bvar 1) (.exs (.bvar 3) (.exs (.bvar 2)
    (.and (boundedKpairFormula_bounded.subst _) (boundedIndexedMarkerFunctionFormula_bounded.subst _)))))
    (.all (.bvar 2) (.exs (.bvar 1)
      (.and (boundedPairMemberFormula_bounded.subst _) (boundedIndexedMarkerFunctionFormula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedMarkerIndexSetFormula (I B n : V) :
    boundedMarkerIndexSetFormula.Evalb ![I, B, n] ↔ I = markerIndexSet B n := by
  simp [boundedMarkerIndexSetFormula]
  constructor
  · rintro ⟨hl, hb, hn⟩
    apply mem_ext
    intro i
    constructor
    · intro hi
      rcases hl i hi with hiB | ⟨j, hj, rfl⟩
      · exact markerIndexSet_base hiB
      · exact markerIndexSet_marker hj
    · intro hi
      rcases mem_union_iff.mp hi with hiB | hp
      · exact hb i hiB
      · obtain ⟨b, hb, j, hj, rfl⟩ := mem_prod_iff.mp hp
        have he : b = B := by simpa using hb
        subst b
        exact hn j hj
  · rintro rfl
    refine ⟨?_, fun _ ↦ markerIndexSet_base, fun _ ↦ markerIndexSet_marker⟩
    intro i hi
    rcases mem_union_iff.mp hi with hiB | hp
    · exact Or.inl hiB
    · obtain ⟨b, hb, j, hj, rfl⟩ := mem_prod_iff.mp hp
      have he : b = B := by simpa using hb
      subst b
      exact Or.inr ⟨j, hj, rfl⟩

theorem eval_boundedIndexedMarkerValueFormula {B n c A i : V}
    (hc : c ∈ A ^ n) (hi : i ∈ markerIndexSet B n) (y : V) :
    boundedIndexedMarkerValueFormula.Evalb ![y, B, n, c, i] ↔ y = indexedMarkerValue B c i := by
  let := IsFunction.of_mem hc
  simp [boundedIndexedMarkerValueFormula]
  by_cases hiB : i ∈ B
  · simp [indexedMarkerValue, hiB]
  · have hp : i ∈ ({B} : V) ×ˢ n := (mem_union_iff.mp hi).resolve_left hiB
    obtain ⟨b, hb, j, hj, rfl⟩ := mem_prod_iff.mp hp
    have he : b = B := by simpa using hb
    subst b
    simp only [indexedMarkerValue, hiB, ↓reduceIte, kpair.π₂_kpair]
    simp [kpair_mem_iff_value, domain_eq_of_mem_function hc, hj, eq_comm]

theorem eval_boundedIndexedMarkerFunctionFormula {B n c A i : V}
    (hBA : B ⊆ A) (hc : c ∈ A ^ n) (hi : i ∈ markerIndexSet B n) (g X : V) :
    boundedIndexedMarkerFunctionFormula.Evalb ![g, X, B, n, c, i, A] ↔
      g = constantGraph X (indexedMarkerValue B c i) := by
  have hv : indexedMarkerValue B c i ∈ A := by
    have hm := function_value_mem (indexedMarkerNames_mem_function hBA hc) hi
    simpa only [indexedMarkerNames, value_definableGraph _ _ _ hi] using hm
  simp [boundedIndexedMarkerFunctionFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, eval_boundedIndexedMarkerValueFormula hc hi, hv]

theorem namedMembershipFunctions_indexed (B n A c : V) :
    namedMembershipFunctions (markerIndexSet B n) A (indexedMarkerNames B n c) =
      definableGraph (markerIndexSet B n)
        (fun i ↦ constantGraph (A ^ (0 : V)) (indexedMarkerValue B c i)) (by definability) := by
  apply mem_ext
  intro p
  simp only [namedMembershipFunctions, mem_definableGraph_iff]
  apply exists_congr
  intro i
  apply and_congr_right
  intro hi
  rw [indexedMarkerNames, value_definableGraph _ _ _ hi]

theorem eval_boundedIndexedMarkerFunctionsFormula {B n A c : V}
    (hBA : B ⊆ A) (hc : c ∈ A ^ n) (U F : V) :
    boundedIndexedMarkerFunctionsFormula.Evalb ![U, F, markerIndexSet B n, A ^ (0 : V), B, n, c, A] ↔
      F = namedMembershipFunctions (markerIndexSet B n) A (indexedMarkerNames B n c) ∧
        ∀ i ∈ markerIndexSet B n, constantGraph (A ^ (0 : V)) (indexedMarkerValue B c i) ∈ U := by
  simp only [boundedIndexedMarkerFunctionsFormula]
  simp (config := { contextual := true }) [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
    eval_boundedIndexedMarkerFunctionFormula hBA hc]
  rw [namedMembershipFunctions_indexed, mem_ext_iff]
  simp only [mem_definableGraph_iff]
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨?_, fun i hi ↦ (hr i hi).1⟩
    intro p
    constructor
    · intro hp
      obtain ⟨i, hi, g, _, he, hg⟩ := hl p hp
      have hg' := (eval_boundedIndexedMarkerFunctionFormula hBA hc hi g _).mp hg
      exact ⟨i, hi, by simpa only [hg'] using he⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hr i hi).2
  · rintro ⟨he, hg⟩
    refine ⟨?_, fun i hi ↦ ⟨hg i hi, (he _).mpr ⟨i, hi, rfl⟩⟩⟩
    intro p hp
    obtain ⟨i, hi, he⟩ := (he p).mp hp
    exact ⟨i, hi, _, hg i hi, he,
      (eval_boundedIndexedMarkerFunctionFormula hBA hc hi _ _).mpr rfl⟩

theorem indexedMarkerFunctions_values_mem_of_mem {U B n A c : V} [IsTransitive U]
    (hF : namedMembershipFunctions (markerIndexSet B n) A (indexedMarkerNames B n c) ∈ U) :
    ∀ i ∈ markerIndexSet B n, constantGraph (A ^ (0 : V)) (indexedMarkerValue B c i) ∈ U := by
  intro i hi
  rw [namedMembershipFunctions_indexed] at hF
  have hp := (inferInstance : IsTransitive U).mem_trans ((mem_definableGraph_iff _ _ _ _).mpr ⟨i, hi, rfl⟩) hF
  exact (kpair_components_mem_transitive hp).2

end ZFVP
