import ZFVP.ModelTheory.UsubaCanonicalBoundInduction
import ZFVP.ModelTheory.ProjectionClosedPreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

def UsubaStageDCBelow (i : V) : Prop :=
  ∀ p ∈ (T).P i, p ∈ forcingFormula ((T).P i) ((T).R i) dependentChoiceBelowFormula
    (standardTuple ![checkName ((T).top i) i])

attribute [local instance] DefinableForcingTower.P_definable DefinableForcingTower.R_definable
  DefinableForcingTower.top_definable

instance usubaStageDCBelow_definable : ℒₛₑₜ-predicate[V] (UsubaStageDCBelow (V := V)) := by
  unfold UsubaStageDCBelow
  apply Language.Definable.all
  apply Language.Definable.imp
  · definability
  · apply Language.DefinableRel₄.comp
      (P := fun p P R v ↦ p ∈ forcingFormula P R dependentChoiceBelowFormula v)
    · definability
    · definability
    · definability
    · simp only [standardTuple]
      definability

theorem usubaStageDCBelow_semantics {i : V} [IsOrdinal i] (h : UsubaStageDCBelow i)
    {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G) :
    ∀ β ∈ (usubaStageContext i hG).check i, InternalDependentChoiceAt β := by
  let A := usubaStageContext i hG
  obtain ⟨p, hp⟩ := hG.1.2.1
  exact (Defined.eval_iff _).mp ((A.checked_unary_truth dependentChoiceBelowFormula i).mpr
    ⟨p, hp, h p (hG.1.1 p hp)⟩)

theorem usubaStageDCBelow_of_generics [Countable V] {i : V} [IsOrdinal i]
    (h : ∀ (G : Set V) (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G),
      ∀ β ∈ (usubaStageContext i hG).check i, InternalDependentChoiceAt β) :
    UsubaStageDCBelow i := by
  apply (all_forces_iff_all_generics ((T).order i inferInstance) ((T).top_spec i inferInstance)
    dependentChoiceBelowFormula
    ![⟨checkName ((T).top i) i, checkName_isName ((T).top_spec i inferInstance).1 i⟩]).mpr
  intro G hG
  exact (Defined.eval_iff _).mpr (h G hG)

theorem usubaStageDCBelow_preserved [Countable V] {i j β : V}
    [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) (hβ : β ∈ i)
    (h : UsubaStageDCBelow i) {H : Set V}
    (hH : IsExternalForcingGeneric ((T).P j) ((T).R j) H) :
    InternalDependentChoiceAt ((usubaStageContext j hH).check β) := by
  let := IsOrdinal.of_mem hβ
  let G := forcingProjectionGeneric ((T).P i) ((T).R i) ((T).projection i j) H
  have hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G :=
    ((T).splitProjection hij).projection.generic ((T).order i inferInstance) hH
  let A := usubaStageContext i hG
  let B := usubaStageContext j hH
  have hDC : InternalDependentChoiceAt (A.check β) :=
    usubaStageDCBelow_semantics h hG (A.check β) ((A.check_mem_iff _ _).mpr hβ)
  have hc := usubaQuotient_closedThrough hij hG hDC
  have hh := A.projectionInclusion_dependentChoiceAt_of_separative_closed B
    ((T).splitProjection hij) rfl hDC hc
  simpa only [A.projectionInclusion_check B ((T).splitProjection hij) rfl] using hh

theorem usubaStageDCBelow_induction [Countable V]
    (hstep : ∀ (k : V) [IsOrdinal k], UsubaStageDCBelow k →
      ∀ (H : Set V) (hH : IsExternalForcingGeneric ((T).P (succ k)) ((T).R (succ k)) H),
        InternalDependentChoiceAt ((usubaStageContext (succ k) hH).check k))
    (i : V) [IsOrdinal i] : UsubaStageDCBelow i := by
  have hall := transfinite_induction (UsubaStageDCBelow (V := V)) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal i)
  intro j ih
  by_cases hs : (j : V) = succ (⋃ˢ (j : V))
  · have hk : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hs).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hk
    have hp := ih (IsOrdinal.toOrdinal (⋃ˢ (j : V))) hk
    rw [hs]
    apply usubaStageDCBelow_of_generics
    intro H hH β hβ
    let B := usubaStageContext (succ (⋃ˢ (j : V))) hH
    have hDC := hstep (⋃ˢ (j : V)) hp H hH
    rw [B.check_succ] at hβ
    let := IsOrdinal.of_mem hβ
    exact hDC.downward (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hβ))
  · apply usubaStageDCBelow_of_generics
    intro H hH β hβ
    let B := usubaStageContext (j : V) hH
    obtain ⟨b, hb, rfl⟩ := (B.mem_check_iff _ _).mp hβ
    let := IsOrdinal.of_mem hb
    have hsb : succ b ⊆ (j : V) := by
      intro x hx
      rcases mem_succ_iff.mp hx with rfl | hx
      · exact hb
      · exact IsOrdinal.toIsTransitive.mem_trans hx hb
    have hbs : succ b ∈ (j : V) := by
      rcases IsOrdinal.subset_iff.mp hsb with he | hm
      · have hj : (j : V) = succ b := he.symm
        apply False.elim
        apply hs
        rw [hj, sUnion_succ_of_transitive]
      · exact hm
    exact usubaStageDCBelow_preserved hsb (mem_succ_self b)
      (ih (IsOrdinal.toOrdinal (succ b)) hbs) hH

end ZFVP
