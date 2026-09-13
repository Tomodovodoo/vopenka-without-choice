import ZFVP.ModelTheory.WoodinCollapseDisplacementName
import ZFVP.ModelTheory.WoodinTailNameActionTransfer
import ZFVP.ModelTheory.ForcingEntailment

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def collapseDisplacementInputFormula : SetTheorySemisentence 8 :=
  f“Q S κ δ p q f g. !regularCardinalFormula κ ∧ !IsOrdinal.dfn δ ∧
    !totalWoodinCollapseFormula Q κ δ ∧ !piOneReverseInclusionOrderFormula S Q ∧
    p ∈ Q ∧ q ∈ Q ∧ !woodinCollapseDisplacementFormula f κ δ p q ∧ !sparseConverseGraphFormula g f”

def collapseDisplacementOutputFormula : SetTheorySemisentence 8 :=
  f“Q S κ δ p q f g. !tailInversePairFormula Q S f g ∧ !tailInversePairFormula Q S g f ∧
    !IsFunction.dfn f ∧ !IsFunction.dfn g ∧
    !value.dfn f (!isEmpty) = !isEmpty ∧ !value.dfn g (!isEmpty) = !isEmpty ∧
    ∃ r ∈ Q, !kpair.dfn r (!value.dfn f p) ∈ S ∧ !kpair.dfn r q ∈ S”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_collapseDisplacementInputFormula (v : Fin 8 → V) :
    collapseDisplacementInputFormula.Evalb v ↔
    IsRegularCardinal (v 2) ∧ IsOrdinal (v 3) ∧
      v 0 = totalWoodinCollapse (v 2) (v 3) ∧ v 1 = reverseInclusionOrder (v 0) ∧
      v 4 ∈ v 0 ∧ v 5 ∈ v 0 ∧
      v 6 = totalWoodinCollapseDisplacement (v 2) (v 3) (v 4) (v 5) ∧ v 7 = converseGraph (v 6) := by
  simp [collapseDisplacementInputFormula]

theorem eval_collapseDisplacementOutputFormula (v : Fin 8 → V) :
    collapseDisplacementOutputFormula.Evalb v ↔
    (IsForcingAutomorphism (v 0) (v 1) (v 6) ∧ IsForcingAutomorphism (v 0) (v 1) (v 7) ∧
      ∀ x ∈ v 0, (v 7) ‘ ((v 6) ‘ x) = x) ∧
    (IsForcingAutomorphism (v 0) (v 1) (v 7) ∧ IsForcingAutomorphism (v 0) (v 1) (v 6) ∧
      ∀ x ∈ v 0, (v 6) ‘ ((v 7) ‘ x) = x) ∧
    IsFunction (v 6) ∧ IsFunction (v 7) ∧ (v 6) ‘ ∅ = ∅ ∧ (v 7) ‘ ∅ = ∅ ∧
      ForcingCompatible (v 0) (v 1) ((v 6) ‘ (v 4)) (v 5) := by
  simp [collapseDisplacementOutputFormula, ForcingCompatible]

theorem collapseDisplacement_input_output (v : Fin 8 → V)
    (h : collapseDisplacementInputFormula.Evalb v) : collapseDisplacementOutputFormula.Evalb v := by
  obtain ⟨hk, hd, hQ, hS, hp, hq, hf, hg⟩ := (eval_collapseDisplacementInputFormula v).mp h
  let := hd
  rw [totalWoodinCollapse_eq] at hQ
  rw [totalWoodinCollapseDisplacement_eq] at hf
  have hp' := hQ ▸ hp
  have hq' := hQ ▸ hq
  have ha : IsForcingAutomorphism (v 0) (v 1) (v 6) := by
    rw [hS, hQ, hf]
    exact woodinCollapseDisplacement_automorphism hk hp' hq'
  have hb : IsForcingAutomorphism (v 0) (v 1) (v 7) := hg ▸ forcingAutomorphism_inverse ha
  have hi : IsForcingIsomorphism (v 0) (v 1) (v 0) (v 1) (v 6) := ha
  have he : (v 6) ‘ ∅ = ∅ := by rw [hf]; exact woodinCollapseDisplacement_empty hp'
  have hz : (∅ : V) ∈ v 0 := by
    rw [hQ]
    exact woodinCollapse_subset hp' (empty_subset _)
  have hge : (v 7) ‘ ∅ = ∅ := by
    rw [hg]
    simpa only [he] using hi.inverse_value hz
  apply (eval_collapseDisplacementOutputFormula v).mpr
  refine ⟨⟨ha, hb, ?_⟩, ⟨hb, ha, ?_⟩, IsFunction.of_mem ha.1, IsFunction.of_mem hb.1, he, hge, ?_⟩
  · intro x hx
    rw [hg]
    exact hi.inverse_value hx
  · intro x hx
    rw [hg]
    exact hi.value_inverse hx
  · rw [hS, hQ, hf]
    exact woodinCollapseDisplacement_common_extension hk hp' hq'

theorem collapseDisplacement_forces_output {P R top r : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hr : r ∈ P)
    (v : Fin 8 → ForcingName P)
    (hi : r ∈ forcingFormula P R collapseDisplacementInputFormula (standardTuple (fun i ↦ (v i).val))) :
    r ∈ forcingFormula P R collapseDisplacementOutputFormula (standardTuple (fun i ↦ (v i).val)) :=
  forcingFormula_entailment collapseDisplacementInputFormula collapseDisplacementOutputFormula
    (fun _ _ _ _ ↦ collapseDisplacement_input_output) hR ht hr v hi

end ZFVP

