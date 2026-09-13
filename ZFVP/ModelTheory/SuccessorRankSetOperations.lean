import ZFVP.ModelTheory.SuccessorRankEmbedding
import ZFVP.SetTheory.LeastWitnessBodies
import ZFVP.SetTheory.FinitePartialFunctions

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneProductFormula : SetTheorySemisentence 3 :=
  “P X Y. ∀ z, z ∈ P ↔ ∃ x ∈ X, ∃ y ∈ Y, !boundedKpairFormula z x y”

theorem piOneProductFormula_piOne : IsPiFormula 1 piOneProductFormula :=
  .all (.bounded ((IsBoundedSetFormula.rel _ _).iff
    (.exs (.bvar 2) (.exs (.bvar 4) (boundedKpairFormula_bounded.subst _)))))

def piOneReverseInclusionOrderFormula : SetTheorySemisentence 2 :=
  “R P. ∀ z, z ∈ R ↔ ∃ p ∈ P, ∃ q ∈ P,
    !boundedKpairFormula z p q ∧ !isSubsetOf q p”

theorem piOneReverseInclusionOrderFormula_piOne : IsPiFormula 1 piOneReverseInclusionOrderFormula :=
  .all (.bounded ((IsBoundedSetFormula.rel _ _).iff
    (.exs (.bvar 2) (.exs (.bvar 3) (.and (boundedKpairFormula_bounded.subst _)
      (isSubsetOf_bounded.subst _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_piOneProductFormula (P X Y : V) :
    piOneProductFormula.Evalb ![P, X, Y] ↔ P = X ×ˢ Y := by
  simp [piOneProductFormula, mem_ext_iff, mem_prod_iff]

@[simp] theorem eval_piOneReverseInclusionOrderFormula (R P : V) :
    piOneReverseInclusionOrderFormula.Evalb ![R, P] ↔ R = reverseInclusionOrder P := by
  have hev : piOneReverseInclusionOrderFormula.Evalb ![R, P] ↔
      ∀ z : V, z ∈ R ↔ ∃ p ∈ P, ∃ q ∈ P, z = ⟨p, q⟩ₖ ∧ q ⊆ p := by
    simp [piOneReverseInclusionOrderFormula]
  rw [hev, mem_ext_iff]
  apply forall_congr'
  intro z
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨p, hp, q, hq, rfl, hs⟩
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hp, hq, hs⟩
  · intro hz
    obtain ⟨p, hp, q, hq, he⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    subst z
    exact ⟨p, hp, q, hq, rfl, ((pair_mem_reverseInclusionOrder _ _ _).mp hz).2.2⟩

theorem reverseInclusionOrder_mem_hierarchy {δ P : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) : reverseInclusionOrder P ∈ hierarchy δ := by
  let := hδ.ordinal
  apply subset_mem_hierarchy_limit hδ.successor_closed
    (prod_mem_hierarchy_limit hδ.successor_closed hP hP)
  intro z hz
  exact (mem_sep_iff.mp hz).1

theorem successorRankEmbedding_value_product {δ ε e X Y : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hX : X ∈ hierarchy δ) (hY : Y ∈ hierarchy δ) :
    e ‘ (X ×ˢ Y) = (e ‘ X) ×ˢ (e ‘ Y) := by
  let := hδ.ordinal
  have hp := prod_mem_hierarchy_limit hδ.successor_closed hX hY
  have he := successorRankEmbedding_pi_iff hδ hε h piOneProductFormula_piOne
    ![X ×ˢ Y, X, Y] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hp, hX, hY])
  apply (eval_piOneProductFormula _ _ _).mp
  convert he.mp ((eval_piOneProductFormula _ _ _).mpr rfl) using 1
  apply congrArg Semiformula.Evalb
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i

theorem successorRankEmbedding_value_power {δ ε e X : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hX : X ∈ hierarchy δ) : e ‘ (℘ X) = ℘ (e ‘ X) := by
  let := hδ.ordinal
  have hp := power_mem_hierarchy_limit hδ.successor_closed hX
  have he := successorRankEmbedding_pi_iff hδ hε h piOnePowerFormula_piOne
    ![℘ X, X] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hp, hX])
  apply (eval_piOnePowerFormula _ _).mp
  convert he.mp ((eval_piOnePowerFormula _ _).mpr rfl) using 1
  apply congrArg Semiformula.Evalb
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i

theorem successorRankEmbedding_value_lower_hierarchy {δ ε e α : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hα : IsOrdinal α) (hαV : α ∈ hierarchy δ) :
    IsOrdinal (e ‘ α) ∧ e ‘ (hierarchy α) = hierarchy (e ‘ α) := by
  have hp := hδ.hierarchy_closed hα hαV
  have he := successorRankEmbedding_pi_iff hδ hε h piOneHierarchyFormula_piOne
    ![hierarchy α, α] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hp, hαV])
  have ht := he.mp ((eval_piOneHierarchyFormula _ _).mpr ⟨hα, rfl⟩)
  simpa [IsHierarchySegment] using ht

theorem successorRankEmbedding_value_reverseInclusionOrder {δ ε e P : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hP : P ∈ hierarchy δ) :
    e ‘ (reverseInclusionOrder P) = reverseInclusionOrder (e ‘ P) := by
  have hp := reverseInclusionOrder_mem_hierarchy hδ hP
  have he := successorRankEmbedding_pi_iff hδ hε h piOneReverseInclusionOrderFormula_piOne
    ![reverseInclusionOrder P, P] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hp, hP])
  apply (eval_piOneReverseInclusionOrderFormula _ _).mp
  convert he.mp ((eval_piOneReverseInclusionOrderFormula _ _).mpr rfl) using 1
  apply congrArg Semiformula.Evalb
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i

end ZFVP


