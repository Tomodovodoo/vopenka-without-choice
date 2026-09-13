import ZFVP.ModelTheory.SuccessorRankSetOperations
import ZFVP.SetTheory.SigmaOneStarCorrectness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneFunctionClosedFormula : SetTheorySemisentence 2 :=
  “D b. ∀ f, !boundedFunctionFormula f D b → f ∈ b”

theorem piOneFunctionClosedFormula_piOne : IsPiFormula 1 piOneFunctionClosedFormula :=
  .all (.bounded (.or (boundedFunctionFormula_bounded.subst _).neg (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance piOneFunctionClosedFormula_defined :
    ℒₛₑₜ-relation[V] (fun D b ↦ b ^ D ⊆ b) via piOneFunctionClosedFormula :=
  ⟨fun v ↦ by simp [piOneFunctionClosedFormula, subset_def]⟩

theorem successorRankEmbedding_functionClosed {δ ε e D b : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hD : D ∈ hierarchy δ) (hb : b ∈ hierarchy δ) :
    b ^ D ⊆ b ↔ (e ‘ b) ^ (e ‘ D) ⊆ e ‘ b := by
  have he := successorRankEmbedding_pi_iff hδ hε h piOneFunctionClosedFormula_piOne ![D, b]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hD, hb])
  exact (piOneFunctionClosedFormula_defined.iff ![D, b]).symm.trans
    (he.trans (piOneFunctionClosedFormula_defined.iff (fun i ↦ e ‘ (![D, b] i))))

theorem successorRankEmbedding_rankFunctionClosed {δ ε e α b : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hα : IsOrdinal α) (hαV : α ∈ hierarchy δ) (hb : b ∈ hierarchy δ) :
    IsRankFunctionClosed α b ↔ IsRankFunctionClosed (e ‘ α) (e ‘ b) := by
  have he := successorRankEmbedding_functionClosed hδ hε h (hδ.hierarchy_closed hα hαV) hb
  rw [(successorRankEmbedding_value_lower_hierarchy hδ hε h hα hαV).2] at he
  exact he

end ZFVP
