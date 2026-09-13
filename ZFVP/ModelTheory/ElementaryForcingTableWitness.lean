import ZFVP.ModelTheory.ElementaryFiniteFunctionClosure
import ZFVP.Syntax.BoundedForcingQuantifiers

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingHullWitnessFormula : SetTheorySemisentence 9 :=
  “x U O D T n b p φ. x ∈ D ∧ !boundedForcingPrependLookup U O T n b x p φ”

theorem forcingHullWitnessFormula_bounded : IsBoundedSetFormula forcingHullWitnessFormula :=
  .and (.rel _ _) (boundedForcingPrependLookup_bounded.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsElementaryInclusion.forcing_table_witness {X B U P R D n φ b p : V}
    [IsTransitive B] [IsSequenceSupport U] (h : IsElementaryInclusion X B)
    (hU : U ∈ X) (hω : (ω : V) ∈ X) (hD : D ∈ X)
    (hT : internalForcingTruthTable P R D ∈ X)
    (hnX : n ∈ X) (hbX : b ∈ X) (hpX : p ∈ X) (hφX : φ ∈ X)
    (hDU : D ⊆ U) (hpU : p ∈ U) (hφU : φ ∈ U)
    (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ n) φ)
    (hb : b ∈ D ^ n) (hp : p ∈ P)
    (hex : ∃ x ∈ D, InternalForces P R D (succ n) φ (assignmentPrepend n b x) p) :
    ∃ x ∈ X ∩ D, InternalForces P R D (succ n) φ (assignmentPrepend n b x) p := by
  let T := internalForcingTruthTable P R D
  have heval (x : V) : forcingHullWitnessFormula.Evalb ![x, U, ω, D, T, n, b, p, φ] ↔
      x ∈ D ∧ InternalForces P R D (succ n) φ (assignmentPrepend n b x) p := by
    simp only [forcingHullWitnessFormula]
    change (x ∈ D ∧ boundedForcingPrependLookup.Evalb ![U, ω, T, n, b, x, p, φ]) ↔ _
    apply and_congr_right
    intro hx
    exact (eval_boundedForcingPrependLookup hDU hn hb hx hpU hφU T).trans
      (internalForcingTruthTable_lookup hφ (assignmentPrepend_mem_function hn hb hx) hp)
  obtain ⟨x, hx, hf⟩ := hex
  obtain ⟨y, hy, hf⟩ := h.bounded_witness forcingHullWitnessFormula_bounded
    ![U, ω, D, T, n, b, p, φ]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hU, hω, hD, hT, hnX, hbX, hpX, hφX, T])
    ⟨x, (inferInstance : IsTransitive B).mem_trans hx (h.subset D hD), (heval x).mpr ⟨hx, hf⟩⟩
  exact ⟨y, mem_inter_iff.mpr ⟨hy, ((heval y).mp hf).1⟩, ((heval y).mp hf).2⟩

end ZFVP
