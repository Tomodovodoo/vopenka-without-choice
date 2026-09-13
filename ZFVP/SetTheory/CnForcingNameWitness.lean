import ZFVP.Syntax.SigmaOneNameWitness
import ZFVP.SetTheory.CnSigmaClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.forcingNameWitness_family {δ P R n φ b p : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hb : b ∈ hierarchy δ)
    (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode (succ n) φ) (hp : p ∈ P)
    (hex : sigmaOneNameWitnessFormula.Evalb ![P, R, n, φ, b, p]) :
    ∃ D ∈ hierarchy δ, IsForcingNameFamily P D ∧ IsNonempty D ∧ b ∈ D ^ n ∧
      ∃ τ ∈ D, InternalForces P R D (succ n) φ (assignmentPrepend n b τ) p := by
  let := hδ.ordinal
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff 0 δ).mp hδ).2.support
  have hnu : n ∈ hierarchy δ := IsCodingSupport.natural_mem hn
  have hφu : φ ∈ hierarchy δ := membershipFormulaCode_formula_mem_support hφ
  have hpu := (hierarchy_transitive δ).mem_trans hp hP
  obtain ⟨D, hD, hmat⟩ := hδ.sigmaOne_witness sigmaOneNameWitnessMatrix_sigmaOne ![P, R, n, φ, b, p]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hP, hR, hnu, hφu, hb, hpu]) hex
  exact ⟨D, hD, (eval_sigmaOneNameWitnessMatrix hn hφ hp).mp hmat⟩

end ZFVP
