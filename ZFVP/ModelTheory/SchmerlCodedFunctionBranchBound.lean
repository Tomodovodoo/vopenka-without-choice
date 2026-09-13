import ZFVP.ModelTheory.SchmerlCodedSourceBridge
import ZFVP.ModelTheory.SchmerlCodedFunctionBranchFilter
import ZFVP.ModelTheory.SchmerlCodedDefinitionCardinality
import ZFVP.ModelTheory.SchmerlInternalWeakSpecialization

/-! The actual coded Rubin source supplies the full branch bound and hence
the internal weak-specializing forcing extension. Source existence is separate. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) (s : W)

attribute [local irreducible] codedFunctionBranchFilter

theorem selectedFunctionBranches_cardLE_definableSubsets {κ c : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val) (codedFiniteDomainOrder R.code (R.equiv s).val) c)
    (hRubin : IsCodedRubin R.code κ) :
    internalCofinalBranches (codedSelectedFunctionNodes R.code (R.equiv s).val κ c) (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) κ
      (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ≤# codedDefinableSubsets R.code := by
  apply cardLE_of_injective_map (codedFunctionBranchFilter R.code (R.equiv s).val) (by definability)
  · intro B hB
    exact (mem_codedDefinableSubsets _ _).mpr
      (R.codedFunctionBranchFilter_isCodedDefinable s hc ((mem_internalCofinalBranches _ _ _ _ _).mp hB) hRubin)
  · intro B hB C hC he
    have hB' := (mem_internalCofinalBranches _ _ _ _ _).mp hB
    have hC' := (mem_internalCofinalBranches _ _ _ _ _).mp hC
    calc
      B = codedFunctionBranchFilter R.code (R.equiv s).val B ∩ codedSelectedFunctionNodes R.code (R.equiv s).val κ c := (R.codedFunctionBranchFilter_recovers s hB').symm
      _ = codedFunctionBranchFilter R.code (R.equiv s).val C ∩ codedSelectedFunctionNodes R.code (R.equiv s).val κ c := congrArg (fun F ↦ F ∩ _) he
      _ = C := R.codedFunctionBranchFilter_recovers s hC'

theorem selectedFunctionBranches_cardLE (hAC : InternalChoice V) {c : V}
    (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V)) (codedFiniteDomains R.code (R.equiv s).val) (codedFiniteDomainOrder R.code (R.equiv s).val) c)
    (hRubin : IsCodedRubin R.code (hartogsNumber (ω : V)))
    (hcard : structureDomain R.code ≤# hartogsNumber (ω : V)) :
    internalCofinalBranches (codedSelectedFunctionNodes R.code (R.equiv s).val (hartogsNumber (ω : V)) c)
      (codedSelectedFunctionOrder R.code (R.equiv s).val (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
      (codedSelectedFunctionRank R.code (R.equiv s).val (hartogsNumber (ω : V)) c) ≤# hartogsNumber (ω : V) := by
  apply (R.selectedFunctionBranches_cardLE_definableSubsets s hc hRubin).trans
  exact codedDefinableSubsets_cardLE hAC (hartogsNumber_initial (ω : V))
    (IsOrdinal.toIsTransitive.transitive _ omega_mem_hartogs_omega) hcard

end ZFVP.BinaryRelationRepresentation


