import ZFVP.ModelTheory.ForcingCodeUniform
import ZFVP.ModelTheory.ForcingLimitCode
import ZFVP.SetTheory.ForcingIterationHistory

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def forcingIterationCodeNextFormula : SetTheorySemisentence 9 :=
  f“z θ s Q T ρ F M u. !forcingIterationCodeFormula z
    (!forcingFamilyNextFormula θ (!forcingCodePFormula s) Q)
    (!forcingFamilyNextFormula θ (!forcingCodeRFormula s) T)
    (!forcingMatrixNextFormula θ (!forcingCodeπFormula s) ρ (!identity.dfn Q))
    (!forcingMatrixNextFormula θ (!forcingCodeEFormula s) F (!identity.dfn Q))
    (!forcingMatrixNextFormula θ (!forcingCodeLFormula s) M (!forcingIdentityLiftFormula Q))
    (!forcingFamilyNextFormula θ (!forcingCodetFormula s) u)”

@[irreducible] def forcingCodeUniverseFormula : SetTheorySemisentence 2 :=
  f“z s. z = !sUnion.dfn (!range.dfn (!forcingCodePFormula s))”

@[irreducible] def forcingHistoryTableFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 3 :=
  f“z θ H. ∀ x, x ∈ z ↔ ∃ i ∈ θ, x ∈ !φ (!value.dfn H i)”

@[irreducible] def forcingIterationCodeUnionFormula : SetTheorySemisentence 3 :=
  f“z θ H. !forcingIterationCodeFormula z
    (!(forcingHistoryTableFormula forcingCodePFormula) θ H)
    (!(forcingHistoryTableFormula forcingCodeRFormula) θ H)
    (!(forcingHistoryTableFormula forcingCodeπFormula) θ H)
    (!(forcingHistoryTableFormula forcingCodeEFormula) θ H)
    (!(forcingHistoryTableFormula forcingCodeLFormula) θ H)
    (!(forcingHistoryTableFormula forcingCodetFormula) θ H)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingIterationCodeNextFormula_defined : Defined
    (fun v : Fin 9 → V ↦ v 0 = forcingIterationCodeNext (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8))
    forcingIterationCodeNextFormula :=
  ⟨fun v ↦ by simp [forcingIterationCodeNextFormula, forcingIterationCodeNext]⟩

instance forcingCodeUniverseFormula_defined : ℒₛₑₜ-function₁[V] forcingCodeUniverse via forcingCodeUniverseFormula :=
  ⟨fun v ↦ by simp [forcingCodeUniverseFormula, forcingCodeUniverse]⟩

instance forcingHistoryTableFormula_defined (c : V → V) (φ : SetTheorySemisentence 2)
    [hc : ℒₛₑₜ-function₁ c via φ] :
    ℒₛₑₜ-function₂ (fun θ H ↦ forcingHistoryTable θ H c hc.to_definable) via forcingHistoryTableFormula φ := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [forcingHistoryTableFormula, forcingHistoryTable, iterationTableUnion, mem_sUnion_iff, repl_spec]

instance forcingIterationCodeUnionFormula_defined :
    ℒₛₑₜ-function₂[V] forcingIterationCodeUnion via forcingIterationCodeUnionFormula :=
  ⟨fun v ↦ by simp [forcingIterationCodeUnionFormula, forcingIterationCodeUnion]⟩

end ZFVP
