import ZFVP.Syntax.EndExtensionTermEvaluation
import ZFVP.Syntax.EndExtensionFormulaCodes
import ZFVP.Syntax.AtomicSatisfaction

/-! Atomic satisfaction in arbitrary coded languages is absolute under ZF end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_evaluatedArguments (j : MembershipEndExtension V W) {L n : V}
    (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ M e b args : V) :
    j (evaluatedArguments L Γ M e n b args) =
      evaluatedArguments (j L) (j Γ) (j M) (j e) (j n) (j b) (j args) := by
  unfold evaluatedArguments evaluateWithFreeAssignment
  rw [j.map_compose, j.map_termEvaluation hL hn Γ M b e]

theorem atomicHolds_iff (j : MembershipEndExtension V W) {L n : V}
    (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (Γ M e b r args : V) :
    AtomicHolds (j L) (j Γ) (j M) (j e) (j n) (j b) (j r) (j args) ↔
      AtomicHolds L Γ M e n b r args := by
  have hzero : j (0 : V) = (0 : W) := j.map_numeral 0
  have hone : j (1 : V) = (1 : W) := j.map_numeral 1
  unfold AtomicHolds
  rw [← j.map_relationSymbols, j.exists_mem_iff]
  simp only [← j.map_equalityToken, ← j.map_relationToken, ← j.map_evaluatedArguments hL hn,
    ← hzero, ← hone, ← j.map_structureRelations, ← j.map_value_total, j.injective.eq_iff, j.mem_iff]

end MembershipEndExtension
end ZFVP
