import ZFVP.SetTheory.CodingUniverse
import ZFVP.SetTheory.UniformParameterizedRecursion
import ZFVP.SetTheory.UniformRank

/-! Uniform definitions of ordinal addition and the coding bounds. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def ordinalAddStepFormula : SetTheorySemisentence 3 :=
  f“y a f. ∀ x, x ∈ y ↔ x ∈ a ∨ ∃ z ∈ !range.dfn f, x = z ∨ x ∈ z”

def ordinalAddFormula : SetTheorySemisentence 3 := parameterRecursionFormula ordinalAddStepFormula

def codingRankFormula : SetTheorySemisentence 2 :=
  f“κ X. κ = !ordinalAddFormula (!rankFormula (!union.dfn X (!singleton.dfn (!isω)))) (!isω)”

def codingUniverseFormula : SetTheorySemisentence 2 :=
  f“C X. C = !hierarchyFormula (!codingRankFormula X)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance ordinalAddStepFormula_defined : ℒₛₑₜ-function₂[V] ordinalAddStep via ordinalAddStepFormula :=
  ⟨fun v ↦ by
    change ordinalAddStepFormula.Evalb v ↔ v 0 = ordinalAddStep (v 1) (v 2)
    rw [mem_ext_iff]
    simp [ordinalAddStepFormula, ordinalAddStep, mem_sUnion_iff, repl_spec, mem_succ_iff]⟩

instance ordinalAddFormula_defined : ℒₛₑₜ-function₂[V] ordinalAdd via ordinalAddFormula :=
  parameterRecursionFormula_defined ordinalAddStep ordinalAddStepFormula

instance ordinalAdd_definable : ℒₛₑₜ-function₂[V] ordinalAdd := ordinalAddFormula_defined.to_definable

instance codingRankFormula_defined : ℒₛₑₜ-function₁[V] codingRank via codingRankFormula :=
  ⟨fun v ↦ by simp [codingRankFormula, codingRank]⟩
instance codingRank_definable : ℒₛₑₜ-function₁[V] codingRank := codingRankFormula_defined.to_definable

instance codingUniverseFormula_defined : ℒₛₑₜ-function₁[V] codingUniverse via codingUniverseFormula :=
  ⟨fun v ↦ by simp [codingUniverseFormula, codingUniverse]⟩
instance codingUniverse_definable : ℒₛₑₜ-function₁[V] codingUniverse := codingUniverseFormula_defined.to_definable

end ZFVP
