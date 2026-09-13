import ZFVP.ModelTheory.NormalizedTwoStepComparison
import ZFVP.SetTheory.TwoStepForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def nameTwoStepOrderOnFormula : SetTheorySemisentence 5 :=
  f“O P R S C. ∀ z, z ∈ O ↔ z ∈ !prod.dfn C C ∧
    !kpair.dfn (!kpair.π₁.dfn (!kpair.π₁.dfn z)) (!kpair.π₁.dfn (!kpair.π₂.dfn z)) ∈ R ∧
    !(tripleForcingTruthFormula boundedPairMemberFormula)
      (!kpair.π₁.dfn (!kpair.π₁.dfn z)) P R S
      (!kpair.π₂.dfn (!kpair.π₁.dfn z)) (!kpair.π₂.dfn (!kpair.π₂.dfn z))”

instance nameTwoStepOrderOnFormula_defined : ℒₛₑₜ-function₄[V] nameTwoStepOrderOn via nameTwoStepOrderOnFormula :=
  ⟨fun v ↦ by
    change nameTwoStepOrderOnFormula.Evalb v ↔ v 0 = nameTwoStepOrderOn (v 1) (v 2) (v 3) (v 4)
    rw [mem_ext_iff]
    simp [nameTwoStepOrderOnFormula, nameTwoStepOrderOn, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Fin.forall_fin_succ]
    aesop⟩

instance nameTwoStepOrderOn_uniform_definable : ℒₛₑₜ-function₄[V] nameTwoStepOrderOn :=
  nameTwoStepOrderOnFormula_defined.to_definable

end ZFVP
