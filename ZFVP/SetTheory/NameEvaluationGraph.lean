import ZFVP.SetTheory.ForcingPairNames
import ZFVP.SetTheory.CheckNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def nameEvaluationGraph (one C : V) : V :=
  repl (fun σ ↦ ⟨orderedPairName one (checkName one σ) σ, one⟩ₖ) (by definability) C

theorem mem_nameEvaluationGraph_iff (one C z : V) :
    z ∈ nameEvaluationGraph one C ↔ ∃ σ ∈ C, z = ⟨orderedPairName one (checkName one σ) σ, one⟩ₖ :=
  repl_spec (by definability)

theorem nameEvaluationGraph_isName {P one C : V} (hone : one ∈ P)
    (hC : ∀ σ ∈ C, IsForcingName P σ) : IsForcingName P (nameEvaluationGraph one C) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, rfl⟩ := (mem_nameEvaluationGraph_iff _ _ _).mp hz
  exact ⟨orderedPairName one (checkName one σ) σ, one, hone, rfl,
    orderedPairName_isName hone (checkName_isName hone σ) (hC σ hσ)⟩

end ZFVP
