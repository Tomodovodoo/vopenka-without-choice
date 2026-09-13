import ZFVP.SetTheory.UsubaLSSequence

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance usubaLSSequence_uniform_definable : ℒₛₑₜ-function₂[V] usubaLSSequence := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 3 → V ↦
      (∃ f, IsAttempt (ordinalClosureStep usubaNextLS (v 1)) (v 2) f ∧
        v 0 = ordinalClosureStep usubaNextLS (v 1) f) ∨
      (¬IsOrdinal (v 2) ∧ v 0 = ∅)) := by
    unfold IsAttempt ordinalClosureStep
    definability
  apply Language.Definable.of_iff h
  intro v
  exact transfiniteRec_eq_iff (ordinalClosureStep usubaNextLS (v 1))
    (ordinalClosureStep_definable usubaNextLS (by definability) (v 1)) (v 2) (v 0)

instance usubaLSLimit_uniform_definable : ℒₛₑₜ-function₂[V] usubaLSLimit := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 3 → V ↦
      ∀ x, x ∈ v 0 ↔ ∃ i ∈ v 2, x ∈ usubaLSSequence (v 1) i) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = usubaLSLimit (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_usubaLSLimit]

end ZFVP
