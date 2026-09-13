import ZFVP.Syntax.UniformSatisfaction
import ZFVP.Syntax.UniformSyntaxTransport

/-! Elementary transport of term evaluation and internal satisfaction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace ElementaryMap

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_packedTermEvaluation (j : ElementaryMap V W) (P n b : V) :
    j (packedTermEvaluation P n b) = packedTermEvaluation (j P) (j n) (j b) :=
  j.map_definedFunction packedTermEvaluationFormula (fun v ↦ packedTermEvaluation (v 0) (v 1) (v 2))
    (fun v ↦ packedTermEvaluation (v 0) (v 1) (v 2)) ![P, n, b]

theorem map_satisfactionParameters (j : ElementaryMap V W) (L Γ M e : V) :
    j (satisfactionParameters L Γ M e) = satisfactionParameters (j L) (j Γ) (j M) (j e) :=
  j.map_definedFunction satisfactionParametersFormula
    (fun v ↦ satisfactionParameters (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ satisfactionParameters (v 0) (v 1) (v 2) (v 3)) ![L, Γ, M, e]

theorem map_termEvaluation (j : ElementaryMap V W) (L Γ n M b e : V) :
    j (termEvaluation L Γ n M b e) = termEvaluation (j L) (j Γ) (j n) (j M) (j b) (j e) := by
  have h := j.map_packedTermEvaluation (satisfactionParameters L Γ M e) n b
  rw [j.map_satisfactionParameters] at h
  simpa only [packedTermEvaluation, satisfactionParameters, satLanguage, satVariables,
    satStructure, satFreeAssignment, kpair.π₁_kpair, kpair.π₂_kpair] using h

theorem map_satisfactionGraph (j : ElementaryMap V W) (L Γ M e : V) :
    j (satisfactionGraph L Γ M e) = satisfactionGraph (j L) (j Γ) (j M) (j e) :=
  j.map_definedFunction satisfactionGraphFormula
    (fun v ↦ satisfactionGraph (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ satisfactionGraph (v 0) (v 1) (v 2) (v 3)) ![L, Γ, M, e]

theorem map_satisfies_iff (j : ElementaryMap V W) (L Γ M e n φ b : V) :
    Satisfies (j L) (j Γ) (j M) (j e) (j n) (j φ) (j b) ↔ Satisfies L Γ M e n φ b :=
  (j.map_defined satisfiesFormula
    (fun v ↦ Satisfies (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (fun v ↦ Satisfies (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) ![L, Γ, M, e, n, φ, b]).symm

end ElementaryMap
end ZFVP
