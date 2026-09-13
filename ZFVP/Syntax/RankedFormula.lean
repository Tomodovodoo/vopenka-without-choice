import ZFVP.SetTheory.DeltaOneRank

/-! Add the rank of a class member as a distinguished bound parameter. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankedFormula {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence (n + 2) :=
  (piOneRankFormula.subst ![.bvar 0, .bvar 1]).and (φ.subst (fun i ↦ .bvar i.succ))

theorem rankedFormula_pi {n k : ℕ} {φ : SetTheorySemisentence (n + 1)}
    (hφ : IsPiFormula k φ) (hk : 0 < k) : IsPiFormula k (rankedFormula φ) :=
  .and ((piOneRankFormula_piOne.subst _).mono hk) (hφ.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankedFormula_eval {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (α x : V) (v : Fin n → V) :
    (rankedFormula φ).Evalb (α :> x :> v) ↔ α = rank x ∧ φ.Evalb (x :> v) := by
  change ((piOneRankFormula.subst ![.bvar 0, .bvar 1]).Evalb (α :> x :> v) ∧
    (φ.subst (fun i ↦ .bvar i.succ)).Evalb (α :> x :> v)) ↔ _
  simp [Semiformula.eval_substs, Function.comp_def]

end ZFVP

