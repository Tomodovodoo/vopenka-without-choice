import ZFVP.SetTheory.BoundedPairBinding
import ZFVP.SetTheory.LeastWitnessBodies
import ZFVP.SetTheory.LevyPrenexNormalForm

/-! A Sigma-k statement has a unique Pi-k code for all its least-rank witnesses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def leastWitnessCodeFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence (n + 1) :=
  boundedQuadrupleBind (.bvar 0) ((leastWitnessBodyFormula ψ).subst
    (.bvar 0 :> .bvar 1 :> .bvar 2 :> .bvar 3 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ))

theorem leastWitnessCodeFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula k ψ) : IsPiFormula (k + 1) (leastWitnessCodeFormula ψ) :=
  boundedQuadrupleBind_levy _ ((leastWitnessBodyFormula_pi hψ).subst _)

def sigmaWitnessCodeFormula {n : ℕ} (k : ℕ) (S : SetTheorySemisentence n) : SetTheorySemisentence (n + 1) :=
  leastWitnessCodeFormula (sigmaPrenexMatrix k S)

theorem sigmaWitnessCodeFormula_pi {n : ℕ} (k : ℕ) (S : SetTheorySemisentence n) :
    IsPiFormula (k + 1) (sigmaWitnessCodeFormula k S) :=
  leastWitnessCodeFormula_pi (sigmaPrenexMatrix_pi k S)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLeastWitnessCode {n : ℕ} (ψ : SetTheorySemisentence (n + 1)) (v : Fin n → V) (c : V) : Prop :=
  ∃ α A B C : V, c = ⟨α, ⟨A, ⟨B, C⟩ₖ⟩ₖ⟩ₖ ∧ LeastWitnessBody ψ v α A B C

theorem eval_leastWitnessCodeFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (c : V) :
    (leastWitnessCodeFormula ψ).Evalb (c :> v) ↔ IsLeastWitnessCode ψ v c := by
  simp [leastWitnessCodeFormula, eval_boundedQuadrupleBind, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, eval_leastWitnessBodyFormula, IsLeastWitnessCode]

theorem IsLeastWitnessCode.unique {n : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    {v : Fin n → V} {c d : V} (hc : IsLeastWitnessCode ψ v c) (hd : IsLeastWitnessCode ψ v d) : c = d := by
  obtain ⟨α, A, B, C, rfl, hc⟩ := hc
  obtain ⟨β, D, E, F, rfl, hd⟩ := hd
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hc.unique hd
  rfl

theorem IsLeastWitnessCode.witness {n : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    {v : Fin n → V} {c : V} (hc : IsLeastWitnessCode ψ v c) : ∃ u : V, ψ.Evalb (u :> v) := by
  obtain ⟨_, _, _, C, _, hc⟩ := hc
  obtain ⟨u, hu⟩ := hc.2.2.2.1
  exact ⟨u, (hc.witness hu).1⟩

theorem leastWitnessCode_existsUnique {n : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (hex : ∃ u : V, ψ.Evalb (u :> v)) : ∃! c : V, IsLeastWitnessCode ψ v c := by
  obtain ⟨α, A, B, C, hc⟩ := leastWitnessBody_exists ψ v hex
  refine ⟨⟨α, ⟨A, ⟨B, C⟩ₖ⟩ₖ⟩ₖ, ⟨α, A, B, C, rfl, hc⟩, ?_⟩
  intro d hd
  exact hd.unique ⟨α, A, B, C, rfl, hc⟩

theorem sigmaWitnessCodeFormula_existsUnique {n k : ℕ} {S : SetTheorySemisentence n}
    (hS : IsSigmaFormula (k + 1) S) (v : Fin n → V) :
    S.Evalb v ↔ ∃! c : V, (sigmaWitnessCodeFormula k S).Evalb (c :> v) := by
  simp only [sigmaWitnessCodeFormula, eval_leastWitnessCodeFormula]
  constructor
  · intro hs
    exact leastWitnessCode_existsUnique _ v ((sigmaPrenexMatrix_correct hS v).mpr hs)
  · rintro ⟨c, hc, _⟩
    exact (sigmaPrenexMatrix_correct hS v).mp hc.witness

theorem sigmaWitnessCodeFormula_implies {n k : ℕ} {S : SetTheorySemisentence n}
    (hS : IsSigmaFormula (k + 1) S) (v : Fin n → V) (c : V)
    (hc : (sigmaWitnessCodeFormula k S).Evalb (c :> v)) : S.Evalb v :=
  (sigmaPrenexMatrix_correct hS v).mp ((eval_leastWitnessCodeFormula _ v c).mp hc).witness

theorem sigmaWitnessCodeFormula_unique {n k : ℕ} {S : SetTheorySemisentence n}
    (v : Fin n → V) (c d : V)
    (hc : (sigmaWitnessCodeFormula k S).Evalb (c :> v))
    (hd : (sigmaWitnessCodeFormula k S).Evalb (d :> v)) : c = d :=
  ((eval_leastWitnessCodeFormula _ v c).mp hc).unique ((eval_leastWitnessCodeFormula _ v d).mp hd)

end ZFVP
