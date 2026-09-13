import ZFVP.Syntax.UniformFormulas

/-! Elementary maps transport the shared definitions of term and formula sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace ElementaryMap

variable {V W : Type*} [SetStructure V] [SetStructure W]

theorem map_definedFunction {k : ℕ} (j : ElementaryMap V W) (φ : SetTheorySemisentence (k + 1))
    (F : (Fin k → V) → V) (G : (Fin k → W) → W)
    [DefinedFunction F φ] [DefinedFunction G φ] (v : Fin k → V) : j (F v) = G (j ∘ v) := by
  have h := j.map_defined φ (fun w ↦ w 0 = F (w ·.succ))
    (fun w ↦ w 0 = G (w ·.succ)) (F v :> v)
  exact h.mp rfl

variable [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_syntaxUniverse (j : ElementaryMap V W) (L Γ : V) :
    j (syntaxUniverse L Γ) = syntaxUniverse (j L) (j Γ) :=
  j.map_definedFunction syntaxUniverseFormula (fun v ↦ syntaxUniverse (v 0) (v 1))
    (fun v ↦ syntaxUniverse (v 0) (v 1)) ![L, Γ]

theorem map_termSet (j : ElementaryMap V W) (L Γ n : V) :
    j (termSet L Γ n) = termSet (j L) (j Γ) (j n) :=
  j.map_definedFunction termSetFormula (fun v ↦ termSet (v 0) (v 1) (v 2))
    (fun v ↦ termSet (v 0) (v 1) (v 2)) ![L, Γ, n]

theorem map_formulaFamily (j : ElementaryMap V W) (L Γ : V) :
    j (formulaFamily L Γ) = formulaFamily (j L) (j Γ) :=
  j.map_definedFunction formulaFamilyFormula (fun v ↦ formulaFamily (v 0) (v 1))
    (fun v ↦ formulaFamily (v 0) (v 1)) ![L, Γ]

theorem map_formulaSet (j : ElementaryMap V W) (L Γ n : V) :
    j (formulaSet L Γ n) = formulaSet (j L) (j Γ) (j n) :=
  j.map_definedFunction formulaSetFormula (fun v ↦ formulaSet (v 0) (v 1) (v 2))
    (fun v ↦ formulaSet (v 0) (v 1) (v 2)) ![L, Γ, n]

theorem map_term_mem_iff (j : ElementaryMap V W) (L Γ n t : V) :
    j t ∈ termSet (j L) (j Γ) (j n) ↔ t ∈ termSet L Γ n := by
  rw [← j.map_termSet, j.map_mem_iff]

theorem map_formula_mem_iff (j : ElementaryMap V W) (L Γ n φ : V) :
    j φ ∈ formulaSet (j L) (j Γ) (j n) ↔ φ ∈ formulaSet L Γ n := by
  rw [← j.map_formulaSet, j.map_mem_iff]

end ElementaryMap
end ZFVP
