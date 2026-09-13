import ZFVP.SetTheory.UniformFormulaWitnessBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def formulaWitnessNameFormula {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence 4 :=
  f“E P R a. ∃ α, !(formulaWitnessBoundFormula φ) α P R a ∧ ∀ z, z ∈ E ↔
    z ∈ !prod.dfn (!hierarchyFormula α) P ∧ !forcingNameFormula P (!kpair.π₁.dfn z) ∧
      !(formulaOutputTruthFormula φ) P R a (!kpair.π₁.dfn z) (!kpair.π₂.dfn z)”

def forcingUnionNameFormula : SetTheorySemisentence 4 :=
  f“U P R E. ∀ z, z ∈ U ↔ z ∈ !prod.dfn (!nameClosureFormula E) P ∧
    ∃ σ s t, !kpair.dfn σ s ∈ E ∧ !kpair.dfn (!kpair.π₁.dfn z) t ∈ σ ∧
      !kpair.dfn (!kpair.π₂.dfn z) s ∈ R ∧ !kpair.dfn (!kpair.π₂.dfn z) t ∈ R”

def formulaUniqueNameFormula {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence 4 :=
  f“U P R a. ∃ E, !(formulaWitnessNameFormula φ) E P R a ∧ !forcingUnionNameFormula U P R E”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance formulaWitnessNameFormula_defined {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    Defined (fun v : Fin 4 → V ↦ v 0 = forcingWitnessName (v 1)
      (fun a ν ↦ forcingFormula (v 1) (v 2) φ (assignmentPrepend (n : V) a ν))
      (by definability) (v 3)) (formulaWitnessNameFormula φ) := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [formulaWitnessNameFormula, forcingWitnessName]
  constructor
  · rintro ⟨x, he, hx⟩
    exact he ▸ hx
  · intro hx
    exact ⟨_, rfl, hx⟩

instance forcingUnionNameFormula_defined :
    ℒₛₑₜ-function₃[V] forcingUnionName via forcingUnionNameFormula := by
  refine ⟨fun v ↦ ?_⟩
  change forcingUnionNameFormula.Evalb v ↔ v 0 = forcingUnionName (v 1) (v 2) (v 3)
  rw [mem_ext_iff]
  simp [forcingUnionNameFormula, forcingUnionName]

instance formulaUniqueNameFormula_defined {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    ℒₛₑₜ-function₃[V] (fun P R a ↦ formulaUniqueName P R φ a) via formulaUniqueNameFormula φ := by
  refine ⟨fun v ↦ ?_⟩
  simp [formulaUniqueNameFormula, formulaUniqueName, forcingUniqueName]
  constructor
  · rintro ⟨x, he, hx⟩
    exact he ▸ hx
  · intro hx
    exact ⟨_, rfl, hx⟩

end ZFVP
