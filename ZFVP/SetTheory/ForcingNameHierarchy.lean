import ZFVP.SetTheory.ForcingNames
import ZFVP.SetTheory.UniformParameterizedRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingNameHierarchyStepFormula : SetTheorySemisentence 3 :=
  f“H P f. ∀ ν, ν ∈ H ↔ ∃ X ∈ !range.dfn f, ν ⊆ !prod.dfn X P”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingNameHierarchyStep (P f : V) : V :=
  ⋃ˢ repl (fun X ↦ ℘ (X ×ˢ P)) (by definability) (range f)

theorem mem_forcingNameHierarchyStep (P f ν : V) :
    ν ∈ forcingNameHierarchyStep P f ↔ ∃ X ∈ range f, ν ⊆ X ×ˢ P := by
  simp only [forcingNameHierarchyStep, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨Y, ⟨X, hX, rfl⟩, hν⟩
    exact ⟨X, hX, mem_power_iff.mp hν⟩
  · rintro ⟨X, hX, hν⟩
    exact ⟨℘ (X ×ˢ P), ⟨X, hX, rfl⟩, mem_power_iff.mpr hν⟩

instance forcingNameHierarchyStepFormula_defined :
    ℒₛₑₜ-function₂[V] forcingNameHierarchyStep via forcingNameHierarchyStepFormula :=
  ⟨fun v ↦ by
    change forcingNameHierarchyStepFormula.Evalb v ↔ v 0 = forcingNameHierarchyStep (v 1) (v 2)
    rw [mem_ext_iff]
    simp [forcingNameHierarchyStepFormula, mem_forcingNameHierarchyStep]⟩

instance forcingNameHierarchyStep_definable : ℒₛₑₜ-function₂[V] forcingNameHierarchyStep :=
  forcingNameHierarchyStepFormula_defined.to_definable

noncomputable def forcingNameHierarchy (P α : V) : V :=
  parameterRecursion forcingNameHierarchyStep forcingNameHierarchyStep_definable P α

instance forcingNameHierarchyFormula_defined :
    ℒₛₑₜ-function₂[V] forcingNameHierarchy via parameterRecursionFormula forcingNameHierarchyStepFormula :=
  parameterRecursionFormula_defined forcingNameHierarchyStep forcingNameHierarchyStepFormula

instance forcingNameHierarchy_definable : ℒₛₑₜ-function₂[V] forcingNameHierarchy :=
  forcingNameHierarchyFormula_defined.to_definable

theorem forcingNameHierarchy_recursion (P α : V) [IsOrdinal α] :
    forcingNameHierarchy P α = forcingNameHierarchyStep P
      (definableGraph α (forcingNameHierarchy P) (by definability)) :=
  Replacement.transfiniteRec_spec (forcingNameHierarchyStep P) (by definability) (IsOrdinal.toOrdinal α)

theorem mem_forcingNameHierarchy (P α ν : V) [IsOrdinal α] :
    ν ∈ forcingNameHierarchy P α ↔ ∃ β ∈ α, ν ⊆ forcingNameHierarchy P β ×ˢ P := by
  rw [forcingNameHierarchy_recursion, mem_forcingNameHierarchyStep, range_definableGraph]
  simp only [repl_spec]
  constructor
  · rintro ⟨X, ⟨β, hβ, rfl⟩, hν⟩
    exact ⟨β, hβ, hν⟩
  · rintro ⟨β, hβ, hν⟩
    exact ⟨forcingNameHierarchy P β, ⟨β, hβ, rfl⟩, hν⟩

theorem forcingNameHierarchy_mono (P : V) {α β : V} [IsOrdinal α] [IsOrdinal β]
    (hαβ : α ⊆ β) : forcingNameHierarchy P α ⊆ forcingNameHierarchy P β := by
  intro ν hν
  obtain ⟨γ, hγ, hν⟩ := (mem_forcingNameHierarchy P α ν).mp hν
  exact (mem_forcingNameHierarchy P β ν).mpr ⟨γ, hαβ γ hγ, hν⟩

theorem forcingNameHierarchy_empty (P : V) : forcingNameHierarchy P ∅ = ∅ := by
  apply mem_ext
  intro ν
  simp [mem_forcingNameHierarchy]

theorem forcingNameHierarchy_succ (P α : V) [IsOrdinal α] :
    forcingNameHierarchy P (succ α) = ℘ (forcingNameHierarchy P α ×ˢ P) := by
  apply mem_ext
  intro ν
  rw [mem_forcingNameHierarchy, mem_power_iff]
  constructor
  · rintro ⟨β, hβ, hν⟩
    rcases mem_succ_iff.mp hβ with rfl | hβα
    · exact hν
    · let := IsOrdinal.of_mem hβα
      intro z hz
      obtain ⟨x, hx, p, hp, rfl⟩ := mem_prod_iff.mp (hν z hz)
      exact kpair_mem_iff.mpr ⟨forcingNameHierarchy_mono P
        (IsOrdinal.toIsTransitive.transitive _ hβα) x hx, hp⟩
  · intro hν
    exact ⟨α, by simp, hν⟩

theorem forcingNameHierarchy_names (P α : V) [IsOrdinal α] :
    ∀ ν ∈ forcingNameHierarchy P α, IsForcingName P ν := by
  have hall := transfinite_induction
    (fun α ↦ ∀ ν ∈ forcingNameHierarchy P α, IsForcingName P ν) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal α)
  intro β ih ν hν
  obtain ⟨γ, hγ, hν⟩ := (mem_forcingNameHierarchy P (β : V) ν).mp hν
  let := IsOrdinal.of_mem hγ
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (hν z hz)
  exact ⟨σ, p, hp, rfl, ih (IsOrdinal.toOrdinal γ) hγ σ hσ⟩

end ZFVP
