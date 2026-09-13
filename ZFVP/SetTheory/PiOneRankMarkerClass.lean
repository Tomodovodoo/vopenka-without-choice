import ZFVP.ModelTheory.DeltaOneMarkerStructures
import ZFVP.SetTheory.BoundedOrdinalOmega
import ZFVP.SetTheory.PiOneHierarchy
import ZFVP.SetTheory.BoundedPairBinding
import ZFVP.SetTheory.RankMarkerStructures

/-! The one-marker rank class is Pi-one with the base hierarchy segment as a parameter. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneOrdinalOmegaHierarchyFormula : SetTheorySemisentence 2 :=
  “A δ. !IsOrdinal.dfn δ ∧ ∀ η, !boundedOrdinalOmegaFormula η δ → !piOneHierarchyFormula A η”

def piOneRankMarkerBody : SetTheorySemisentence 5 :=
  “A C M ρ B. ∃ δ ∈ A, !IsOrdinal.dfn δ ∧ !isSubsetOf ρ δ ∧
    !piOneOrdinalOmegaHierarchyFormula A δ ∧ !piOneMarkerStructureFormula M B A δ”

def piOneRankMarkerClassFormula : SetTheorySemisentence 3 :=
  boundedPairBind (.bvar 0) piOneRankMarkerBody

theorem piOneOrdinalOmegaHierarchyFormula_piOne : IsPiFormula 1 piOneOrdinalOmegaHierarchyFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or (.bounded (boundedOrdinalOmegaFormula_bounded.subst _).neg)
      (piOneHierarchyFormula_piOne.subst _)))

theorem piOneRankMarkerBody_piOne : IsPiFormula 1 piOneRankMarkerBody :=
  .boundedExs (.bvar 0) (.and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.bounded (isSubsetOf_bounded.subst _))
      (.and (piOneOrdinalOmegaHierarchyFormula_piOne.subst _) (piOneMarkerStructureFormula_piOne.subst _))))

theorem piOneRankMarkerClassFormula_piOne : IsPiFormula 1 piOneRankMarkerClassFormula :=
  boundedPairBind_levy _ piOneRankMarkerBody_piOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_piOneOrdinalOmegaHierarchyFormula (A δ : V) :
    piOneOrdinalOmegaHierarchyFormula.Evalb ![A, δ] ↔ IsOrdinal δ ∧ A = hierarchy (ordinalAdd δ ω) := by
  simp [piOneOrdinalOmegaHierarchyFormula, eval_boundedOrdinalOmegaFormula]
  intro hδ
  let := hδ
  simp [IsHierarchySegment, hδ, show IsOrdinal (ordinalAdd δ (ω : V)) from inferInstance]

theorem eval_piOneRankMarkerBody (A C M ρ B : V) :
    piOneRankMarkerBody.Evalb ![A, C, M, ρ, B] ↔
      ∃ δ ∈ A, IsOrdinal δ ∧ ρ ⊆ δ ∧ A = hierarchy (ordinalAdd δ ω) ∧ M = markerStructure B A δ := by
  simp [piOneRankMarkerBody, eval_piOneOrdinalOmegaHierarchyFormula, eval_piOneMarkerStructureFormula,
    and_left_comm, and_comm]

theorem eval_piOneRankMarkerClassFormula (M ρ B : V) :
    piOneRankMarkerClassFormula.Evalb ![M, ρ, B] ↔
      ∃ δ, IsOrdinal δ ∧ ρ ⊆ δ ∧ M = markerStructure B (hierarchy (ordinalAdd δ ω)) δ := by
  rw [piOneRankMarkerClassFormula, eval_boundedPairBind]
  simp only [Semiterm.val_bvar, Matrix.cons_val_zero, eval_piOneRankMarkerBody]
  constructor
  · rintro ⟨A, C, _, δ, _, hδ, hρ, rfl, hM⟩
    exact ⟨δ, hδ, hρ, hM⟩
  · rintro ⟨δ, hδ, hρ, rfl⟩
    let := hδ
    refine ⟨hierarchy (ordinalAdd δ ω), _, rfl, δ, rankMarkerStructure_marker_mem δ, hδ, hρ, rfl, rfl⟩

theorem eval_piOneRankMarkerClassFormula_hierarchy (M ρ : V) :
    piOneRankMarkerClassFormula.Evalb ![M, ρ, hierarchy ρ] ↔ IsRankMarkerStructure ρ M :=
  eval_piOneRankMarkerClassFormula M ρ (hierarchy ρ)

end ZFVP
