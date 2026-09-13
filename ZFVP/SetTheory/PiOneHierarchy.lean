import ZFVP.SetTheory.DeltaOneRank

/-! The graph of the cumulative hierarchy on ordinals is Pi-one. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneRankLtFormula : SetTheorySemisentence 2 :=
  “x α. ∃ β ∈ α, !sigmaOneRankFormula β x”

def piOneRankLtFormula : SetTheorySemisentence 2 :=
  “x α. ∃ β ∈ α, !piOneRankFormula β x”

def piOneHierarchyFormula : SetTheorySemisentence 2 :=
  “A α. !IsOrdinal.dfn α ∧ ∀ x,
    (x ∈ A → !piOneRankLtFormula x α) ∧ (!sigmaOneRankLtFormula x α → x ∈ A)”

theorem sigmaOneRankLtFormula_sigmaOne : IsSigmaFormula 1 sigmaOneRankLtFormula :=
  .boundedExs (.bvar 1) (sigmaOneRankFormula_sigmaOne.subst _)

theorem piOneRankLtFormula_piOne : IsPiFormula 1 piOneRankLtFormula :=
  .boundedExs (.bvar 1) (piOneRankFormula_piOne.subst _)

theorem piOneHierarchyFormula_piOne : IsPiFormula 1 piOneHierarchyFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.and (.or (.bounded (.nrel _ _)) (piOneRankLtFormula_piOne.subst _))
      (.or (sigmaOneRankLtFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneRankLtFormula (x α : V) : sigmaOneRankLtFormula.Evalb ![x, α] ↔ rank x ∈ α := by
  simp [sigmaOneRankLtFormula]

theorem eval_piOneRankLtFormula (x α : V) : piOneRankLtFormula.Evalb ![x, α] ↔ rank x ∈ α := by
  simp [piOneRankLtFormula]

theorem eval_piOneHierarchyFormula (A α : V) :
    piOneHierarchyFormula.Evalb ![A, α] ↔ IsOrdinal α ∧ A = hierarchy α := by
  simp [piOneHierarchyFormula, eval_sigmaOneRankLtFormula, eval_piOneRankLtFormula]
  intro hα
  let := hα
  rw [mem_ext_iff]
  simp only [mem_hierarchy_iff_rank_mem]
  exact forall_congr' fun x ↦ ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.mp, h.mpr⟩⟩

def IsHierarchySegment (A α : V) : Prop := IsOrdinal α ∧ A = hierarchy α

instance piOneHierarchyFormula_defined : ℒₛₑₜ-relation[V] IsHierarchySegment via piOneHierarchyFormula :=
  ⟨fun (v : Fin 2 → V) ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    change piOneHierarchyFormula.Evalb v ↔ IsHierarchySegment (v 0) (v 1)
    rw [← hv]
    exact eval_piOneHierarchyFormula (v 0) (v 1)⟩

end ZFVP
