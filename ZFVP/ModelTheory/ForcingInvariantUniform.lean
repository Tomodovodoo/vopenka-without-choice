import ZFVP.ModelTheory.ForcingCodeConstructionUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def iterationTableFormula : SetTheorySemisentence 2 :=
  f“A g. !IsFunction.dfn g ∧ !domain.dfn g = A”

@[irreducible] def orderedSplitForcingSystemFormula : SetTheorySemisentence 5 :=
  f“θ P R π E.
    (∀ i ∈ θ, !forcingPreorderFormula (!value.dfn P i) (!value.dfn R i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ !value.dfn P j, ∀ b ∈ !value.dfn P j,
      !kpair.dfn a b ∈ !value.dfn R j →
      !kpair.dfn (!value.dfn (!value.dfn π (!kpair.dfn i j)) a)
        (!value.dfn (!value.dfn π (!kpair.dfn i j)) b) ∈ !value.dfn R i) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ !value.dfn P j, ∀ b ∈ !value.dfn P i,
      !kpair.dfn a (!value.dfn (!value.dfn E (!kpair.dfn i j)) b) ∈ !value.dfn R j ↔
      !kpair.dfn (!value.dfn (!value.dfn π (!kpair.dfn i j)) a) b ∈ !value.dfn R i)”

@[irreducible] def functionalSplitForcingSystemFormula : SetTheorySemisentence 4 :=
  f“θ P π E.
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → !boundedFunctionFormula (!value.dfn π (!kpair.dfn i j)) (!value.dfn P j) (!value.dfn P i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → !boundedFunctionFormula (!value.dfn E (!kpair.dfn i j)) (!value.dfn P i) (!value.dfn P j))”

@[irreducible] def toppedSplitForcingSystemFormula : SetTheorySemisentence 6 :=
  f“θ P R π E t.
    (∀ i ∈ θ, !forcingTopFormula (!value.dfn P i) (!value.dfn R i) (!value.dfn t i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → !value.dfn (!value.dfn π (!kpair.dfn i j)) (!value.dfn t j) = !value.dfn t i) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → !value.dfn (!value.dfn E (!kpair.dfn i j)) (!value.dfn t i) = !value.dfn t j)”

@[irreducible] def coherentForcingLiftFormula : SetTheorySemisentence 5 :=
  f“θ P R π L.
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ !value.dfn P j, ∀ b ∈ !value.dfn P i,
      !kpair.dfn b (!value.dfn (!value.dfn π (!kpair.dfn i j)) a) ∈ !value.dfn R i →
      !value.dfn (!value.dfn L (!kpair.dfn i j)) (!kpair.dfn a b) ∈ !value.dfn P j ∧
      !kpair.dfn (!value.dfn (!value.dfn L (!kpair.dfn i j)) (!kpair.dfn a b)) a ∈ !value.dfn R j ∧
      !value.dfn (!value.dfn π (!kpair.dfn i j)) (!value.dfn (!value.dfn L (!kpair.dfn i j)) (!kpair.dfn a b)) = b) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k → ∀ a ∈ !value.dfn P k, ∀ b ∈ !value.dfn P i,
      !kpair.dfn b (!value.dfn (!value.dfn π (!kpair.dfn i k)) a) ∈ !value.dfn R i →
      !value.dfn (!value.dfn π (!kpair.dfn j k)) (!value.dfn (!value.dfn L (!kpair.dfn i k)) (!kpair.dfn a b)) =
      !value.dfn (!value.dfn L (!kpair.dfn i j)) (!kpair.dfn (!value.dfn (!value.dfn π (!kpair.dfn j k)) a) b))”

@[irreducible] def sectionCompatibleForcingLiftFormula : SetTheorySemisentence 6 :=
  f“θ P R π E L.
    ∀ i ∈ θ, ∀ k ∈ θ, ∀ j ∈ θ, i ⊆ k → k ⊆ j → ∀ a ∈ !value.dfn P k, ∀ b ∈ !value.dfn P i,
      !kpair.dfn b (!value.dfn (!value.dfn π (!kpair.dfn i k)) a) ∈ !value.dfn R i →
      !value.dfn (!value.dfn L (!kpair.dfn i j)) (!kpair.dfn (!value.dfn (!value.dfn E (!kpair.dfn k j)) a) b) =
      !value.dfn (!value.dfn E (!kpair.dfn k j)) (!value.dfn (!value.dfn L (!kpair.dfn i k)) (!kpair.dfn a b))”

@[irreducible] def forcingIterationSystemFormula : SetTheorySemisentence 7 :=
  f“θ P R π E L t. !splitForcingSystemFormula θ P π E ∧ !orderedSplitForcingSystemFormula θ P R π E ∧
    !functionalSplitForcingSystemFormula θ P π E ∧ !toppedSplitForcingSystemFormula θ P R π E t ∧
    !coherentForcingLiftFormula θ P R π L ∧ !sectionCompatibleForcingLiftFormula θ P R π E L”

@[irreducible] def isForcingIterationCodeFormula : SetTheorySemisentence 2 :=
  f“θ s.
    !forcingIterationSystemFormula θ (!forcingCodePFormula s) (!forcingCodeRFormula s) (!forcingCodeπFormula s)
      (!forcingCodeEFormula s) (!forcingCodeLFormula s) (!forcingCodetFormula s) ∧
    !iterationTableFormula θ (!forcingCodePFormula s) ∧ !iterationTableFormula θ (!forcingCodeRFormula s) ∧
    !iterationTableFormula (!prod.dfn θ θ) (!forcingCodeπFormula s) ∧
    !iterationTableFormula (!prod.dfn θ θ) (!forcingCodeEFormula s) ∧
    !iterationTableFormula (!prod.dfn θ θ) (!forcingCodeLFormula s) ∧ !iterationTableFormula θ (!forcingCodetFormula s)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance iterationTableFormula_defined : Defined (fun v : Fin 2 → V ↦ IsIterationTable (v 0) (v 1)) iterationTableFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [iterationTableFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.function, h.domain_eq⟩⟩

instance orderedSplitForcingSystemFormula_defined : Defined (fun v : Fin 5 → V ↦ IsOrderedSplitForcingSystem (v 0) (v 1) (v 2) (v 3) (v 4)) orderedSplitForcingSystemFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [orderedSplitForcingSystemFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2⟩, fun h ↦ ⟨h.preorder, h.projMono, h.below⟩⟩

instance functionalSplitForcingSystemFormula_defined : Defined (fun v : Fin 4 → V ↦ IsFunctionalSplitForcingSystem (v 0) (v 1) (v 2) (v 3)) functionalSplitForcingSystemFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [functionalSplitForcingSystemFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.projection, h.sectionMap⟩⟩

instance toppedSplitForcingSystemFormula_defined : Defined (fun v : Fin 6 → V ↦ IsToppedSplitForcingSystem (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) toppedSplitForcingSystemFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [toppedSplitForcingSystemFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2⟩, fun h ↦ ⟨h.top, h.projTop, h.secTop⟩⟩

instance coherentForcingLiftFormula_defined : Defined (fun v : Fin 5 → V ↦ IsCoherentForcingLift (v 0) (v 1) (v 2) (v 3) (v 4)) coherentForcingLiftFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [coherentForcingLiftFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.lift, h.commute⟩⟩

instance sectionCompatibleForcingLiftFormula_defined : Defined (fun v : Fin 6 → V ↦ IsSectionCompatibleForcingLift (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) sectionCompatibleForcingLiftFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [sectionCompatibleForcingLiftFormula]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.compatible⟩

instance forcingIterationSystemFormula_defined : Defined (fun v : Fin 7 → V ↦ IsForcingIterationSystem (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) forcingIterationSystemFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [forcingIterationSystemFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩, fun h ↦ ⟨h.split, h.order, h.functions, h.tops, h.lifts, h.compatible⟩⟩

instance isForcingIterationCodeFormula_defined : Defined (fun v : Fin 2 → V ↦ IsForcingIterationCode (v 0) (v 1)) isForcingIterationCodeFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [isForcingIterationCodeFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, fun h ↦ ⟨h.system, h.tableP, h.tableR, h.tableπ, h.tableE, h.tableL, h.tablet⟩⟩

end ZFVP
