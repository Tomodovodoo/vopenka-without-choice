import ZFVP.SetTheory.LeastWitnessCertificate
import ZFVP.SetTheory.DeltaOneBoundedTruth

/-! Pi_1 formulas for the rank and set components of a least-witness certificate. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneSuccessorHierarchyFormula : SetTheorySemisentence 2 :=
  “W ξ. ∀ s, !boundedSuccFormula s ξ → !piOneHierarchyFormula W s”

theorem piOneSuccessorHierarchyFormula_piOne : IsPiFormula 1 piOneSuccessorHierarchyFormula :=
  .all (.or (.bounded (boundedSuccFormula_bounded.subst _).neg)
    (piOneHierarchyFormula_piOne.subst _))

def leastWitnessCertificateBaseFormula : SetTheorySemisentence 4 :=
  “ξ U W C. !piOneHierarchyFormula U ξ ∧ !piOneSuccessorHierarchyFormula W ξ ∧
    !boundedNonemptyFormula C ∧ !isSubsetOf C W”

theorem leastWitnessCertificateBaseFormula_piOne : IsPiFormula 1 leastWitnessCertificateBaseFormula :=
  .and (piOneHierarchyFormula_piOne.subst _) (.and (piOneSuccessorHierarchyFormula_piOne.subst _)
    (.and (.bounded (boundedNonemptyFormula_bounded.subst _)) (.bounded (isSubsetOf_bounded.subst _))))

def certificateWitnessFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence (n + 5) :=
  ψ.subst (.bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance piOneSuccessorHierarchyFormula_defined :
    ℒₛₑₜ-relation[V] (fun W ξ ↦ IsHierarchySegment W (succ ξ)) via piOneSuccessorHierarchyFormula :=
  ⟨fun v ↦ by simp [piOneSuccessorHierarchyFormula]⟩

theorem eval_leastWitnessCertificateBaseFormula (ξ U W C : V) :
    leastWitnessCertificateBaseFormula.Evalb ![ξ, U, W, C] ↔
      IsOrdinal ξ ∧ U = hierarchy ξ ∧ W = hierarchy (succ ξ) ∧ IsNonempty C ∧ C ⊆ W := by
  simp [leastWitnessCertificateBaseFormula, IsHierarchySegment]
  constructor
  · rintro ⟨⟨hξ, hU⟩, ⟨_, hW⟩, hC, hCW⟩
    exact ⟨hξ, hU, hW, hC, hCW⟩
  · rintro ⟨hξ, hU, hW, hC, hCW⟩
    let := hξ
    exact ⟨⟨hξ, hU⟩, ⟨inferInstance, hW⟩, hC, hCW⟩

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_certificateWitnessFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (u ξ U W C : V) (v : Fin n → V) :
    (certificateWitnessFormula ψ).Evalb (u :> ξ :> U :> W :> C :> v) ↔ ψ.Evalb (u :> v) := by
  simp [certificateWitnessFormula, Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def]

end ZFVP
