import ZFVP.ModelTheory.BooleanGenericTransfer
import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.BooleanCompletionValues

/-! Boolean values: a generic filter on the Boolean completion contains the regular join of a
regular set of Boolean conditions exactly when it meets that set, so truth in the Boolean
extension is membership of the Boolean value `‖φ(v)‖ ∈ RO(P)` in the transferred generic, i.e.
the original generic meets `‖φ(v)‖`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A generic filter on the Boolean completion contains the join of a regular set of Boolean
conditions if and only if it meets that set. -/
theorem regularJoin_mem_iff_meets {P R S : V} {H : Set V} (hR : IsForcingPreorder P R)
    (hH : IsExternalForcingGeneric (booleanConditions P R) (booleanOrder P R) H)
    (hS : IsForcingRegular (booleanConditions P R) (booleanOrder P R) S) :
    regularJoin P R S ∈ H ↔ GenericMeets H S := by
  constructor
  · intro hc
    have hcB : regularJoin P R S ∈ booleanConditions P R := hH.1.1 _ hc
    obtain ⟨q, hqH, hqS⟩ := externalForcingGeneric_meets_denseBelow (booleanOrder_poset P R).1 hH hc
      (boolean_regular_denseBelow hR hS hcB (fun x hx ↦ hx))
    exact ⟨q, hqH, hqS⟩
  · rintro ⟨A, hAH, hAS⟩
    have hAB := hH.1.1 A hAH
    have hcB := regularJoin_mem_booleanConditions hR hS.1 hAS
    exact hH.1.2.2.1 A hAH _ hcB
      ((kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hAB, hcB, subset_regularJoin_of_mem hR hS.1 hAS⟩)

theorem mem_booleanGeneric_iff (P R : V) (G : Set V) (C : V) :
    C ∈ booleanGeneric P R G ↔ C ∈ booleanConditions P R ∧ ∃ p ∈ G, p ∈ C := Iff.rfl

namespace ForcingContext

/-- The Boolean value `‖φ(v)‖ ∈ RO(P)` of a formula at names for the Boolean completion. -/
noncomputable def booleanValue (A : ForcingContext V) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → V) : V :=
  regularJoin A.P A.R
    (forcingFormula (booleanConditions A.P A.R) (booleanOrder A.P A.R) φ (standardTuple v))

theorem booleanValue_regular (A : ForcingContext V) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → V) : IsForcingRegular A.P A.R (A.booleanValue φ v) :=
  regularJoin_booleanSubset_regular A.order
    (forcingFormula_regular (booleanOrder_poset A.P A.R).1 φ _).1

/-- Truth in the Boolean extension is membership of the Boolean value in the transferred generic. -/
theorem booleanValue_truth (A : ForcingContext V) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → ForcingName A.booleanContext.P) :
    φ.Evalb (fun i ↦ A.booleanContext.ofName (v i)) ↔
      A.booleanValue φ (fun i ↦ (v i).val) ∈ A.booleanContext.G := by
  rw [A.booleanContext.formula_truth φ v]
  exact (regularJoin_mem_iff_meets A.order A.booleanContext.generic
    (forcingFormula_regular (booleanOrder_poset A.P A.R).1 φ _)).symm

/-- Truth in the Boolean extension is the original generic meeting the Boolean value. -/
theorem booleanValue_truth_meets (A : ForcingContext V) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → ForcingName A.booleanContext.P) :
    φ.Evalb (fun i ↦ A.booleanContext.ofName (v i)) ↔
      GenericMeets A.G (A.booleanValue φ (fun i ↦ (v i).val)) := by
  rw [A.booleanValue_truth φ v]
  change _ ∈ booleanGeneric A.P A.R A.G ↔ _
  rw [mem_booleanGeneric_iff]
  constructor
  · rintro ⟨_, p, hp, hpv⟩
    exact ⟨p, hp, hpv⟩
  · rintro ⟨p, hp, hpv⟩
    exact ⟨(mem_booleanConditions_iff _ _ _).mpr ⟨A.booleanValue_regular φ _, p, hpv⟩, p, hp, hpv⟩

end ForcingContext

end ZFVP
