import ZFVP.SetTheory.ForcingUniqueNameRank
import ZFVP.ModelTheory.ForcingFormulaName
import ZFVP.ModelTheory.ForcingSemanticConsequence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaUniqueName_mem_hierarchy_of_witness {P R δ ν : V} [IsOrdinal δ]
    (hs : ∀ α ∈ δ, succ α ∈ δ) (hP : P ∈ hierarchy δ) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → V)
    (hν : IsForcingName P ν) (hνδ : ν ∈ hierarchy δ)
    (hf : ∀ p ∈ P, p ∈ forcingFormula P R φ (standardTuple (ν :> v))) :
    formulaUniqueName P R φ (standardTuple v) ∈ hierarchy δ := by
  apply forcingUniqueName_mem_hierarchy_of_witness hs hP
    (fun a τ ↦ forcingFormula P R φ (assignmentPrepend (n : V) a τ)) (by definability) hν hνδ
  intro p hp
  simpa only [standardTuple, Matrix.cons_val_zero, Matrix.cons_val_succ] using hf p hp

theorem formulaUniqueName_mem_hierarchy_of_semantics [Countable V] {P R one δ : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hs : ∀ α ∈ δ, succ α ∈ δ) (hP : P ∈ hierarchy δ) {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (v : Fin n → ForcingName P) (ν : ForcingName P)
    (hνδ : ν.val ∈ hierarchy δ)
    (htruth : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      φ.Evalb (fun i ↦ (ForcingContext.mk P R one G hR htop hG).ofName ((ν :> v) i))) :
    formulaUniqueName P R φ (standardTuple (fun i ↦ (v i).val)) ∈ hierarchy δ := by
  apply formulaUniqueName_mem_hierarchy_of_witness hs hP φ _ ν.property hνδ
  intro p hp
  exact forcingFormula_of_all_generics hR htop hp φ (ν :> v) (fun G hG _ ↦ htruth G hG)

end ZFVP
