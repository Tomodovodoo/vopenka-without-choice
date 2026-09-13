import ZFVP.ModelTheory.ForcingSemanticConsequence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem atomicMembership_of_all_generics [Countable V] {P R one p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (σ τ : ForcingName P)
    (htruth : ∀ G : Set V, ∀ hG : IsExternalForcingGeneric P R G, p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      A.ofName σ ∈ A.ofName τ) :
    p ∈ atomicMembership P R σ.val τ.val := by
  let φ : SetTheorySemisentence 2 := .rel Language.Set.Rel.mem ![.bvar 0, .bvar 1]
  have hh := forcingFormula_of_all_generics hR ht hp φ ![σ, τ] (by
    intro G hG hpG
    exact htruth G hG hpG)
  simpa only [φ, forcingFormula_rel, forcingAtomic, forcingTermValue, value_standardTuple,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hh

end ZFVP

