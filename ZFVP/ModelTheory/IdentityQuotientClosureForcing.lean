import ZFVP.ModelTheory.IdentityQuotientClosure
import ZFVP.ModelTheory.ProjectionQuotientClosureForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def identityQuotientClosureFormula : SetTheorySemisentence 5 :=
  f“P R o π η. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !boundedFunctionFormula π P P ∧ (∀ p ∈ P, !value.dfn π p = p) →
    !allProjectionQuotientClosedBelowFormula P R o P R π η”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem identityQuotient_closedBelow_forced_countable [Countable V] {P R one π η : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hπ : π ∈ P ^ P) (he : ∀ p ∈ P, π ‘ p = p) :
    ForcesProjectionQuotientClosedBelow P R one P R π η := by
  have hproj : IsForcingProjection P R P R π := by
    refine ⟨hπ, ?_, ?_⟩
    · intro q hq r hr hqr
      rwa [he q hq, he r hr]
    · intro q hq p hp hpq
      exact ⟨p, hp, (he q hq) ▸ hpq, he p hp⟩
  apply projectionQuotient_closedBelow_forced_of_generics hR ht hproj hR
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  exact fun α _ ↦ A.identityQuotient_separative_closedAt hπ he α

theorem eval_identityQuotientClosureFormula (v : Fin 5 → V) : identityQuotientClosureFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      v 3 ∈ (v 0) ^ (v 0) → (∀ p ∈ v 0, (v 3) ‘ p = p) →
      ForcesProjectionQuotientClosedBelow (v 0) (v 1) (v 2) (v 0) (v 1) (v 3) (v 4)) := by
  simp [identityQuotientClosureFormula]

theorem identityQuotient_closedBelow_forced {P R one π η : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hπ : π ∈ P ^ P) (he : ∀ p ∈ P, π ‘ p = p) :
    ForcesProjectionQuotientClosedBelow P R one P R π η := by
  have hv := eval_of_countable_zf identityQuotientClosureFormula (by
    intro W _ _ _ _ v
    exact (eval_identityQuotientClosureFormula v).mpr
      (fun hR ht hπ he ↦ identityQuotient_closedBelow_forced_countable hR ht hπ he)) ![P, R, one, π, η]
  exact (eval_identityQuotientClosureFormula _).mp hv hR ht hπ he

end ZFVP
