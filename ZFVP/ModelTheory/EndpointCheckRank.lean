import ZFVP.ModelTheory.ForcingLowRankNames
import ZFVP.ModelTheory.GenericFilterName
import ZFVP.SetTheory.CnSigmaClosure

/-!
# Rank of checked sets at a `Sigma_1`-correct stage

The `checkRank` field of `ForcingContext.EndpointZFC` asks that the check map send `hierarchy Λ`
into `hierarchy (A.check Λ)`.  That is not automatic for an arbitrary `Λ`, because the check name
of `x` can have larger rank than `x`.  It does hold when `Λ` is `Sigma_1`-correct, since then
`checkName A.one x` stays inside `hierarchy Λ` and the low-rank name lemma applies.

Only `Cn 1 Λ` and `A.one ∈ hierarchy Λ` are used; the poset itself need not lie in `hierarchy Λ`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- The check map does not raise rank past a `Sigma_1`-correct stage: if `x` has rank below `Λ`,
`Λ ∈ C^(1)` and the top condition has rank below `Λ`, then `A.check x` has rank below
`A.check Λ`. -/
theorem check_mem_checked_hierarchy (A : ForcingContext V) {Λ : V}
    (hΛ : Cn 1 Λ) (hone : A.one ∈ hierarchy Λ) {x : V}
    (hx : x ∈ hierarchy Λ) : A.check x ∈ hierarchy (A.check Λ) := by
  let := hΛ.ordinal
  rw [A.check_eq_ofName_checkName]
  exact A.ofName_mem_checked_hierarchy _ (hΛ.checkName_closed hone hx)

/-- The packaged form, matching the `checkRank` field of `EndpointZFC`. -/
theorem checkRank_of_cn (A : ForcingContext V) {Λ : V}
    (hΛ : Cn 1 Λ) (hone : A.one ∈ hierarchy Λ) :
    ∀ x ∈ hierarchy Λ, A.check x ∈ hierarchy (A.check Λ) :=
  fun _ hx ↦ A.check_mem_checked_hierarchy hΛ hone hx

/-- Variant taking the poset instead of the top condition, for callers that have `A.P` low. -/
theorem checkRank_of_cn_of_poset_mem (A : ForcingContext V) {Λ : V}
    (hΛ : Cn 1 Λ) (hP : A.P ∈ hierarchy Λ) :
    ∀ x ∈ hierarchy Λ, A.check x ∈ hierarchy (A.check Λ) := by
  let := hΛ.ordinal
  exact A.checkRank_of_cn hΛ ((hierarchy_transitive Λ).mem_trans A.top.1 hP)

end ForcingContext

end ZFVP
