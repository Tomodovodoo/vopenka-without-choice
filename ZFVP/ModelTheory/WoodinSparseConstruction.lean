import ZFVP.ModelTheory.WoodinSparseSuccessorStep
import ZFVP.ModelTheory.WoodinSparseDirectStep
import ZFVP.ModelTheory.WoodinSparseInverseStep

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseRecodingRec_step {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (ih : ∀ i ∈ θ, IsWoodinSparseRow i (woodinSparseRecodingRec i)) :
    IsWoodinSparseRow θ (woodinSparseRecodingRec θ) := by
  classical
  rw [woodinSparseRecodingRec_rule]
  unfold woodinSparseRecodingRule
  by_cases hz : θ = ∅
  · subst θ
    simp only [woodinSparseRecodingRowRule, ite_true]
    exact woodinSparseInitialRow_correct hΩ
  by_cases hsucc : θ = succ (⋃ˢ θ)
  · generalize hk : ⋃ˢ θ = k at hsucc
    subst θ
    let : IsOrdinal k := IsOrdinal.of_mem (mem_succ_self k)
    simp only [woodinSparseRecodingRowRule, ite_eq_right hz, sUnion_succ_of_transitive, ite_true]
    exact woodinSparseSuccessorRow_correct hΩ hAC hθ ih
  by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · simp only [woodinSparseRecodingRowRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_left hinac]
    exact woodinSparseRecodingDirectRow_correct hΩ hAC hθ hz hsucc hinac ih
  · simp only [woodinSparseRecodingRowRule, ite_eq_right hz, ite_eq_right hsucc, ite_eq_right hinac]
    exact woodinSparseRecodingInverseRow_correct hΩ hAC hθ hz hsucc hinac ih

theorem woodinSparseRecodingRec_correct {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ θ ∈ Ω, IsWoodinSparseRow θ (woodinSparseRecodingRec θ) := by
  let := hΩ.inaccessible.1
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ Ω → IsWoodinSparseRow ξ (woodinSparseRecodingRec ξ)) (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  apply woodinSparseRecodingRec_step hΩ hAC hθ
  intro i hi
  let := IsOrdinal.of_mem hi
  exact ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)

end ZFVP
