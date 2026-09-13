import ZFVP.SetTheory.BoundedDomainFormula
import ZFVP.SetTheory.DeltaOneForcingNames
import ZFVP.ModelTheory.SuccessorRankSyntaxFamily
import ZFVP.ModelTheory.LimitRankEmbedding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedLowNameSetFormula : SetTheorySemisentence 3 :=
  “U P D. !isSubsetOf D U ∧ ∀ τ ∈ U, τ ∈ D ↔ !(boundedDomainFormula piOneForcingNameFormula) P τ U”

theorem boundedLowNameSetFormula_bounded : IsBoundedSetFormula boundedLowNameSetFormula :=
  .and (isSubsetOf_bounded.subst _) (.all (.bvar 0)
    ((IsBoundedSetFormula.rel _ _).iff ((boundedDomainFormula_bounded piOneForcingNameFormula).subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def lowRankNameSet (P δ : V) : V := {τ ∈ hierarchy δ ; IsForcingName P τ}

theorem mem_lowRankNameSet (P δ τ : V) : τ ∈ lowRankNameSet P δ ↔
    τ ∈ hierarchy δ ∧ IsForcingName P τ := by simp [lowRankNameSet]

theorem lowRankNameSet_subset (P δ : V) : lowRankNameSet P δ ⊆ hierarchy δ := sep_subset

theorem eval_boundedLowNameSetFormula {δ P : V} (hδ : Cn 1 δ) (hP : P ∈ hierarchy δ) (D : V) :
    boundedLowNameSetFormula.Evalb ![hierarchy δ, P, D] ↔ D = lowRankNameSet P δ := by
  have hev {τ : V} (hτ : τ ∈ hierarchy δ) :
      (boundedDomainFormula piOneForcingNameFormula).Evalb ![P, τ, hierarchy δ] ↔ IsForcingName P τ := by
    rw [eval_boundedDomainFormula_two (hierarchy δ) piOneForcingNameFormula
      (⟨P, hP⟩ : SetDomain (hierarchy δ)) (⟨τ, hτ⟩ : SetDomain (hierarchy δ))]
    exact hδ.defined_correct piOneForcingNameFormula_piOne (fun v ↦ IsForcingName (v 0) (v 1)) _
  simp [boundedLowNameSetFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  constructor
  · rintro ⟨hs, he⟩
    apply mem_ext
    intro τ
    rw [mem_lowRankNameSet]
    exact ⟨fun ht ↦ ⟨hs τ ht, (hev (hs τ ht)).mp ((he τ (hs τ ht)).mp ht)⟩,
      fun ⟨hτ, ht⟩ ↦ (he τ hτ).mpr ((hev hτ).mpr ht)⟩
  · rintro rfl
    refine ⟨lowRankNameSet_subset P δ, fun τ hτ ↦ ?_⟩
    rw [mem_lowRankNameSet, and_iff_right hτ]
    exact (hev hτ).symm

theorem successorRankEmbedding_value_lowRankNameSet {δ ε f P : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) f)
    (hP : P ∈ hierarchy δ) : f ‘ (lowRankNameSet P δ) = lowRankNameSet (f ‘ P) ε := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hierarchy_transitive (succ δ)
  let := hierarchy_transitive (succ ε)
  have hU : hierarchy δ ∈ hierarchy (succ δ) := by rw [hierarchy_succ, mem_power_iff]
  have hPs := (hierarchy_transitive (succ δ)).mem_trans hP hU
  have hD : lowRankNameSet P δ ∈ hierarchy (succ δ) := by
    simpa only [hierarchy_succ, mem_power_iff] using lowRankNameSet_subset P δ
  have ht := (he.bounded_formula_iff boundedLowNameSetFormula_bounded
    ![hierarchy δ, P, lowRankNameSet P δ] (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hU, hPs, hD])).mp
      ((eval_boundedLowNameSetFormula hδ hP _).mpr rfl)
  have hv : (fun i ↦ f ‘ (![hierarchy δ, P, lowRankNameSet P δ] i)) =
      ![f ‘ (hierarchy δ), f ‘ P, f ‘ (lowRankNameSet P δ)] := by
    funext i
    repeat' first | exact rfl | exact Fin.elim0 i | (refine Fin.cases ?_ (fun i ↦ ?_) i)
  rw [hv, successorRankEmbedding_value_hierarchy he] at ht
  exact (eval_boundedLowNameSetFormula hε (successorRankElementaryMap he ⟨P, hP⟩).property _).mp ht

end ZFVP
