import ZFVP.SetTheory.RankWitnessStructures
import ZFVP.SetTheory.BoundedOrdinalOmega
import ZFVP.SetTheory.BoundedUnion
import ZFVP.SetTheory.DeltaOneRank

/-! A Pi-one graph for the rank bound used in the fragment construction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneWitnessRankBoundFormula : SetTheorySemisentence 4 :=
  “b ρ α e. !IsOrdinal.dfn ρ ∧ !IsOrdinal.dfn α ∧ ∃ r ∈ b, ∃ s ∈ b, ∃ t ∈ b,
    !piOneRankFormula r e ∧ !boundedUnionFormula s ρ α ∧ !boundedUnionFormula t s r ∧
    !boundedOrdinalOmegaFormula b t”

theorem piOneWitnessRankBoundFormula_piOne : IsPiFormula 1 piOneWitnessRankBoundFormula := by
  refine .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.bounded (isOrdinalFormula_bounded.subst _)) ?_)
  refine .boundedExs (.bvar 0) (.boundedExs (.bvar 1) (.boundedExs (.bvar 2) ?_))
  exact .and (piOneRankFormula_piOne.subst _) (.and (.bounded (boundedUnionFormula_bounded.subst _))
    (.and (.bounded (boundedUnionFormula_bounded.subst _)) (.bounded (boundedOrdinalOmegaFormula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_piOneWitnessRankBoundFormula (b ρ α e : V) :
    piOneWitnessRankBoundFormula.Evalb ![b, ρ, α, e] ↔
      IsOrdinal ρ ∧ IsOrdinal α ∧ b = witnessRankBound ρ α e := by
  simp [piOneWitnessRankBoundFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, eval_boundedOrdinalOmegaFormula]
  intro hρ hα
  let := hρ
  let := hα
  let := ordinal_union_ordinal ρ α
  let := ordinal_union_ordinal (ρ ∪ α) (rank e)
  constructor
  · rintro ⟨_, _, _, _, he⟩
    exact he
  · rintro rfl
    have ht : (ρ ∪ α) ∪ rank e ∈ witnessRankBound ρ α e := ordinalAdd_omega_gt _
    have hs : ρ ∪ α ∈ witnessRankBound ρ α e := by
      rcases IsOrdinal.subset_iff.mp (show ρ ∪ α ⊆ (ρ ∪ α) ∪ rank e from
        fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) with he | he
      · exact he ▸ ht
      · exact IsOrdinal.toIsTransitive.mem_trans he ht
    exact ⟨(witnessRankBound_above ρ α e).2.2, hs, ht, inferInstance, rfl⟩

end ZFVP
