import ZFVP.SetTheory.RankTables

/-! Bounded relational formulas for rank-table equations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedRankStepFormula : SetTheorySemisentence 3 :=
  “R f x. ∃ α ∈ R, !boundedPairMemberFormula f x α ∧ !IsOrdinal.dfn α ∧
    (∀ y ∈ x, ∃ β ∈ R, !boundedPairMemberFormula f y β ∧ β ∈ α) ∧
    ∀ β ∈ α, ∃ y ∈ x, ∃ γ ∈ R, !boundedPairMemberFormula f y γ ∧ !isSubsetOf β γ”

def boundedRankTableFormula : SetTheorySemisentence 3 :=
  “T R f. !boundedFunctionFormula f T R ∧ ∀ x ∈ T, !boundedRankStepFormula R f x”

theorem boundedRankStepFormula_bounded : IsBoundedSetFormula boundedRankStepFormula :=
  .exs (.bvar 0) (.and (boundedPairMemberFormula_bounded.subst _)
    (.and (isOrdinalFormula_bounded.subst _)
      (.and (.all (.bvar 3) (.exs (.bvar 2) (.and (boundedPairMemberFormula_bounded.subst _) (.rel _ _))))
        (.all (.bvar 0) (.exs (.bvar 4) (.exs (.bvar 3)
          (.and (boundedPairMemberFormula_bounded.subst _) (isSubsetOf_bounded.subst _))))))))

theorem boundedRankTableFormula_bounded : IsBoundedSetFormula boundedRankTableFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (.all (.bvar 0) (boundedRankStepFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedRankStepFormula {T R f x : V} [hT : IsTransitive T]
    (hf : f ∈ R ^ T) (hx : x ∈ T) :
    boundedRankStepFormula.Evalb ![R, f, x] ↔
      IsOrdinal (f ‘ x) ∧ (∀ y ∈ x, f ‘ y ∈ f ‘ x) ∧ ∀ β ∈ f ‘ x, ∃ y ∈ x, β ⊆ f ‘ y := by
  let := IsFunction.of_mem hf
  have hxR := function_value_mem hf hx
  have hyT (y : V) (hy : y ∈ x) : y ∈ T := hT.mem_trans hy hx
  have hyR (y : V) (hy : y ∈ x) : f ‘ y ∈ R := function_value_mem hf (hyT y hy)
  simp (config := { contextual := true }) [boundedRankStepFormula, kpair_mem_iff_value, domain_eq_of_mem_function hf, hx, hxR,
    hyT, hyR]
  intro _ _
  exact forall_congr' fun β ↦ imp_congr_right fun _ ↦ exists_congr fun y ↦ and_congr_right fun hy ↦ by
    simp [hyR y hy, hyT y hy]

theorem eval_boundedRankTableFormula {T : V} [IsTransitive T] (R f : V) :
    boundedRankTableFormula.Evalb ![T, R, f] ↔ IsRankTable T R f := by
  simp [boundedRankTableFormula, IsRankTable]
  intro hf
  exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ eval_boundedRankStepFormula hf hx

end ZFVP
