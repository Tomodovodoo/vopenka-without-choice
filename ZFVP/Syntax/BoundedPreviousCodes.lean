import ZFVP.Syntax.BoundedAtomicDefinition

/-! Bounded lookup of a previously derived formula in a sequence certificate. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedPreviousValueFormula : SetTheorySemisentence 3 :=
  “s i q. ∃ j ∈ i, !boundedPairMemberFormula s j q”

def boundedPreviousCodeFormula : SetTheorySemisentence 5 :=
  “U s i n φ. ∃ q ∈ U, !boundedKpairFormula q n φ ∧ !boundedPreviousValueFormula s i q”

theorem boundedPreviousValueFormula_bounded : IsBoundedSetFormula boundedPreviousValueFormula :=
  .exs (.bvar 1) (boundedPairMemberFormula_bounded.subst _)

theorem boundedPreviousCodeFormula_bounded : IsBoundedSetFormula boundedPreviousCodeFormula :=
  .exs (.bvar 0) (.and (boundedKpairFormula_bounded.subst _) (boundedPreviousValueFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedPreviousValueFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun s i q : V ↦ q ∈ range (s ↾ i)) via boundedPreviousValueFormula :=
  ⟨fun v ↦ by simp [boundedPreviousValueFormula, mem_range_iff, and_comm]⟩

theorem eval_boundedPreviousCodeFormula {U : V} [hU : IsCodingSupport U]
    (s i : V) {n φ : V} (hn : n ∈ U) (hφ : φ ∈ U) :
    boundedPreviousCodeFormula.Evalb ![U, s, i, n, φ] ↔ ⟨n, φ⟩ₖ ∈ range (s ↾ i) := by
  simp [boundedPreviousCodeFormula, hU.kpair_closed n hn φ hφ]

theorem range_subset_codingSupport {U s : V} [hU : IsCodingSupport U] (hs : s ∈ U) : range s ⊆ U := by
  intro q hq
  obtain ⟨j, hj⟩ := mem_range_iff.mp hq
  exact (kpair_components_mem_transitive (hU.mem_trans hj hs)).2

theorem previousCode_components_mem {U s i n φ : V} [IsCodingSupport U] (hs : s ∈ U)
    (hp : ⟨n, φ⟩ₖ ∈ range (s ↾ i)) : n ∈ U ∧ φ ∈ U := by
  obtain ⟨j, hj⟩ := mem_range_iff.mp hp
  exact kpair_components_mem_transitive
    (range_subset_codingSupport hs _ (mem_range_of_kpair_mem (kpair_mem_restrict_iff.mp hj).1))

end ZFVP
