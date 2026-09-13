import ZFVP.ModelTheory.ElementaryBoundedWitness

/-! Parameter and finite-pair closure for elementary submodels of transitive sets. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedPairFirstWitnessFormula : SetTheorySemisentence 2 :=
  “x p. ∃ d ∈ p, ∃ y ∈ d, !boundedKpairFormula p x y”

def boundedPairSecondWitnessFormula : SetTheorySemisentence 2 :=
  “y p. ∃ d ∈ p, ∃ x ∈ d, !boundedKpairFormula p x y”

theorem boundedPairFirstWitnessFormula_bounded : IsBoundedSetFormula boundedPairFirstWitnessFormula :=
  .exs (.bvar 1) (.exs (.bvar 0) (boundedKpairFormula_bounded.subst _))

theorem boundedPairSecondWitnessFormula_bounded : IsBoundedSetFormula boundedPairSecondWitnessFormula :=
  .exs (.bvar 1) (.exs (.bvar 0) (boundedKpairFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion
variable {X B : V} (h : IsElementaryInclusion X B) [IsTransitive B]

include h in
theorem kpair_components_mem {x y : V} (hp : ⟨x, y⟩ₖ ∈ X) : x ∈ X ∧ y ∈ X := by
  obtain ⟨hxB, hyB⟩ := kpair_components_mem_transitive (h.subset _ hp)
  have hfirst : boundedPairFirstWitnessFormula.Evalb ![x, ⟨x, y⟩ₖ] := by
    simp [boundedPairFirstWitnessFormula]
    exact ⟨doubleton x y, by simp [kpair, pair_eq_doubleton], by simp⟩
  have hsecond : boundedPairSecondWitnessFormula.Evalb ![y, ⟨x, y⟩ₖ] := by
    simp [boundedPairSecondWitnessFormula]
    exact ⟨doubleton x y, by simp [kpair, pair_eq_doubleton], by simp⟩
  obtain ⟨u, hu, he⟩ := h.bounded_witness boundedPairFirstWitnessFormula_bounded
    ![⟨x, y⟩ₖ] (by simpa using hp) ⟨x, hxB, hfirst⟩
  obtain ⟨v, hv, he'⟩ := h.bounded_witness boundedPairSecondWitnessFormula_bounded
    ![⟨x, y⟩ₖ] (by simpa using hp) ⟨y, hyB, hsecond⟩
  have hu' : u = x := by
    have hh : ∃ d ∈ ⟨x, y⟩ₖ, y ∈ d ∧ x = u := by
      simpa [boundedPairFirstWitnessFormula] using he
    obtain ⟨_, _, _, hh⟩ := hh
    exact hh.symm
  have hv' : v = y := by
    have hh : ∃ d ∈ ⟨x, y⟩ₖ, x ∈ d ∧ y = v := by
      simpa [boundedPairSecondWitnessFormula] using he'
    obtain ⟨_, _, _, hh⟩ := hh
    exact hh.symm
  exact ⟨hu' ▸ hu, hv' ▸ hv⟩

include h in
theorem nonempty_inter_member {A : V} (hA : A ∈ X) (hne : IsNonempty A) : IsNonempty (A ∩ X) := by
  obtain ⟨x, hx⟩ := hne.nonempty
  have hxB := (inferInstance : IsTransitive B).mem_trans hx (h.subset _ hA)
  obtain ⟨y, hy, he⟩ := h.bounded_witness
    (φ := “x A. x ∈ A”) (.rel _ _) ![A] (by simpa using hA) ⟨x, hxB, by simpa using hx⟩
  exact ⟨y, mem_inter_iff.mpr ⟨by simpa using he, hy⟩⟩

end IsElementaryInclusion
end ZFVP

