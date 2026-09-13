import ZFVP.ModelTheory.ElementaryParameterClosure

/-! Reflecting witnesses in ordered-pair tables into an elementary submodel. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedPairFiberWitnessFormula : SetTheorySemisentence 3 :=
  “b T a. !boundedPairMemberFormula T a b ∧
    ∃ d ∈ b, ∃ r ∈ d, ∃ e ∈ b, ∃ v ∈ e, !boundedKpairFormula b r v”

theorem boundedPairFiberWitnessFormula_bounded : IsBoundedSetFormula boundedPairFiberWitnessFormula :=
  .and (boundedPairMemberFormula_bounded.subst _)
    (.exs (.bvar 0) (.exs (.bvar 0) (.exs (.bvar 2) (.exs (.bvar 0)
      (boundedKpairFormula_bounded.subst _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion
variable {X B : V} (h : IsElementaryInclusion X B) [IsTransitive B]

include h in
theorem kpair_mem {a b : V} (ha : a ∈ X) (hb : b ∈ X) (hp : ⟨a, b⟩ₖ ∈ B) :
    ⟨a, b⟩ₖ ∈ X := by
  obtain ⟨p, hpX, he⟩ := h.bounded_witness boundedKpairFormula_bounded
    ![a, b] (by simp [ha, hb]) ⟨⟨a, b⟩ₖ, hp, by simp⟩
  have heq : p = ⟨a, b⟩ₖ := by simpa using he
  exact heq ▸ hpX

include h in
theorem table_fiber_witness {T a : V} (hT : T ∈ X) (ha : a ∈ X)
    (hex : ∃ b, ⟨a, b⟩ₖ ∈ T) : ∃ b ∈ X, ⟨a, b⟩ₖ ∈ T := by
  obtain ⟨b, hb⟩ := hex
  have hbB := (kpair_components_mem_transitive
    ((inferInstance : IsTransitive B).mem_trans hb (h.subset _ hT))).2
  obtain ⟨c, hc, he⟩ := h.bounded_witness
    (boundedPairMemberFormula_bounded.subst ![.bvar 1, .bvar 2, .bvar 0])
    ![T, a] (by simp [hT, ha]) ⟨b, hbB, by simpa using hb⟩
  exact ⟨c, hc, by simpa using he⟩

include h in
theorem table_pair_fiber_witness {T a : V} (hT : T ∈ X) (ha : a ∈ X)
    (hex : ∃ r v, ⟨a, ⟨r, v⟩ₖ⟩ₖ ∈ T) :
    ∃ r ∈ X, ∃ v ∈ X, ⟨a, ⟨r, v⟩ₖ⟩ₖ ∈ T := by
  obtain ⟨r, v, hrv⟩ := hex
  have hpB := (kpair_components_mem_transitive
    ((inferInstance : IsTransitive B).mem_trans hrv (h.subset _ hT))).2
  have heval : boundedPairFiberWitnessFormula.Evalb ![⟨r, v⟩ₖ, T, a] := by
    simp [boundedPairFiberWitnessFormula, hrv]
    exact ⟨doubleton r v, by simp [kpair, pair_eq_doubleton], by simp,
      doubleton r v, by simp [kpair, pair_eq_doubleton], by simp⟩
  obtain ⟨p, hp, hep⟩ := h.bounded_witness boundedPairFiberWitnessFormula_bounded
    ![T, a] (by simp [hT, ha]) ⟨⟨r, v⟩ₖ, hpB, heval⟩
  have hparts : ⟨a, p⟩ₖ ∈ T ∧
      ∃ d ∈ p, ∃ r ∈ d, ∃ e ∈ p, ∃ v ∈ e, p = ⟨r, v⟩ₖ := by
    simpa [boundedPairFiberWitnessFormula] using hep
  obtain ⟨_, _, r', _, _, _, v', _, rfl⟩ := hparts.2
  have hmem := h.kpair_components_mem hp
  exact ⟨r', hmem.1, v', hmem.2, hparts.1⟩

end IsElementaryInclusion
end ZFVP
