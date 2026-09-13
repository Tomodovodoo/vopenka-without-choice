import ZFVP.SetTheory.FiniteSets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A definable family closed under binary intersections has a least member whenever it
contains one internally finite member. Internal induction includes nonstandard finite sets. -/
theorem finite_intersection_minimum (R : V → Prop) (hR : ℒₛₑₜ-predicate R)
    (hex : ∃ D, R D ∧ IsInternallyFinite D)
    (hinter : ∀ E F, R E → R F → R (E ∩ F)) :
    ∃ E, R E ∧ ∀ F, R F → E ⊆ F := by
  classical
  obtain ⟨D, hD, hDf⟩ := hex
  have key : ∀ A : V, IsInternallyFinite A →
      ∃ E, R E ∧ E ⊆ D ∧
        ∀ i ∈ A, i ∈ E → ∀ F, R F → i ∈ F := by
    apply internallyFinite_induction (fun A ↦
      ∃ E, R E ∧ E ⊆ D ∧
        ∀ i ∈ A, i ∈ E → ∀ F, R F → i ∈ F) (by definability)
    · exact ⟨D, hD, subset_refl D, fun i hi ↦ (not_mem_empty hi).elim⟩
    · intro A a ih
      obtain ⟨E, hE, hED, hmin⟩ := ih
      by_cases hall : ∀ F, R F → a ∈ F
      · refine ⟨E, hE, hED, ?_⟩
        intro i hi hiE F hF
        rcases mem_insert.mp hi with rfl | hi
        · exact hall F hF
        · exact hmin i hi hiE F hF
      · push Not at hall
        obtain ⟨F, hF, haF⟩ := hall
        refine ⟨E ∩ F, hinter E F hE hF,
          fun i hi ↦ hED i (mem_inter_iff.mp hi).1, ?_⟩
        intro i hi hiEF K hK
        rcases mem_insert.mp hi with rfl | hi
        · exact (haF (mem_inter_iff.mp hiEF).2).elim
        · exact hmin i hi (mem_inter_iff.mp hiEF).1 K hK
  obtain ⟨E, hE, hED, hmin⟩ := key D hDf
  exact ⟨E, hE, fun F hF i hi ↦ hmin i (hED i hi) hi F hF⟩

end ZFVP
