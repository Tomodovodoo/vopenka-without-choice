import ZFVP.SetTheory.ForcingNameFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingNameFamily_containing {P X : V} (hX : ∀ τ ∈ X, IsForcingName P τ) :
    ∃ D : V, IsForcingNameFamily P D ∧ IsNonempty D ∧ X ⊆ D := by
  let T : V := transitiveClosure ({X, ∅} : V)
  have hT : IsTransitive T := transitiveClosure_transitive _
  have hXT : X ∈ T := subset_transitiveClosure _ _ (by simp)
  have h0T : (∅ : V) ∈ T := subset_transitiveClosure _ _ (by simp)
  refine ⟨{τ ∈ T ; IsForcingName P τ}, forcingNameFamily_transitive_part P T hT,
    ⟨∅, mem_sep_iff.mpr ⟨h0T, empty_forcingName P⟩⟩, ?_⟩
  intro τ hτ
  exact mem_sep_iff.mpr ⟨hT.mem_trans hτ hXT, hX τ hτ⟩

theorem nameSequence_family_with_witness {P n b τ : V} [IsFunction b]
    (hs : IsNameSequence P b) (hd : domain b = n) (hτ : IsForcingName P τ) :
    ∃ D : V, IsForcingNameFamily P D ∧ IsNonempty D ∧ b ∈ D ^ n ∧ τ ∈ D := by
  have hX : ∀ σ ∈ insert τ (range b), IsForcingName P σ := by
    intro σ hσ
    rcases (show σ = τ ∨ σ ∈ range b from by simpa using hσ) with rfl | hσ
    · exact hτ
    · obtain ⟨i, hi⟩ := mem_range_iff.mp hσ
      exact (value_eq_of_kpair_mem hi) ▸ hs i (mem_domain_of_kpair_mem hi)
  obtain ⟨D, hD, hne, hXD⟩ := forcingNameFamily_containing hX
  refine ⟨D, hD, hne, ?_, hXD τ (by simp)⟩
  rw [← hd]
  exact mem_function_of_mem_function_of_subset (IsFunction.mem_function b)
    (fun σ hσ ↦ hXD σ (by simp [hσ]))

end ZFVP
