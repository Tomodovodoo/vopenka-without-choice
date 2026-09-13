import ZFVP.SetTheory.WoodinDependentChoiceFailure
import ZFVP.SetTheory.LeastOrdinalChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinLeastDCFailure : V :=
  leastOrdinalOrZero (fun (_ : V) γ ↦ ¬InternalDependentChoiceAt γ) (by definability) ∅

/-- The source selection under failure of Choice. The omega fallback totalizes
the auxiliary restored-stage constructors when there is no DC failure. -/
noncomputable def woodinSeedCardinal : V := by
  classical
  exact if (woodinLeastDCFailure : V) = ∅ then ω else woodinLeastDCFailure

theorem woodinLeastDCFailure_spec (hAC : ¬InternalChoice V) :
    IsLeastDependentChoiceFailure (woodinLeastDCFailure : V) := by
  obtain ⟨κ, hκ, _⟩ := leastDependentChoiceFailure_existsUnique hAC
  exact leastOrdinalOrZero_spec _ (by definability) ∅ ⟨κ, hκ.1, hκ.2.1⟩

theorem woodinSeedCardinal_spec (hAC : ¬InternalChoice V) :
    IsLeastDependentChoiceFailure (woodinSeedCardinal : V) := by
  have h := woodinLeastDCFailure_spec hAC
  have hn : (woodinLeastDCFailure : V) ≠ ∅ := by
    intro he
    exact h.2.1 (he.symm ▸ dependentChoiceAt_zero)
  simpa only [woodinSeedCardinal, ite_eq_right hn] using h

theorem woodinSeedCardinal_cases :
    (woodinSeedCardinal : V) = ω ∨ IsLeastDependentChoiceFailure (woodinSeedCardinal : V) := by
  classical
  by_cases hz : (woodinLeastDCFailure : V) = ∅
  · exact Or.inl (by simp only [woodinSeedCardinal, ite_eq_left hz])
  · right
    have he := (leastOrdinalOrZero_eq_iff
      (fun (_ : V) γ ↦ ¬InternalDependentChoiceAt γ) (by definability) (∅ : V) woodinLeastDCFailure).mp rfl
    have h := he.resolve_right (fun h ↦ hz h.2)
    change IsLeastDependentChoiceFailure (woodinLeastDCFailure : V) at h
    simpa only [woodinSeedCardinal, ite_eq_right hz] using h

theorem woodinSeedCardinal_regular : IsRegularCardinal (woodinSeedCardinal : V) := by
  rcases woodinSeedCardinal_cases (V := V) with he | h
  · rw [he]; exact omega_regular
  · exact h.regular

theorem woodinSeedCardinal_DC : ∀ α ∈ (woodinSeedCardinal : V), InternalDependentChoiceAt α := by
  rcases woodinSeedCardinal_cases (V := V) with he | h
  · rw [he]; exact dependentChoiceAt_finite
  · exact fun _ hα ↦ h.below hα

instance woodinSeedCardinal_ordinal : IsOrdinal (woodinSeedCardinal : V) :=
  woodinSeedCardinal_regular.1.1

theorem woodinSeedCardinal_lt {δ : V} (hδ : IsWoodinSupercompact δ) :
    (woodinSeedCardinal : V) ∈ δ := by
  rcases woodinSeedCardinal_cases (V := V) with he | h
  · rw [he]; exact hδ.omega_lt
  · exact h.lt_supercompact hδ

theorem woodinSeedCardinal_omega_subset : (ω : V) ⊆ woodinSeedCardinal := by
  rcases woodinSeedCardinal_cases (V := V) with he | h
  · rw [he]
  · exact h.omega_subset

end ZFVP
