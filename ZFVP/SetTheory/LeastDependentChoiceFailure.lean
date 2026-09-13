import ZFVP.SetTheory.OrdinalDependentChoiceAC
import ZFVP.SetTheory.OrdinalDependentChoiceFunctions
import ZFVP.SetTheory.PathDependentChoice

/-! Finite dependent choice and the least ordinal at which it fails. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem InternalDependentChoiceAt.succ {γ : V} [IsOrdinal γ]
    (hγ : InternalDependentChoiceAt γ) : InternalDependentChoiceAt (succ γ) := by
  intro A R hA hR
  have hserial : ∀ s ∈ shorterSequences γ A, ∃ x ∈ A, ⟨s, x⟩ₖ ∈ R := by
    intro s hs
    obtain ⟨β, hβ, hsf⟩ := (mem_shorterSequences _ _ _).mp hs
    exact hR s ((mem_shorterSequences _ _ _).mpr
      ⟨β, mem_succ_iff.mpr (Or.inr hβ), hsf⟩)
  obtain ⟨f, hf, hstep⟩ := hγ A R hA hserial
  obtain ⟨x, hx, hfx⟩ := hR f ((mem_shorterSequences _ _ _).mpr ⟨γ, by simp, hf⟩)
  refine ⟨insert ⟨γ, x⟩ₖ f, function_append_mem hf hx, ?_⟩
  intro β hβ
  rcases mem_succ_iff.mp hβ with rfl | hβ
  · rwa [function_append_restrict hf, function_append_value_new hf hx]
  · have hnot : γ ∉ β := fun hγβ ↦ mem_irrefl γ
      (IsOrdinal.toIsTransitive.mem_trans hγβ hβ)
    rw [restrict_insert_kpair_eq_restrict_of_not_mem hnot, function_append_value_old hf hx hβ]
    exact hstep β hβ

theorem dependentChoiceAt_finite (n : V) (hn : n ∈ (ω : V)) : InternalDependentChoiceAt n := by
  apply naturalNumber_induction InternalDependentChoiceAt (by definability) dependentChoiceAt_zero
    (fun m hm h ↦ ?_) n hn
  let := IsOrdinal.of_mem hm
  exact h.succ

def IsLeastDependentChoiceFailure (κ : V) : Prop :=
  IsLeastOrdinal (fun γ ↦ ¬InternalDependentChoiceAt γ) κ

instance leastDependentChoiceFailure_definable : ℒₛₑₜ-predicate[V] IsLeastDependentChoiceFailure := by
  unfold IsLeastDependentChoiceFailure IsLeastOrdinal
  definability

theorem leastDependentChoiceFailure_existsUnique (hAC : ¬InternalChoice V) :
    ∃! κ : V, IsLeastDependentChoiceFailure κ := by
  apply leastOrdinal_existsUnique _ (by definability)
  by_contra hn
  apply hAC
  apply internalChoice_of_all_dependentChoiceAt
  intro γ hγ
  by_contra hbad
  exact hn ⟨γ, hγ, hbad⟩

theorem IsLeastDependentChoiceFailure.below {κ : V} (hκ : IsLeastDependentChoiceFailure κ)
    {α : V} (hα : α ∈ κ) : InternalDependentChoiceAt α := by
  let := hκ.1
  let := IsOrdinal.of_mem hα
  by_contra hn
  exact mem_irrefl α (hκ.2.2 α inferInstance hn α hα)

theorem IsLeastDependentChoiceFailure.omega_subset {κ : V} (hκ : IsLeastDependentChoiceFailure κ) :
    (ω : V) ⊆ κ := by
  let := hκ.1
  rcases IsOrdinal.mem_trichotomy (ω : V) κ with h | rfl | h
  · exact IsOrdinal.toIsTransitive.transitive _ h
  · exact subset_refl _
  · exact False.elim (hκ.2.1 (dependentChoiceAt_finite κ h))

theorem IsLeastDependentChoiceFailure.successor_closed {κ : V} (hκ : IsLeastDependentChoiceFailure κ) :
    ∀ α ∈ κ, succ α ∈ κ := by
  let := hκ.1
  intro α hα
  let := IsOrdinal.of_mem hα
  rcases IsOrdinal.mem_trichotomy (succ α) κ with h | he | h
  · exact h
  · exact False.elim (hκ.2.1 (he ▸ (hκ.below hα).succ))
  · rcases mem_succ_iff.mp h with he | h
    · exact False.elim (mem_irrefl α (he ▸ hα))
    · exact False.elim (mem_irrefl κ (IsOrdinal.toIsTransitive.mem_trans h hα))

end ZFVP
