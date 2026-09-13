import ZFVP.ModelTheory.ForcingFiniteFunctions
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.InjectionRetraction

/-! Closure at the ground model's internal omega preserves its omega-one
in the actual forcing quotient. The sequence theorem used below constructs
an internal descending decision sequence through every member of omega,
using internal dependent choice, then applies an internal closure bound. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Exact closure at internal omega supplies all shorter ordinal closure
instances. Finite closure also covers nonstandard members of omega. -/
theorem forcingClosedAt_through_omega {P R one : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hclosed : IsForcingClosedAt P R (ω : V)) :
    ∀ α, IsOrdinal α → α ⊆ (ω : V) → IsForcingClosedAt P R α := by
  intro α hα hαω
  let : IsOrdinal α := hα
  rcases IsOrdinal.subset_iff.mp hαω with rfl | hmem
  · exact hclosed
  · exact forcingClosedAt_finite hR htop hmem

namespace ForcingContext

/-- Every sequence indexed by the extension's full internal omega, with
values in a checked ground set, is itself a checked ground sequence. -/
theorem function_eq_check_of_internalOmegaClosed (F : ForcingContext V)
    (hDC : InternalDependentChoiceAt (ω : V))
    (hclosed : IsForcingClosedAt F.P F.R (ω : V)) {X : V} {f : F.Model}
    (hf : f ∈ F.check X ^ (ω : F.Model)) : ∃ g ∈ X ^ (ω : V), F.check g = f := by
  apply F.function_eq_check_of_closed hDC
    (forcingClosedAt_through_omega F.order F.top hclosed)
  simpa only [show F.check (ω : V) = (ω : F.Model) from F.checkEmbedding.map_omega] using hf

/-- Internal omega closure preserves and reflects countability of every
checked ground set, without external countability assumptions on the model. -/
theorem check_countable_iff_of_internalOmegaClosed (F : ForcingContext V)
    (hDC : InternalDependentChoiceAt (ω : V))
    (hclosed : IsForcingClosedAt F.P F.R (ω : V)) (X : V) :
    IsInternallyCountable (F.check X) ↔ IsInternallyCountable X := by
  constructor
  · intro hcount
    by_cases hne : ∃ x : V, x ∈ X
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨f, hf, hr⟩ := surjection_of_injection hcount
        ⟨F.check x, (F.check_mem_iff x X).mpr hx⟩
      obtain ⟨g, hg, he⟩ := F.function_eq_check_of_internalOmegaClosed hDC hclosed hf
      have hrcheck : F.check (range g) = F.check X := calc
        F.check (range g) = range (F.check g) := F.checkEmbedding.map_range g
        _ = range f := congrArg range he
        _ = F.check X := hr
      exact internallyCountable_of_surjection internallyCountable_omega hg
        ((F.check_eq_iff (range g) X).mp hrcheck)
    · have hX : X = ∅ := SetTheory.subset_antisymm
        (fun x hx ↦ False.elim (hne ⟨x, hx⟩)) (empty_subset _)
      exact hX ▸ internallyCountable_empty
  · intro hcount
    have h := F.checkEmbedding.map_cardLE hcount
    change F.check X ≤# F.check (ω : V) at h
    simpa only [show F.check (ω : V) = (ω : F.Model) from F.checkEmbedding.map_omega,
      IsInternallyCountable] using h

/-- Exact internal omega closure preserves the actual first uncountable
ordinal. Only internal omega-dependent choice is needed in the ground. -/
theorem check_hartogs_omega_of_internalOmegaClosed (F : ForcingContext V)
    (hDC : InternalDependentChoiceAt (ω : V))
    (hclosed : IsForcingClosedAt F.P F.R (ω : V)) :
    F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) := by
  have hnot : ¬IsInternallyCountable (F.check (hartogsNumber (ω : V))) := fun h ↦
    hartogs_omega_not_countable ((F.check_countable_iff_of_internalOmegaClosed hDC hclosed _).mp h)
  have hbelow : ∀ a ∈ F.check (hartogsNumber (ω : V)), IsInternallyCountable a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (F.mem_check_iff _ a).mp ha
    exact (F.check_countable_iff_of_internalOmegaClosed hDC hclosed b).mpr
      (countable_of_mem_hartogs_omega hb)
  symm
  rw [hartogsNumber_eq_iff]
  refine ⟨inferInstance, hnot, ?_⟩
  intro β hβ hβnot
  let : IsOrdinal β := hβ
  by_contra hsub
  have hβsub : β ⊆ F.check (hartogsNumber (ω : V)) :=
    (IsOrdinal.subset_or_supset _ _).resolve_left hsub
  rcases IsOrdinal.subset_iff.mp hβsub with he | hmem
  · exact hsub (he ▸ subset_refl _)
  · exact hβnot (hbelow β hmem)

theorem check_hartogs_omega_of_internalOmegaClosed_choice (F : ForcingContext V)
    (hAC : InternalChoice V) (hclosed : IsForcingClosedAt F.P F.R (ω : V)) :
    F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) :=
  F.check_hartogs_omega_of_internalOmegaClosed (dependentChoiceAt_of_internalChoice hAC _) hclosed

end ForcingContext
end ZFVP
