import ZFVP.ModelTheory.SchmerlInternalCCCPreservationValues
import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.SetTheory.HartogsRegularChoice
import ZFVP.SetTheory.EndExtensionFinite
import ZFVP.SetTheory.InjectionRetraction

/-! Internal ccc preserves omega-one in the actual forcing quotient.
Internal antichains bound each possible-value set; internal countable union
and ground Hartogs regularity give a common ordinal bound. Quotient truth
then bounds every function with domain the extension's internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace Schmerl

/-- A bound in the ground model for every possible value of the name over
its internal omega, uniform over all generics for this forcing. -/
theorem checkedPossibleOmegaRange_bounded (hAC : InternalChoice V)
    {P R one τ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hccc : IsInternallyCCC P R) :
    ∃ β ∈ hartogsNumber (ω : V),
      checkedPossibleOmegaRange P R one τ (hartogsNumber (ω : V)) ⊆ β :=
  regular_small_subset_bounded (hartogsNumber_regular hAC (CardLE.refl (ω : V)))
    (checkedPossibleOmegaRange_subset _ _ _ _ _) omega_mem_hartogs_omega
    (checkedPossibleOmegaRange_countable hAC hR htop hτ hccc _)

end Schmerl

namespace ForcingContext

open Schmerl

/-- Every omega-sequence of checked countable ordinals in the actual quotient
has a bound below the checked ground omega-one. -/
theorem function_values_bounded_of_internalCCC (S : ForcingContext V)
    (hAC : InternalChoice V) (hccc : IsInternallyCCC S.P S.R)
    {f : S.Model} (hf : f ∈ S.check (hartogsNumber (ω : V)) ^ (ω : S.Model)) :
    ∃ β ∈ hartogsNumber (ω : V), ∀ a ∈ (ω : S.Model), f ‘ a ∈ S.check β := by
  obtain ⟨τ, rfl⟩ := S.ofName_surjective f
  obtain ⟨β, hβ, hb⟩ := checkedPossibleOmegaRange_bounded hAC S.order S.top τ.property hccc
  refine ⟨β, hβ, ?_⟩
  intro a ha
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  obtain ⟨n, hn, rfl⟩ := (S.mem_check_iff (ω : V) a).mp (hω.symm ▸ ha)
  let : IsFunction (S.ofName τ) := IsFunction.of_mem hf
  have hnω : S.check n ∈ (ω : S.Model) := hω ▸ (S.check_mem_iff _ _).mpr hn
  obtain ⟨x, hx, he⟩ := (S.mem_check_iff (hartogsNumber (ω : V)) _).mp
    (function_value_mem hf hnω)
  obtain ⟨p, hpG, hpx⟩ := (S.checkedFunctionValue_truth τ n x).mpr ⟨inferInstance, he⟩
  have hxrange : x ∈ checkedPossibleOmegaRange S.P S.R S.one τ.val (hartogsNumber (ω : V)) :=
    (mem_checkedPossibleOmegaRange _ _ _ _ _ _).mpr ⟨n, hn,
      (mem_checkedPossibleValues _ _ _ _ _ _ _).mpr ⟨hx, p, S.generic.1.1 p hpG, hpx⟩⟩
  exact he ▸ (S.check_mem_iff x β).mpr (hb x hxrange)

/-- There is no internal countable cofinal map into the checked ground omega-one. -/
theorem no_cofinal_omega_map_of_internalCCC (S : ForcingContext V)
    (hAC : InternalChoice V) (hccc : IsInternallyCCC S.P S.R) (f : S.Model) :
    ¬IsCofinalMap (S.check (hartogsNumber (ω : V))) (ω : S.Model) f := by
  intro hf
  obtain ⟨β, hβ, hb⟩ := S.function_values_bounded_of_internalCCC hAC hccc hf.1
  obtain ⟨a, ha, hβa⟩ := hf.2 (S.check β) ((S.check_mem_iff _ _).mpr hβ)
  exact mem_irrefl (f ‘ a) (hβa _ (hb a ha))

/-- The checked ground omega-one cannot become internally countable. -/
theorem check_hartogs_omega_not_countable_of_internalCCC (S : ForcingContext V)
    (hAC : InternalChoice V) (hccc : IsInternallyCCC S.P S.R) :
    ¬IsInternallyCountable (S.check (hartogsNumber (ω : V))) := by
  intro hcount
  have hzero : (∅ : V) ∈ hartogsNumber (ω : V) :=
    IsOrdinal.toIsTransitive.transitive _ omega_mem_hartogs_omega _ empty_mem_ω
  obtain ⟨f, hf, hr⟩ := surjection_of_injection hcount
    ⟨S.check ∅, (S.check_mem_iff _ _).mpr hzero⟩
  let : IsFunction f := IsFunction.of_mem hf
  apply S.no_cofinal_omega_map_of_internalCCC hAC hccc f
  refine ⟨hf, fun ξ hξ ↦ ?_⟩
  obtain ⟨a, haξ⟩ := mem_range_iff.mp (hr.symm ▸ hξ)
  refine ⟨a, domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem haξ, ?_⟩
  rw [value_eq_of_kpair_mem haξ]

/-- The actual forcing extension and its ground model have the same omega-one. -/
theorem check_hartogs_omega_of_internalCCC (S : ForcingContext V)
    (hAC : InternalChoice V) (hccc : IsInternallyCCC S.P S.R) :
    S.check (hartogsNumber (ω : V)) = hartogsNumber (ω : S.Model) := by
  have hbelow : ∀ a ∈ S.check (hartogsNumber (ω : V)), IsInternallyCountable a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (S.mem_check_iff _ a).mp ha
    have h := S.checkEmbedding.map_cardLE (countable_of_mem_hartogs_omega hb)
    change S.check b ≤# S.check (ω : V) at h
    simpa only [show S.check (ω : V) = (ω : S.Model) from S.checkEmbedding.map_omega,
      IsInternallyCountable] using h
  symm
  rw [hartogsNumber_eq_iff]
  refine ⟨inferInstance, S.check_hartogs_omega_not_countable_of_internalCCC hAC hccc, ?_⟩
  intro β hβ hnot
  let : IsOrdinal β := hβ
  by_contra hsub
  have hβsub : β ⊆ S.check (hartogsNumber (ω : V)) :=
    (IsOrdinal.subset_or_supset _ _).resolve_left hsub
  rcases IsOrdinal.subset_iff.mp hβsub with he | hmem
  · exact hsub (he ▸ subset_refl _)
  · exact hnot (hbelow β hmem)

end ForcingContext
end ZFVP
