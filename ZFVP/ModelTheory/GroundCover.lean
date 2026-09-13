import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.InverseFunction
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.WellOrderingChoice

/-! The cover property of the ground model: a subset of a checked set of size at most `|P|` in
the extension is covered by the check of a ground set of size at most `|P × P|`, the set of
ordinals that some condition forces to be a value of a name for the inverse enumeration. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The elements of `θ` that some condition forces to be a value of `τ` at a checked condition. -/
def IsForcedValue (P R one τ θ α : V) : Prop :=
  α ∈ θ ∧ ∃ p ∈ P, ∃ q ∈ P, ForcesCheckedFunctionValue P R one τ q p α

instance isForcedValue_definable (P R one τ θ : V) : ℒₛₑₜ-predicate (IsForcedValue P R one τ θ) := by
  unfold IsForcedValue
  definability

/-- The cover property: a subset of `θ̌` of size at most `|P̌|` lies inside the check of a subset
of `θ` of size at most `|P × P|`. -/
theorem ForcingContext.cover (S : ForcingContext V) (hAC : InternalChoice V) (θ : V) {x : S.Model}
    (hx : x ⊆ S.check θ) (hsmall : x ≤# S.check S.P) :
    ∃ y : V, y ⊆ θ ∧ y ≤# S.P ×ˢ S.P ∧ x ⊆ S.check y := by
  obtain ⟨e, he, heinj⟩ := hsmall
  have hef : IsFunction e := IsFunction.of_mem he
  have hconv := converseGraph_mem_function he heinj
  have hgf : IsFunction (converseGraph e) := IsFunction.of_mem hconv
  obtain ⟨τ, hτ⟩ := S.ofName_surjective (converseGraph e)
  let Y : V := sep θ (IsForcedValue S.P S.R S.one τ.val θ) inferInstance
  refine ⟨Y, sep_subset, ?_, ?_⟩
  · -- each forced value is determined by a pair of conditions
    refine cardLE_of_separating_relation (wellOrderable_of_internalChoice hAC _)
      (fun α z ↦ z ∈ S.P ×ˢ S.P ∧ ForcesCheckedFunctionValue S.P S.R S.one τ.val (kpair.π₂ z) (kpair.π₁ z) α)
      (by definability) ?_ ?_
    · intro α hα
      obtain ⟨-, p, hp, q, hq, hf⟩ := (mem_sep_iff.mp hα).2
      refine ⟨⟨p, q⟩ₖ, kpair_mem_iff.mpr ⟨hp, hq⟩, kpair_mem_iff.mpr ⟨hp, hq⟩, ?_⟩
      rw [kpair.π₁_kpair, kpair.π₂_kpair]
      exact hf
    · intro α hα β hβ z hz h1 h2
      exact forcesCheckedFunctionValue_unique S.order S.top τ.property h1.2 h2.2
  · intro z hz
    obtain ⟨α, hα, rfl⟩ := (S.mem_check_iff _ _).mp (hx z hz)
    have hez : e ‘ (S.check α) ∈ S.check S.P := function_value_mem he hz
    obtain ⟨p, hp, hep⟩ := (S.mem_check_iff _ _).mp hez
    have hval : (converseGraph e) ‘ (S.check p) = S.check α := by
      rw [← hep]
      exact converseGraph_value_value he heinj hz
    rw [← hτ] at hval hgf
    obtain ⟨q, hqG, hq⟩ := (S.checkedFunctionValue_truth τ p α).mpr ⟨hgf, hval⟩
    exact (S.check_mem_iff _ _).mpr (mem_sep_iff.mpr ⟨hα, hα, p, hp, q, S.generic.1.1 q hqG, hq⟩)

end ZFVP
