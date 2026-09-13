import ZFVP.ModelTheory.GroundCover
import ZFVP.SetTheory.Hessenberg
import ZFVP.SetTheory.UltrafilterOrdinals

/-! The cover property with an arbitrary checked bounding set: a subset of a checked set that in
the extension has size at most `ν̌` is covered by the check of a ground set of size at most
`ν × (P × P)`. Taking the covered set to be a check gives back a ground bound on the size of a
ground set from the size of its check, and with `ν` an infinite ordinal above `|P|` the bound
collapses to `ν` itself. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The elements of `θ` that some condition forces to be the value of `τ` at some checked
element of `ν`. -/
def IsForcedValueAt (P R one τ ν θ α : V) : Prop :=
  α ∈ θ ∧ ∃ β ∈ ν, ∃ q ∈ P, ForcesCheckedFunctionValue P R one τ q β α

instance isForcedValueAt_definable (P R one τ ν θ : V) :
    ℒₛₑₜ-predicate (IsForcedValueAt P R one τ ν θ) := by
  unfold IsForcedValueAt
  definability

/-- The cover property for an arbitrary checked bound: a subset of `θ̌` of size at most `ν̌` lies
inside the check of a subset of `θ` of size at most `ν × (P × P)`. -/
theorem ForcingContext.cover_of_cardLE (S : ForcingContext V) (hAC : InternalChoice V) (θ ν : V)
    {x : S.Model} (hx : x ⊆ S.check θ) (hsmall : x ≤# S.check ν) :
    ∃ y : V, y ⊆ θ ∧ y ≤# ν ×ˢ (S.P ×ˢ S.P) ∧ x ⊆ S.check y := by
  obtain ⟨e, he, heinj⟩ := hsmall
  have hef : IsFunction e := IsFunction.of_mem he
  have hconv := converseGraph_mem_function he heinj
  have hgf : IsFunction (converseGraph e) := IsFunction.of_mem hconv
  obtain ⟨τ, hτ⟩ := S.ofName_surjective (converseGraph e)
  let Y : V := sep θ (IsForcedValueAt S.P S.R S.one τ.val ν θ) inferInstance
  refine ⟨Y, sep_subset, ?_, ?_⟩
  · -- a forced value is determined by the checked argument and the condition
    refine cardLE_of_separating_relation (wellOrderable_of_internalChoice hAC _)
      (fun α z ↦ z ∈ ν ×ˢ (S.P ×ˢ S.P) ∧ ForcesCheckedFunctionValue S.P S.R S.one τ.val
        (kpair.π₁ (kpair.π₂ z)) (kpair.π₁ z) α)
      (by definability) ?_ ?_
    · intro α hα
      obtain ⟨-, β, hβ, q, hq, hf⟩ := (mem_sep_iff.mp hα).2
      have hmem : (⟨β, ⟨q, q⟩ₖ⟩ₖ : V) ∈ ν ×ˢ (S.P ×ˢ S.P) :=
        kpair_mem_iff.mpr ⟨hβ, kpair_mem_iff.mpr ⟨hq, hq⟩⟩
      refine ⟨⟨β, ⟨q, q⟩ₖ⟩ₖ, hmem, hmem, ?_⟩
      rw [kpair.π₁_kpair, kpair.π₂_kpair, kpair.π₁_kpair]
      exact hf
    · intro α hα β hβ z hz h1 h2
      exact forcesCheckedFunctionValue_unique S.order S.top τ.property h1.2 h2.2
  · intro z hz
    obtain ⟨α, hα, rfl⟩ := (S.mem_check_iff _ _).mp (hx z hz)
    have hez : e ‘ (S.check α) ∈ S.check ν := function_value_mem he hz
    obtain ⟨β, hβ, heβ⟩ := (S.mem_check_iff _ _).mp hez
    have hval : (converseGraph e) ‘ (S.check β) = S.check α := by
      rw [← heβ]
      exact converseGraph_value_value he heinj hz
    rw [← hτ] at hval hgf
    obtain ⟨q, hqG, hq⟩ := (S.checkedFunctionValue_truth τ β α).mpr ⟨hgf, hval⟩
    exact (S.check_mem_iff _ _).mpr (mem_sep_iff.mpr ⟨hα, hα, β, hβ, q, S.generic.1.1 q hqG, hq⟩)

/-- If the check of `x` has size at most the check of `ν` in the extension, then in the ground
model `x` has size at most `ν × (P × P)`. -/
theorem ForcingContext.check_cardLE_of_cardLE (S : ForcingContext V) (hAC : InternalChoice V)
    {x ν : V} (hx : S.check x ≤# S.check ν) : x ≤# ν ×ˢ (S.P ×ˢ S.P) := by
  obtain ⟨y, -, hcard, hsub⟩ := S.cover_of_cardLE hAC x ν (fun _ hz ↦ hz) hx
  refine (cardLE_of_subset ?_).trans hcard
  intro α hα
  exact (S.check_mem_iff α y).mp (hsub _ ((S.check_mem_iff α x).mpr hα))

/-- With `ν` an infinite ordinal of size at least `|P|`, cardinalities of ground sets are not
changed by the extension: `x̌ ≤# ν̌` gives `x ≤# ν`. -/
theorem ForcingContext.check_cardLE_of_cardLE_infinite (S : ForcingContext V)
    (hAC : InternalChoice V) {x ν : V} (hν : IsOrdinal ν) (hω : (ω : V) ⊆ ν) (hP : S.P ≤# ν)
    (hx : S.check x ≤# S.check ν) : x ≤# ν := by
  have hνord : IsOrdinal ν := hν
  have hunion : ν ∪ (ω : V) = ν :=
    mem_ext (fun z ↦ ⟨fun h ↦ (mem_union_iff.mp h).elim id (fun h ↦ hω z h),
      fun h ↦ mem_union_iff.mpr (Or.inl h)⟩)
  have hsq : ν ×ˢ ν ≤# ν := by
    have h := ordinal_prod_cardLE_union_omega (V := V) ν
    rwa [hunion] at h
  have hPP : S.P ×ˢ S.P ≤# ν := (prod_cardLE_prod hP hP).trans hsq
  exact (S.check_cardLE_of_cardLE hAC hx).trans
    ((prod_cardLE_prod (CardLE.refl ν) hPP).trans hsq)

end ZFVP
