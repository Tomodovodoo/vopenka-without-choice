import ZFVP.ModelTheory.BooleanRealTrace
import ZFVP.ModelTheory.CompleteSubalgebra

/-! Boolean values of membership in a name over an arbitrary ground index set, and the canonical
"decision name" of a subset of a checked set: the pairs `(q̌, b_q)` for the Boolean values
`b_q = ‖q̌ ∈ τ‖`. Its value in any context over a subposet of the Boolean conditions containing the
relevant values is the set of checks whose value lies in the generic; in the Boolean extension it
recovers the value of `τ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The name `{(q̌, s ‘ q) : q ∈ Q, s ‘ q ∈ P'}`. -/
noncomputable def decisionName (one s Q P' : V) : V :=
  repl (fun q ↦ ⟨checkName one q, s ‘ q⟩ₖ) (by definability) {q ∈ Q ; s ‘ q ∈ P'}

theorem mem_decisionName_iff (one s Q P' z : V) :
    z ∈ decisionName one s Q P' ↔ ∃ q ∈ Q, s ‘ q ∈ P' ∧ z = ⟨checkName one q, s ‘ q⟩ₖ := by
  unfold decisionName
  rw [repl_spec]
  simp only [mem_sep_iff, and_assoc]

theorem decisionName_isName {one s Q P' : V} (hone : one ∈ P') :
    IsForcingName P' (decisionName one s Q P') := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨q, _, hq, rfl⟩ := (mem_decisionName_iff _ _ _ _ _).mp hz
  exact ⟨checkName one q, s ‘ q, hq, rfl, checkName_isName hone q⟩

namespace ForcingContext

variable (S : ForcingContext V)

theorem check_eq_ofName_checkName (x : V) :
    S.check x = S.ofName ⟨checkName S.one x, checkName_isName S.top.1 x⟩ := rfl

/-- The value of the decision name: the checks whose Boolean value lies in the generic. -/
theorem mem_ofName_decisionName (s Q : V) (x : S.Model) :
    x ∈ S.ofName ⟨decisionName S.one s Q S.P, decisionName_isName S.top.1⟩ ↔
      ∃ q ∈ Q, s ‘ q ∈ S.G ∧ x = S.check q := by
  rw [S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hp, hνp, rfl⟩
    obtain ⟨q, hq, _, he⟩ := (mem_decisionName_iff _ _ _ _ _).mp hνp
    obtain ⟨hν, hpe⟩ := kpair_iff.mp he
    refine ⟨q, hq, hpe ▸ hp, ?_⟩
    rw [S.check_eq_ofName_checkName]
    congr 1
    exact Subtype.ext hν
  · rintro ⟨q, hq, hqG, rfl⟩
    refine ⟨⟨checkName S.one q, checkName_isName S.top.1 q⟩, s ‘ q, hqG, ?_, rfl⟩
    exact (mem_decisionName_iff _ _ _ _ _).mpr ⟨q, hq, S.generic.1.1 _ hqG, rfl⟩

variable (A : ForcingContext V)

/-- The Boolean values `‖q̌ ∈ τ‖` for `q ∈ Q`, as a function on `Q`. -/
noncomputable def booleanValueFamily (τ Q : V) : V :=
  definableGraph Q (A.booleanMemValue τ) (A.booleanMemValue_definable τ)

theorem booleanValueFamily_mem_function (τ Q : V) :
    A.booleanValueFamily τ Q ∈ regularSets A.P A.R ^ Q :=
  definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun _ _ ↦ (mem_regularSets_iff _ _ _).mpr (A.booleanValue_regular memAtom _))

theorem booleanValueFamily_value {τ Q q : V} (hq : q ∈ Q) :
    (A.booleanValueFamily τ Q) ‘ q = A.booleanMemValue τ q :=
  value_definableGraph _ _ _ hq

theorem booleanValueFamily_range_subset (τ Q : V) :
    range (A.booleanValueFamily τ Q) ⊆ regularSets A.P A.R :=
  range_subset_of_mem_function (A.booleanValueFamily_mem_function τ Q)

/-- Membership of a Boolean value in the Boolean generic is truth of the membership. -/
theorem booleanMemValue_mem_generic_iff (τ : ForcingName A.booleanContext.P) (q : V) :
    A.booleanMemValue τ.val q ∈ A.booleanContext.G ↔
      A.booleanContext.check q ∈ A.booleanContext.ofName τ := by
  rw [← A.booleanMemValue_meets τ q]
  change A.booleanMemValue τ.val q ∈ booleanGeneric A.P A.R A.G ↔ _
  rw [mem_booleanGeneric_iff]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨p, hp, hpv⟩
    exact ⟨(mem_booleanConditions_iff _ _ _).mpr ⟨A.booleanValue_regular memAtom _, p, hpv⟩, p, hp, hpv⟩

/-- In the Boolean extension the decision name of the value family recovers the value of `τ`. -/
theorem ofName_decisionName_boolean (τ : ForcingName A.booleanContext.P) {Q : V}
    (hτ : A.booleanContext.ofName τ ⊆ A.booleanContext.check Q) :
    A.booleanContext.ofName ⟨decisionName A.booleanContext.one (A.booleanValueFamily τ.val Q) Q
      A.booleanContext.P, decisionName_isName A.booleanContext.top.1⟩ = A.booleanContext.ofName τ := by
  apply mem_ext
  intro x
  rw [A.booleanContext.mem_ofName_decisionName]
  constructor
  · rintro ⟨q, hq, hqG, rfl⟩
    rw [A.booleanValueFamily_value hq] at hqG
    exact (A.booleanMemValue_mem_generic_iff τ q).mp hqG
  · intro hx
    obtain ⟨q, hq, rfl⟩ := (A.booleanContext.mem_check_iff _ _).mp (hτ x hx)
    refine ⟨q, hq, ?_, rfl⟩
    rw [A.booleanValueFamily_value hq]
    exact (A.booleanMemValue_mem_generic_iff τ q).mpr hx

/-- In the extension by a complete subalgebra containing the value family, the decision name has
the same value as in the Boolean extension. -/
theorem subalgebraRealization_value_decisionName {D : V} (hD : IsCompleteSubalgebra A.P A.R D)
    (τ : ForcingName A.booleanContext.P) {Q : V} (hτ : A.booleanContext.ofName τ ⊆ A.booleanContext.check Q)
    (hrange : range (A.booleanValueFamily τ.val Q) ⊆ D) :
    (A.subalgebraRealization hD).value ((A.subalgebraContext hD).ofName
      ⟨decisionName (A.subalgebraContext hD).one (A.booleanValueFamily τ.val Q) Q
        (A.subalgebraContext hD).P, decisionName_isName (A.subalgebraContext hD).top.1⟩) =
      A.booleanContext.ofName τ := by
  rw [← A.ofName_decisionName_boolean τ hτ]
  have h := A.booleanContext.restrictRealization_value_ofName
    (A.subalgebraConditions_subset_boolean (D := D)) (A.top_mem_subalgebraConditions hD)
    (hD.trace_generic A.order A.generic)
    ⟨decisionName (A.subalgebraContext hD).one (A.booleanValueFamily τ.val Q) Q
        (A.subalgebraContext hD).P, decisionName_isName (A.subalgebraContext hD).top.1⟩
  refine h.trans ?_
  apply mem_ext
  intro x
  rw [A.booleanContext.mem_ofName_iff, A.booleanContext.mem_ofName_decisionName]
  constructor
  · rintro ⟨ν, p, hp, hνp, rfl⟩
    obtain ⟨q, hq, _, he⟩ := (mem_decisionName_iff _ _ _ _ _).mp hνp
    obtain ⟨hν, hpe⟩ := kpair_iff.mp he
    refine ⟨q, hq, hpe ▸ hp, ?_⟩
    rw [A.booleanContext.check_eq_ofName_checkName]
    congr 1
    exact Subtype.ext hν
  · rintro ⟨q, hq, hqG, rfl⟩
    refine ⟨⟨checkName A.booleanContext.one q, checkName_isName A.booleanContext.top.1 q⟩,
      (A.booleanValueFamily τ.val Q) ‘ q, hqG, ?_, rfl⟩
    refine (mem_decisionName_iff _ _ _ _ _).mpr ⟨q, hq, ?_, rfl⟩
    exact (mem_subalgebraConditions_iff _ _ _ _).mpr
      ⟨hrange _ (value_mem_range (A.booleanValueFamily_mem_function τ.val Q) hq),
        A.booleanContext.generic.1.1 _ hqG⟩

end ForcingContext

end ZFVP
