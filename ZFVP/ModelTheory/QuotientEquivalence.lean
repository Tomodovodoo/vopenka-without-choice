import ZFVP.ModelTheory.EndExtensionBasics
import ZFVP.ModelTheory.QuotientForcing
import ZFVP.ModelTheory.ForcingRealizationGeneration
import ZFVP.SetTheory.EndExtensionNameValue

/-! The factorization `V[G] = V[G ∩ D][G / D]`: the Boolean extension is isomorphic, over the
ground model, to the extension of the intermediate model `V[G ∩ D]` by the quotient forcing with
the Boolean generic. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A : ForcingContext V) {D : V} (hD : IsCompleteSubalgebra A.P A.R D)

/-- The ground model inside the two-step extension. -/
noncomputable def quotientGround : MembershipEndExtension V (A.quotientContext hD).Model :=
  (A.subalgebraContext hD).checkEmbedding.trans (A.quotientContext hD).checkEmbedding

theorem quotientGround_apply (x : V) :
    A.quotientGround hD x = (A.quotientContext hD).check ((A.subalgebraContext hD).check x) := rfl

theorem quotientGround_mem_genericSet_iff (b : V) :
    A.quotientGround hD b ∈ (A.quotientContext hD).genericSet ↔ b ∈ booleanGeneric A.P A.R A.G := by
  rw [quotientGround_apply, (A.quotientContext hD).check_mem_genericSet_iff]
  exact A.check_mem_quotientGeneric_iff hD b

/-- The Boolean extension realized inside the two-step extension. -/
noncomputable def quotientRealization : ForcingRealization A.booleanContext (A.quotientContext hD).Model where
  ground := A.quotientGround hD
  genericSet := (A.quotientContext hD).genericSet
  generic_subset := by
    intro x hx
    have h1 := (A.quotientContext hD).genericSet_subset x hx
    have h2 : (A.quotientContext hD).check (A.quotientConditions hD) ⊆
        (A.quotientContext hD).check ((A.subalgebraContext hD).check (booleanConditions A.P A.R)) :=
      ((A.quotientContext hD).checkEmbedding.subset_iff _ _).mpr (A.quotientConditions_subset hD)
    exact h2 x h1
  generic_mem := A.quotientGround_mem_genericSet_iff hD

/-- Names over the subalgebra are names over the Boolean completion. -/
def subalgebraNameLift (τ : ForcingName (A.subalgebraContext hD).P) : ForcingName A.booleanContext.P :=
  ⟨τ.val, τ.property.mono (subalgebraConditions_subset A.P A.R D)⟩

theorem quotientGeneric_inter_eq (τ : ForcingName (A.subalgebraContext hD).P) :
    (A.quotientContext hD).genericSet ∩
        (A.quotientContext hD).check ((A.subalgebraContext hD).check (subalgebraConditions A.P A.R D)) =
      (A.quotientContext hD).check (A.subalgebraContext hD).genericSet ∩
        (A.quotientContext hD).check ((A.subalgebraContext hD).check (subalgebraConditions A.P A.R D)) := by
  let C := A.subalgebraContext hD
  let Q := A.quotientContext hD
  ext z
  rw [mem_inter_iff, mem_inter_iff]
  constructor
  · rintro ⟨hz, hzC⟩
    refine ⟨?_, hzC⟩
    obtain ⟨y, hy, rfl⟩ := (Q.mem_check_iff _ _).mp hzC
    obtain ⟨d, hd, rfl⟩ := (C.mem_check_iff _ _).mp hy
    rw [Q.check_mem_genericSet_iff] at hz
    have hz' := (A.check_mem_quotientGeneric_iff hD d).mp hz
    rw [Q.check_mem_iff, C.check_mem_genericSet_iff]
    exact ⟨hz', hd⟩
  · rintro ⟨hz, hzC⟩
    refine ⟨?_, hzC⟩
    obtain ⟨y, hy, rfl⟩ := (Q.mem_check_iff _ _).mp hzC
    obtain ⟨d, _, rfl⟩ := (C.mem_check_iff _ _).mp hy
    rw [Q.check_mem_iff, C.check_mem_genericSet_iff] at hz
    rw [Q.check_mem_genericSet_iff]
    exact (A.check_mem_quotientGeneric_iff hD d).mpr hz.1

/-- The value of a subalgebra name in the Boolean extension is sent to the check of its value in
the intermediate extension. -/
theorem quotientRealization_value_lift (τ : ForcingName (A.subalgebraContext hD).P) :
    (A.quotientRealization hD).value (A.booleanContext.ofName (A.subalgebraNameLift hD τ)) =
      (A.quotientContext hD).check ((A.subalgebraContext hD).ofName τ) := by
  let C := A.subalgebraContext hD
  let Q := A.quotientContext hD
  rw [ForcingRealization.value_ofName, ← C.nameValue_genericSet_check τ]
  change nameValue Q.genericSet (Q.check (C.check τ.val)) =
    Q.checkEmbedding (nameValue C.genericSet (C.check τ.val))
  rw [Q.checkEmbedding.map_nameValue]
  change nameValue Q.genericSet (Q.check (C.check τ.val)) =
    nameValue (Q.check C.genericSet) (Q.check (C.check τ.val))
  have hn : IsForcingName (Q.check (C.check (subalgebraConditions A.P A.R D))) (Q.check (C.check τ.val)) :=
    Q.checkEmbedding.map_forcingName (C.checkEmbedding.map_forcingName τ.property)
  rw [← nameValue_inter_of_name hn, A.quotientGeneric_inter_eq hD τ, nameValue_inter_of_name hn]

theorem quotientRealization_value_genericSet :
    (A.quotientRealization hD).value A.booleanContext.genericSet = (A.quotientContext hD).genericSet := by
  let B := A.booleanContext
  let Q := A.quotientContext hD
  let L := A.quotientRealization hD
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := L.value_endExtension _ hz
    obtain ⟨b, hb, rfl⟩ := (B.mem_genericSet_iff x).mp hx
    rw [L.value_check]
    exact (A.quotientGround_mem_genericSet_iff hD b).mpr hb
  · intro hz
    obtain ⟨y, hy, rfl⟩ := (Q.mem_genericSet_iff z).mp hz
    obtain ⟨b, hb, rfl⟩ := hy
    have hx : B.check b ∈ B.genericSet := (B.check_mem_genericSet_iff b).mpr hb
    have := (L.value_mem_iff _ _).mpr hx
    rw [L.value_check] at this
    exact this

theorem quotientRealization_surjective : Function.Surjective (A.quotientRealization hD).value :=
  ForcingRealization.value_surjective_of_generators (A.quotientContext hD) (A.quotientRealization hD)
    (fun x ↦ by
      obtain ⟨τ, rfl⟩ := (A.subalgebraContext hD).ofName_surjective x
      exact ⟨_, A.quotientRealization_value_lift hD τ⟩)
    ⟨_, A.quotientRealization_value_genericSet hD⟩

/-- The factorization `V[G] ≃ V[G ∩ D][G / D]`. -/
noncomputable def quotientEquiv : A.booleanContext.Model ≃ (A.quotientContext hD).Model :=
  Equiv.ofBijective (A.quotientRealization hD).value
    ⟨(A.quotientRealization hD).value_injective, A.quotientRealization_surjective hD⟩

theorem quotientEquiv_mem_iff (x y : A.booleanContext.Model) :
    A.quotientEquiv hD x ∈ A.quotientEquiv hD y ↔ x ∈ y :=
  (A.quotientRealization hD).value_mem_iff x y

theorem quotientEquiv_check (x : V) :
    A.quotientEquiv hD (A.booleanContext.check x) =
      (A.quotientContext hD).check ((A.subalgebraContext hD).check x) :=
  (A.quotientRealization hD).value_check x

/-- Elements of the intermediate extension are sent to checks of the two-step extension. -/
theorem quotientEquiv_lift (τ : ForcingName (A.subalgebraContext hD).P) :
    A.quotientEquiv hD (A.booleanContext.ofName (A.subalgebraNameLift hD τ)) =
      (A.quotientContext hD).check ((A.subalgebraContext hD).ofName τ) :=
  A.quotientRealization_value_lift hD τ

end ForcingContext

end ZFVP
