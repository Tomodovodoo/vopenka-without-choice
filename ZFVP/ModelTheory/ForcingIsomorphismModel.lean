import ZFVP.ModelTheory.ForcingIsomorphismTransport
import ZFVP.ModelTheory.ProjectionNameTransport
import ZFVP.SetTheory.MembershipIso
import ZFVP.SetTheory.HartogsDictionary
import ZFVP.SetTheory.ElementaryDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A B : ForcingContext V) {f : V}
  (hf : IsForcingIsomorphism A.P A.R B.P B.R f)
  (hG : forcingProjectionGeneric A.P A.R (converseGraph f) B.G = A.G)

include hf hG

theorem isomorphismInclusion_surjective :
    Function.Surjective (A.projectionInclusion B hf.splitProjection hG) := by
  intro y
  obtain ⟨τ, rfl⟩ := B.ofName_surjective y
  let σ : ForcingName A.P := ⟨nameAction (converseGraph f) τ.val,
    nameAction_isName hf.inverse_maps τ.property⟩
  refine ⟨A.ofName σ, ?_⟩
  rw [← A.projectionInclusion_nameAction B hf.splitProjection hG σ]
  apply congrArg B.ofName
  apply Subtype.ext
  exact hf.name_cancel_inverse τ.property

noncomputable def isomorphismModelEquiv : A.Model ≃ B.Model :=
  Equiv.ofBijective (A.projectionInclusion B hf.splitProjection hG)
    ⟨(A.projectionInclusion B hf.splitProjection hG).injective,
      A.isomorphismInclusion_surjective B hf hG⟩

theorem isomorphismModelEquiv_mem_iff (x y : A.Model) :
    A.isomorphismModelEquiv B hf hG x ∈ A.isomorphismModelEquiv B hf hG y ↔ x ∈ y :=
  (A.projectionInclusion B hf.splitProjection hG).mem_iff x y

theorem isomorphismModelEquiv_check (x : V) :
    A.isomorphismModelEquiv B hf hG (A.check x) = B.check x :=
  A.projectionInclusion_check B hf.splitProjection hG x

theorem isomorphismModelEquiv_name (τ : ForcingName A.P) :
    A.isomorphismModelEquiv B hf hG (A.ofName τ) =
      B.ofName ⟨nameAction f τ.val, nameAction_isName hf.1 τ.property⟩ :=
  (A.projectionInclusion_nameAction B hf.splitProjection hG τ).symm

theorem isomorphismModelEquiv_symm_name (τ : ForcingName B.P) :
    (A.isomorphismModelEquiv B hf hG).symm (B.ofName τ) =
      A.ofName ⟨nameAction (converseGraph f) τ.val, nameAction_isName hf.inverse_maps τ.property⟩ := by
  apply (A.isomorphismModelEquiv B hf hG).injective
  rw [Equiv.apply_symm_apply, A.isomorphismModelEquiv_name B hf hG]
  apply congrArg B.ofName
  apply Subtype.ext
  exact (hf.name_cancel_inverse τ.property).symm

noncomputable def isomorphismElementaryMap : ElementaryMap A.Model B.Model :=
  ElementaryMap.ofMembershipIso (A.isomorphismModelEquiv B hf hG)
    (A.isomorphismModelEquiv_mem_iff B hf hG)

theorem isomorphismModelEquiv_hartogs (γ : V) :
    A.isomorphismModelEquiv B hf hG (hartogsNumber (A.check γ)) = hartogsNumber (B.check γ) := by
  have hh := (A.isomorphismElementaryMap B hf hG).map_hartogsNumber (A.check γ)
  change A.isomorphismModelEquiv B hf hG (hartogsNumber (A.check γ)) =
    hartogsNumber (A.isomorphismModelEquiv B hf hG (A.check γ)) at hh
  simpa only [A.isomorphismModelEquiv_check B hf hG] using hh

theorem isomorphismModelEquiv_dependentChoiceAt (γ : V) :
    InternalDependentChoiceAt (A.check γ) ↔ InternalDependentChoiceAt (B.check γ) := by
  have hh := (A.isomorphismElementaryMap B hf hG).map_defined dependentChoiceAtFormula
    (fun v ↦ InternalDependentChoiceAt (v 0)) (fun v ↦ InternalDependentChoiceAt (v 0)) ![A.check γ]
  change InternalDependentChoiceAt (A.check γ) ↔
    InternalDependentChoiceAt (A.isomorphismModelEquiv B hf hG (A.check γ)) at hh
  simpa only [A.isomorphismModelEquiv_check B hf hG] using hh

theorem isomorphismModelEquiv_dependentChoiceBelow (γ : V) :
    (∀ α ∈ A.check γ, InternalDependentChoiceAt α) ↔
      ∀ α ∈ B.check γ, InternalDependentChoiceAt α := by
  constructor
  · intro h α hα
    obtain ⟨δ, hδ, rfl⟩ := (B.mem_check_iff γ α).mp hα
    exact (A.isomorphismModelEquiv_dependentChoiceAt B hf hG δ).mp
      (h _ ((A.check_mem_iff δ γ).mpr hδ))
  · intro h α hα
    obtain ⟨δ, hδ, rfl⟩ := (A.mem_check_iff γ α).mp hα
    exact (A.isomorphismModelEquiv_dependentChoiceAt B hf hG δ).mpr
      (h _ ((B.check_mem_iff δ γ).mpr hδ))

end ForcingContext
end ZFVP
