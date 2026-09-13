import ZFVP.ModelTheory.ForcingIsomorphismModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A : ForcingContext V) {Q S f : V}
    (hf : IsForcingIsomorphism A.P A.R Q S f) (hS : IsForcingPreorder Q S)

noncomputable def isomorphismImage : ForcingContext V :=
  ⟨Q, S, f ‘ A.one, forcingProjectionGeneric Q S f A.G, hS, hf.map_top A.top,
    hf.projection.generic hS A.generic⟩

theorem isomorphismImage_pullback :
    forcingProjectionGeneric A.P A.R (converseGraph f) (A.isomorphismImage hf hS).G = A.G :=
  hf.generic_inverse_image A.generic.1 A.order hS

noncomputable def isomorphismImageEquiv : A.Model ≃ (A.isomorphismImage hf hS).Model :=
  A.isomorphismModelEquiv (A.isomorphismImage hf hS) hf (A.isomorphismImage_pullback hf hS)

theorem isomorphismImageEquiv_mem (x y : A.Model) :
    A.isomorphismImageEquiv hf hS x ∈ A.isomorphismImageEquiv hf hS y ↔ x ∈ y :=
  A.isomorphismModelEquiv_mem_iff (A.isomorphismImage hf hS) hf (A.isomorphismImage_pullback hf hS) x y

theorem isomorphismImageEquiv_check (x : V) :
    A.isomorphismImageEquiv hf hS (A.check x) = (A.isomorphismImage hf hS).check x :=
  A.isomorphismModelEquiv_check (A.isomorphismImage hf hS) hf (A.isomorphismImage_pullback hf hS) x

theorem isomorphismImageEquiv_name (τ : ForcingName A.P) :
    A.isomorphismImageEquiv hf hS (A.ofName τ) =
      (A.isomorphismImage hf hS).ofName ⟨nameAction f τ.val, nameAction_isName hf.1 τ.property⟩ :=
  A.isomorphismModelEquiv_name (A.isomorphismImage hf hS) hf (A.isomorphismImage_pullback hf hS) τ

theorem isomorphismImageEquiv_symm_name (τ : ForcingName Q) :
    (A.isomorphismImageEquiv hf hS).symm ((A.isomorphismImage hf hS).ofName τ) =
      A.ofName ⟨nameAction (converseGraph f) τ.val, nameAction_isName hf.inverse_maps τ.property⟩ :=
  A.isomorphismModelEquiv_symm_name (A.isomorphismImage hf hS) hf (A.isomorphismImage_pullback hf hS) τ

end ForcingContext
end ZFVP
