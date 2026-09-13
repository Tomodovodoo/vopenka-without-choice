import ZFVP.ModelTheory.ForcingVopenkaPreservation
import ZFVP.ModelTheory.BooleanGenericTransfer
import ZFVP.ModelTheory.ClassForcingTowerBoundedModels
import ZFVP.SetTheory.VopenkaLowenheimSkolem
import ZFVP.SetTheory.UsubaCollapseTargets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Boolean completion removes antisymmetry as a restriction on the
set-forcing preservation theorem for VP. -/
theorem preorder_vopenkaInstance (A : ForcingContext V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (φ : SetTheorySemisentence 2) : VopenkaInstance (V := A.Model) φ := by
  have hB := A.booleanContext.vopenkaInstance (booleanOrder_poset A.P A.R) hVP φ
  apply vopenkaInstance_of_membershipIso A.booleanEquiv.symm ?_ φ hB
  intro x y
  simpa only [Equiv.apply_symm_apply] using
    (A.booleanEquiv_mem_iff (A.booleanEquiv.symm x) (A.booleanEquiv.symm y)).symm

theorem lsCardinals_unbounded (A : ForcingContext V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (ξ : A.Model) [IsOrdinal ξ] : ∃ κ : A.Model, ξ ∈ κ ∧ IsLSCardinal κ :=
  vopenka_lsCardinal_unbounded (A.preorder_vopenkaInstance hVP) ξ

theorem usubaTargets (A : ForcingContext V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (ξ : A.Model) [IsOrdinal ξ] :
    ξ ∈ usubaAuxiliaryLS ξ ∧ IsWeaklyLSCardinal (usubaAuxiliaryLS ξ) ∧
      IsLSCardinal (usubaCollapseTarget ξ) ∧
      internalCofinality (usubaCollapseTarget ξ) = hartogsNumber (usubaAuxiliaryLS ξ) ∧
      IsRegularCardinal (internalCofinality (usubaCollapseTarget ξ)) ∧
      usubaAuxiliaryLS ξ ∈ internalCofinality (usubaCollapseTarget ξ) ∧
      internalCofinality (usubaCollapseTarget ξ) ∈ usubaCollapseTarget ξ :=
  usubaCollapseTarget_spec
    (fun β hβ ↦ by have := hβ; exact A.lsCardinals_unbounded hVP β) ξ

end ForcingContext
end ZFVP
