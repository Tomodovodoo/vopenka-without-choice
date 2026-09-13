import ZFVP.ModelTheory.BoundedForcingPrefixAgreement
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.Syntax.SigmaOneInternalForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def subnameClosedForcingPoolFormula : SetTheorySemisentence 2 :=
  f“P D. (∀ τ ∈ D, !sigmaOneForcingNameFormula P τ) ∧ !boundedNonemptyFormula D ∧
    (∀ τ ∈ D, ∀ u, ∀ p, !kpair.dfn u p ∈ τ → u ∈ D)”

def guardedBoundedForcingFormula : SetTheorySemisentence 7 :=
  “P R D n φ b p. !sigmaOneBoundedCodeFormula n φ ∧ !boundedFunctionFormula b n D ∧ p ∈ P ∧
    !sigmaOneInternalForcingFormula P R D n φ b p”

def boundedForcingPrefixTransferFormula : SetTheorySemisentence 14 :=
  f“P R o Q S t π E D F n φ b p.
    !forcingPreorderFormula P R → !forcingTopFormula P R o →
    !forcingPreorderFormula Q S → !forcingTopFormula Q S t →
    !forcingSplitProjectionFormula P R Q S π E →
    (∀ q ∈ P, !value.dfn E q = q) →
    !subnameClosedForcingPoolFormula P D → !subnameClosedForcingPoolFormula Q F →
    !sigmaOneBoundedCodeFormula n φ → !boundedFunctionFormula b n D →
    !boundedFunctionFormula b n F → p ∈ P →
    (!guardedBoundedForcingFormula P R D n φ b p ↔
      !guardedBoundedForcingFormula Q S F n φ b p)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsSubnameClosedForcingPool (P D : V) : Prop :=
  (∀ τ ∈ D, IsForcingName P τ) ∧ IsNonempty D ∧
    ∀ τ ∈ D, ∀ u p, ⟨u, p⟩ₖ ∈ τ → u ∈ D

instance subnameClosedForcingPoolFormula_defined : Defined
    (fun v : Fin 2 → V ↦ IsSubnameClosedForcingPool (v 0) (v 1))
    subnameClosedForcingPoolFormula :=
  ⟨fun v ↦ by simp [subnameClosedForcingPoolFormula, IsSubnameClosedForcingPool]⟩

def GuardedBoundedForces (P R D n φ b p : V) : Prop :=
  IsBoundedFormulaCode n φ ∧ b ∈ D ^ n ∧ p ∈ P ∧ p ∈ internalForcingSet P R D n φ b

theorem eval_guardedBoundedForcingFormula (v : Fin 7 → V) :
    guardedBoundedForcingFormula.Evalb v ↔
      GuardedBoundedForces (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) := by
  have he : guardedBoundedForcingFormula.Evalb v ↔
      IsBoundedFormulaCode (v 3) (v 4) ∧ v 5 ∈ v 2 ^ v 3 ∧ v 6 ∈ v 0 ∧
        sigmaOneInternalForcingFormula.Evalb ![v 0, v 1, v 2, v 3, v 4, v 5, v 6] := by
    simp [guardedBoundedForcingFormula, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton]
  rw [he]
  apply and_congr_right
  intro hφ
  apply and_congr_right
  intro hb
  apply and_congr_right
  intro hp
  exact (eval_sigmaOneInternalForcingFormula (boundedFormulaFamily_subset _ hφ) hb hp).trans
    (mem_internalForcingSet (boundedFormulaFamily_subset _ hφ)).symm

instance guardedBoundedForcingFormula_defined : Defined
    (fun v : Fin 7 → V ↦ GuardedBoundedForces (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    guardedBoundedForcingFormula := ⟨eval_guardedBoundedForcingFormula⟩

private theorem forall_three_eq_bounded {W : Type*} (a b c : W) (F : W → W → W → Prop) :
    (∀ x y z, x = a → y = b → z = c → F x y z) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h x y z hx hy hz ↦ by subst x y z; exact h⟩

private theorem forall_six_eq_bounded {W : Type*} (a b c d e f : W)
    (F : W → W → W → W → W → W → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

private theorem forall_seven_eq_bounded {W : Type*} (a b c d e f g : W)
    (F : W → W → W → W → W → W → W → Prop) :
    (∀ t u v w x y z, t = a → u = b → v = c → w = d → x = e → y = f → z = g →
      F t u v w x y z) ↔ F a b c d e f g :=
  ⟨fun h ↦ h a b c d e f g rfl rfl rfl rfl rfl rfl rfl,
    fun h t u v w x y z ht hu hv hw hx hy hz ↦ by subst t u v w x y z; exact h⟩

theorem eval_boundedForcingPrefixTransferFormula (v : Fin 14 → V) :
    boundedForcingPrefixTransferFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
       IsForcingPreorder (v 3) (v 4) → IsForcingTop (v 3) (v 4) (v 5) →
       IsForcingSplitProjection (v 0) (v 1) (v 3) (v 4) (v 6) (v 7) →
       (∀ q ∈ v 0, (v 7) ‘ q = q) →
       IsSubnameClosedForcingPool (v 0) (v 8) → IsSubnameClosedForcingPool (v 3) (v 9) →
       IsBoundedFormulaCode (v 10) (v 11) → v 12 ∈ v 8 ^ v 10 → v 12 ∈ v 9 ^ v 10 → v 13 ∈ v 0 →
       (GuardedBoundedForces (v 0) (v 1) (v 8) (v 10) (v 11) (v 12) (v 13) ↔
         GuardedBoundedForces (v 3) (v 4) (v 9) (v 10) (v 11) (v 12) (v 13))) := by
  simp [boundedForcingPrefixTransferFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_three_eq_bounded,
    forall_six_eq_bounded, forall_seven_eq_bounded]

/-- Bounded-prefix forcing independence over arbitrary ZF models. Countable
generic semantics is used only to prove a fixed first-order ZF assertion. -/
theorem boundedForcing_prefix_iff
    {P R one Q S top π E D0 D1 n φ b p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hS : IsForcingPreorder Q S) (hu : IsForcingTop Q S top)
    (hπ : IsForcingSplitProjection P R Q S π E) (hE : ∀ p ∈ P, E ‘ p = p)
    (hD0 : IsSubnameClosedForcingPool P D0) (hD1 : IsSubnameClosedForcingPool Q D1)
    (hφ : IsBoundedFormulaCode n φ) (hb0 : b ∈ D0 ^ n) (hb1 : b ∈ D1 ^ n)
    (hp : p ∈ P) :
    p ∈ internalForcingSet P R D0 n φ b ↔ p ∈ internalForcingSet Q S D1 n φ b := by
  have hh := eval_of_countable_zf boundedForcingPrefixTransferFormula (by
    intro W _ _ _ _ v
    apply (eval_boundedForcingPrefixTransferFormula v).mpr
    intro hR ht hS hu hπ hE hD0 hD1 hφ hb0 hb1 hp
    have h := boundedForcing_prefix_iff_countable hR ht hS hu hπ hE
      hD0.1 hD1.1 hD0.2.1 hD1.2.1 hD0.2.2 hD1.2.2 hφ hb0 hb1 hp
    have hpQ := hπ.subset_of_section_identity hE _ hp
    simpa only [GuardedBoundedForces, hφ, hb0, hb1, hp, hpQ, true_and] using h)
    ![P, R, one, Q, S, top, π, E, D0, D1, n, φ, b, p]
  have h := (eval_boundedForcingPrefixTransferFormula _).mp hh
    hR ht hS hu hπ hE hD0 hD1 hφ hb0 hb1 hp
  change GuardedBoundedForces P R D0 n φ b p ↔ GuardedBoundedForces Q S D1 n φ b p at h
  have hpQ := hπ.subset_of_section_identity hE p hp
  simpa only [GuardedBoundedForces, hφ, hb0, hb1, hp, hpQ, true_and] using h

end ZFVP
