import ZFVP.ModelTheory.EquivalentRetractionQuotientForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingRetractionTransferFormula : SetTheorySemisentence 5 :=
  f“N T P R n. !boundedFunctionFormula n P N ∧ N ⊆ P ∧
    (∀ p ∈ N, !value.dfn n p = p) ∧
    (∀ p ∈ P, ∀ q ∈ P, !kpair.dfn p q ∈ R → !kpair.dfn (!value.dfn n p) (!value.dfn n q) ∈ T) ∧
    (∀ q ∈ P, ∀ p ∈ N, !kpair.dfn q p ∈ R ↔ !kpair.dfn (!value.dfn n q) p ∈ T) ∧
    (∀ q ∈ P, ∀ p ∈ N, !kpair.dfn p (!value.dfn n q) ∈ T →
      ∃ r ∈ P, !kpair.dfn r q ∈ R ∧ !value.dfn n r = p)”

def forcingIsomorphismTransferFormula : SetTheorySemisentence 5 :=
  f“N T P R f. !boundedFunctionFormula f N P ∧ !Injective.dfn f ∧ !range.dfn f = P ∧
    (∀ p ∈ N, ∀ q ∈ N, !kpair.dfn p q ∈ T ↔ !kpair.dfn (!value.dfn f p) (!value.dfn f q) ∈ R)”

def equivalentRetractionQuotientTransferFormula : SetTheorySemisentence 18 :=
  f“P R o N T n A B f Q S π K L ρ u v κ.
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingRetractionTransferFormula N T P R n ∧ !forcingPreorderFormula N T ∧ o ∈ N ∧
    (∀ p ∈ P, !kpair.dfn (!value.dfn n p) p ∈ R) ∧
    !forcingIsomorphismTransferFormula N T A B f ∧ !forcingPreorderFormula A B ∧
    !forcingProjectionFormula P R Q S π ∧ !forcingPreorderFormula Q S ∧
    !forcingProjectionFormula A B K L ρ ∧ !forcingPreorderFormula K L ∧
    !boundedFunctionFormula u Q K ∧ !boundedFunctionFormula v K Q ∧
    (∀ q ∈ K, !value.dfn u (!value.dfn v q) = q) ∧
    (∀ p ∈ Q, ∀ q ∈ Q, !kpair.dfn (!value.dfn u p) (!value.dfn u q) ∈ L ↔ !kpair.dfn p q ∈ S) ∧
    (∀ p ∈ Q, !value.dfn ρ (!value.dfn u p) = !value.dfn f (!value.dfn n (!value.dfn π p))) ∧
    !IsOrdinal.dfn κ ∧ !allProjectionQuotientClosedBelowFormula P R o Q S π κ →
    !allProjectionQuotientClosedBelowFormula A B (!value.dfn f o) K L ρ κ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingRetractionTransferFormula_defined : Defined
    (fun w : Fin 5 → V ↦ IsForcingRetraction (w 0) (w 1) (w 2) (w 3) (w 4))
    forcingRetractionTransferFormula := by
  refine ⟨fun w ↦ ?_⟩
  simp only [forcingRetractionTransferFormula]
  simp
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h ↦ ⟨h.maps, h.inclusion, h.fixes, h.monotone, h.below, h.lift⟩⟩

instance forcingIsomorphismTransferFormula_defined : Defined
    (fun w : Fin 5 → V ↦ IsForcingIsomorphism (w 0) (w 1) (w 2) (w 3) (w 4))
    forcingIsomorphismTransferFormula :=
  ⟨fun w ↦ by simp [forcingIsomorphismTransferFormula, IsForcingIsomorphism]⟩

theorem eval_equivalentRetractionQuotientTransferFormula (w : Fin 18 → V) :
    equivalentRetractionQuotientTransferFormula.Evalb w ↔
    (IsForcingPreorder (w 0) (w 1) → IsForcingTop (w 0) (w 1) (w 2) →
    IsForcingRetraction (w 3) (w 4) (w 0) (w 1) (w 5) → IsForcingPreorder (w 3) (w 4) → w 2 ∈ w 3 →
    (∀ p ∈ w 0, ⟨(w 5) ‘ p, p⟩ₖ ∈ w 1) →
    IsForcingIsomorphism (w 3) (w 4) (w 6) (w 7) (w 8) → IsForcingPreorder (w 6) (w 7) →
    IsForcingProjection (w 0) (w 1) (w 9) (w 10) (w 11) → IsForcingPreorder (w 9) (w 10) →
    IsForcingProjection (w 6) (w 7) (w 12) (w 13) (w 14) → IsForcingPreorder (w 12) (w 13) →
    w 15 ∈ (w 12) ^ (w 9) → w 16 ∈ (w 9) ^ (w 12) →
    (∀ q ∈ w 12, (w 15) ‘ ((w 16) ‘ q) = q) →
    (∀ p ∈ w 9, ∀ q ∈ w 9, ⟨(w 15) ‘ p, (w 15) ‘ q⟩ₖ ∈ w 13 ↔ ⟨p, q⟩ₖ ∈ w 10) →
    (∀ p ∈ w 9, (w 14) ‘ ((w 15) ‘ p) = (w 8) ‘ ((w 5) ‘ ((w 11) ‘ p))) →
    IsOrdinal (w 17) → ForcesProjectionQuotientClosedBelow (w 0) (w 1) (w 2) (w 9) (w 10) (w 11) (w 17) →
    ForcesProjectionQuotientClosedBelow (w 6) (w 7) ((w 8) ‘ (w 2)) (w 12) (w 13) (w 14) (w 17)) := by
  simp [equivalentRetractionQuotientTransferFormula]

theorem equivalentRetraction_quotient_closedBelow_forced
    {P R one N T n P' R' f Q S π K L ρ u v κ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hr : IsForcingRetraction N T P R n) (hT : IsForcingPreorder N T)
    (hone : one ∈ N) (he : ∀ p ∈ P, ⟨n ‘ p, p⟩ₖ ∈ R)
    (hf : IsForcingIsomorphism N T P' R' f) (hR' : IsForcingPreorder P' R')
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hρ : IsForcingProjection P' R' K L ρ) (hL : IsForcingPreorder K L)
    (hu : u ∈ K ^ Q) (hv : v ∈ Q ^ K)
    (hi : ∀ q ∈ K, u ‘ (v ‘ q) = q)
    (ho : ∀ p ∈ Q, ∀ q ∈ Q, ⟨u ‘ p, u ‘ q⟩ₖ ∈ L ↔ ⟨p, q⟩ₖ ∈ S)
    (hcomm : ∀ p ∈ Q, ρ ‘ (u ‘ p) = (compose n f) ‘ (π ‘ p))
    (hclosed : ForcesProjectionQuotientClosedBelow P R one Q S π κ) :
    ForcesProjectionQuotientClosedBelow P' R' (f ‘ one) K L ρ κ := by
  have hvalid := eval_of_countable_zf equivalentRetractionQuotientTransferFormula (by
    intro W _ _ _ _ w
    apply (eval_equivalentRetractionQuotientTransferFormula w).mpr
    intro hR htop hr hT hone he hf hR' hπ hS hρ hL hu hv hi ho hcomm hκ hclosed
    let := hκ
    apply equivalentRetraction_quotient_closedBelow_forced_countable
      hR htop hr hT hone he hf hR' hπ hS hρ hL hu hv hi ho ?_ hclosed
    intro p hp
    rw [value_compose_of_mem_function hr.maps hf.1 (function_value_mem hπ.maps hp)]
    exact hcomm p hp) ![P, R, one, N, T, n, P', R', f, Q, S, π, K, L, ρ, u, v, κ]
  apply (eval_equivalentRetractionQuotientTransferFormula _).mp hvalid
    hR htop hr hT hone he hf hR' hπ hS hρ hL hu hv hi ho ?_ (show IsOrdinal κ from inferInstance) hclosed
  intro p hp
  change ρ ‘ (u ‘ p) = f ‘ (n ‘ (π ‘ p))
  rw [← value_compose_of_mem_function hr.maps hf.1 (function_value_mem hπ.maps hp)]
  exact hcomm p hp

end ZFVP

