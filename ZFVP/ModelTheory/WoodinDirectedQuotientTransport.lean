import ZFVP.ModelTheory.WoodinDirectedActualQuotient
import ZFVP.ModelTheory.EquivalentRetractionQuotientTransfer
import ZFVP.ModelTheory.TwoStepDirectedClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingSeparativeDirectedClosedAtFormula : SetTheorySemisentence 3 :=
  “P R α. ∃ S, !forcingSeparativeOrderFormula S P R ∧ !forcingDirectedClosedAtFormula P S α”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingSeparativeDirectedClosedAtFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun P R α ↦ IsForcingDirectedClosedAt P (forcingSeparativeOrder P R) α)
      via forcingSeparativeDirectedClosedAtFormula :=
  ⟨fun v ↦ by simp [forcingSeparativeDirectedClosedAtFormula]⟩

theorem ElementaryMap.forcingSeparativeDirectedClosedAt_iff
    {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (j : ElementaryMap V W) (P R α : V) :
    IsForcingDirectedClosedAt P (forcingSeparativeOrder P R) α ↔
      IsForcingDirectedClosedAt (j P) (forcingSeparativeOrder (j P) (j R)) (j α) := by
  have h := j.evalb forcingSeparativeDirectedClosedAtFormula ![P, R, α]
  exact (Defined.eval_iff _).symm.trans (h.trans (Defined.eval_iff _))

theorem IsForcingSplitProjection.separative_directedClosedAt_iff_of_order_reflecting
    {P R Q S π E α : V} (h : IsForcingSplitProjection P R Q S π E)
    (ho : ∀ a ∈ Q, ∀ b ∈ Q, ⟨π ‘ a, π ‘ b⟩ₖ ∈ R ↔ ⟨a, b⟩ₖ ∈ S) :
    IsForcingDirectedClosedAt Q (forcingSeparativeOrder Q S) α ↔
      IsForcingDirectedClosedAt P (forcingSeparativeOrder P R) α := by
  constructor
  · exact h.separative_directedClosedAt_of_source
  · exact h.projection.separative_directedClosedAt
      (fun _ ha _ hb ↦ h.compatible_iff_of_order_reflecting ho ha hb)
      (fun p hp ↦ ⟨E ‘ p, function_value_mem h.maps hp, h.right_inverse p hp⟩)

namespace ForcingContext
variable (A B : ForcingContext V) (e : A.Model ≃ B.Model)
  (hm : ∀ x y, e x ∈ e y ↔ x ∈ y) (hc : ∀ x, e (A.check x) = B.check x)
  {Q S π K L ρ u v : V}
  (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ B.P ^ K) (hu : u ∈ K ^ Q) (hv : v ∈ Q ^ K)
  (hg : ∀ p ∈ Q, ρ ‘ (u ‘ p) ∈ B.G ↔ π ‘ p ∈ A.G)
  (hi : ∀ q ∈ K, u ‘ (v ‘ q) = q)
  (ho : ∀ p ∈ Q, ∀ q ∈ Q, ⟨u ‘ p, u ‘ q⟩ₖ ∈ L ↔ ⟨p, q⟩ₖ ∈ S)

include hm hc hπ hρ hu hv hg hi ho in
theorem projectionQuotient_equivalence_directedClosedAt_iff (α : A.Model) :
    IsForcingDirectedClosedAt (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α ↔
    IsForcingDirectedClosedAt (B.projectionQuotient K ρ)
      (forcingSeparativeOrder (B.projectionQuotient K ρ) (B.projectionQuotientOrder K L ρ)) (e α) := by
  have hs := A.transportedProjectionQuotient_splitProjection B e hm hc hπ hρ hu hv hg hi ho
  have hc' := hs.separative_directedClosedAt_iff_of_order_reflecting
    (A.transportedProjectionQuotientMap_order_iff B e hm hc hπ hρ hu hg ho) (α := α)
  have ht := (ElementaryMap.ofMembershipIso e hm).forcingSeparativeDirectedClosedAt_iff
    (A.transportedProjectionQuotient B e K ρ)
    (A.transportedProjectionQuotientOrder B e K L ρ) α
  change _ ↔ IsForcingDirectedClosedAt (e (e.symm _))
    (forcingSeparativeOrder (e (e.symm _)) (e (e.symm _))) (e α) at ht
  simp only [Equiv.apply_symm_apply] at ht
  exact hc'.trans ht

include hm hc hπ hρ hu hv hg hi ho in
theorem projectionQuotient_equivalence_directedClosedBelow_check (κ : V)
    (hclosed : ∀ α ∈ A.check κ,
      IsForcingDirectedClosedAt (A.projectionQuotient Q π)
        (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α) :
    ∀ β ∈ B.check κ,
      IsForcingDirectedClosedAt (B.projectionQuotient K ρ)
        (forcingSeparativeOrder (B.projectionQuotient K ρ) (B.projectionQuotientOrder K L ρ)) β := by
  intro β hβ
  obtain ⟨α, rfl⟩ := e.surjective β
  have hα : α ∈ A.check κ := (hm α (A.check κ)).mp (hc κ ▸ hβ)
  exact (A.projectionQuotient_equivalence_directedClosedAt_iff B e hm hc hπ hρ hu hv hg hi ho α).mp
    (hclosed α hα)

end ForcingContext
theorem equivalentRetraction_quotient_directedClosedBelow
    {P R one N T n P' R' f Q S π K L ρ u v κ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hr : IsForcingRetraction N T P R n) (hT : IsForcingPreorder N T)
    (hone : one ∈ N) (he : ∀ p ∈ P, ⟨n ‘ p, p⟩ₖ ∈ R)
    (hf : IsForcingIsomorphism N T P' R' f) (hR' : IsForcingPreorder P' R')
    (hπ : IsForcingProjection P R Q S π) (_hS : IsForcingPreorder Q S)
    (hρ : IsForcingProjection P' R' K L ρ) (_hL : IsForcingPreorder K L)
    (hu : u ∈ K ^ Q) (hv : v ∈ Q ^ K)
    (hi : ∀ q ∈ K, u ‘ (v ‘ q) = q)
    (ho : ∀ p ∈ Q, ∀ q ∈ Q, ⟨u ‘ p, u ‘ q⟩ₖ ∈ L ↔ ⟨p, q⟩ₖ ∈ S)
    (hcomm : ∀ p ∈ Q, ρ ‘ (u ‘ p) = (compose n f) ‘ (π ‘ p))
    (hclosed : ∀ (A : ForcingContext V), A.P = P → A.R = R → A.one = one →
      ∀ α ∈ A.check κ, IsForcingDirectedClosedAt (A.projectionQuotient Q π)
        (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) α)
    (H : Set V) (hH : IsExternalForcingGeneric P' R' H) :
    let C : ForcingContext V := ⟨P', R', f ‘ one, H, hR', hf.map_top (hr.top_of_mem htop hone), hH⟩
    ∀ β ∈ C.check κ, IsForcingDirectedClosedAt (C.projectionQuotient K ρ)
      (forcingSeparativeOrder (C.projectionQuotient K ρ) (C.projectionQuotientOrder K L ρ)) β := by
  have htop' := hf.map_top (hr.top_of_mem htop hone)
  let G := forcingProjectionPreimage P (compose n f) H
  have hG : IsExternalForcingGeneric P R G := hr.isomorphism_generic_preimage hf hR he hH
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let B := A.retractionIsomorphismImage hr hT hone hf hR'
  let C : ForcingContext V := ⟨P', R', f ‘ one, H, hR', htop', hH⟩
  have hBG : B.G = H := by
    change forcingProjectionGeneric P' R' f (forcingProjectionGeneric N T n G) = H
    rw [forcingProjectionGeneric_comp hf.projection hr.projection hR' hT hG.1]
    exact (hr.isomorphism_projection hf).image_preimage (hr.isomorphism_surjective hf) hR' hH.1
  have hctx : B = C := by
    dsimp [B, C, ForcingContext.retractionIsomorphismImage, ForcingContext.retractionImage,
      ForcingContext.isomorphismImage, A]
    congr 1
  have hg : ∀ p ∈ Q, ρ ‘ (u ‘ p) ∈ B.G ↔ π ‘ p ∈ A.G := by
    intro p hp
    rw [hBG, hcomm p hp]
    change _ ↔ π ‘ p ∈ P ∧ (compose n f) ‘ (π ‘ p) ∈ H
    simp only [function_value_mem hπ.maps hp, true_and]
  have hA := hclosed A rfl rfl rfl
  have hB := A.projectionQuotient_equivalence_directedClosedBelow_check B
    (A.retractionIsomorphismImageEquiv hr hT hone he hf hR')
    (A.retractionIsomorphismImageEquiv_mem hr hT hone he hf hR')
    (A.retractionIsomorphismImageEquiv_check hr hT hone he hf hR')
    hπ.maps hρ.maps hu hv hg hi ho κ hA
  rw [hctx] at hB
  exact hB

end ZFVP
