import ZFVP.ModelTheory.TwoStepLocalUnionBound
import ZFVP.ModelTheory.SaturatedTwoStepBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem saturated_twoStep_mem_of_all_generics [Countable V] {P R one δ q t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one) (hq : q ∈ P)
    (ν Q : ForcingName P) (hν : ν.val ∈ forcingNameHierarchy P δ)
    (hm : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), q ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      A.ofName ν ∈ A.ofName ⟨forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val,
        forcingSaturatedName_isName _ _ _ _⟩) :
    ⟨q, ν.val⟩ₖ ∈ twoStepConditions P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) t := by
  have hmem : q ∈ atomicMembership P R ν.val Q.val := by
    rw [← forcingFormula_nameMember]
    apply forcingFormula_of_all_generics hR ho hq nameMemberFormula ![ν, Q]
    intro G hG hqG
    let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
    have hx := ((A.mem_saturatedName_iff _ Q _).mp (hm G hG hqG)).1
    simpa [nameMemberFormula] using hx
  exact (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hq,
    mem_union_iff.mpr (Or.inl (forcingSaturatedName_mem_domain hν hq ν.property hmem)),
    forcingSaturatedName_forces_member hR hν hq ν.property hmem⟩

theorem local_union_pair_mem_of_all_generics [Countable V] {P R one δ p q S t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (Q f : ForcingName P)
    (h : IsForcingIterand P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) S t)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), q ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      let Q' := forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val
      ∃ κ α : A.Model, IsOrdinal α ∧
        IsForcingDescending
          (A.projectionQuotient (twoStepConditions P R Q' t) (twoStepProjection P R Q' t))
          (forcingSeparativeOrder
            (A.projectionQuotient (twoStepConditions P R Q' t) (twoStepProjection P R Q' t))
            (A.projectionQuotientOrder (twoStepConditions P R Q' t)
              (twoStepOrder P R Q' S t) (twoStepProjection P R Q' t))) α (A.ofName f) ∧
        IsRegularCardinal κ ∧ κ ⊆ A.check δ ∧ α ∈ κ ∧ InternalDependentChoiceAt α ∧
        A.ofName ⟨Q', h.posetName⟩ = woodinCollapse κ (A.check δ) ∧
        A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (A.check δ)) :
    let Q' := forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val
    ⟨q, forcingLocalCanonicalName P R one δ p
      (forcingSelectedUnion P R one (twoStepNames Q' t) (twoStepTailSelector P R Q' t) f.val)⟩ₖ ∈
        twoStepConditions P R Q' t := by
  dsimp only
  apply saturated_twoStep_mem_of_all_generics hR ho hq
    ⟨_, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩ Q
    (forcingLocalCanonicalName_mem hR ho hδ hP _ _)
  intro G hG hqG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
  obtain ⟨κ, α, hαord, hdesc, hκ, hκδ, hακ, hDC, hQ, hS⟩ := hf G hG hqG
  let := hαord
  have hpG : p ∈ A.G := A.generic.1.2.2.1 q hqG p hp hqp
  exact (TwoStepModel.local_collapse_union_bound A h hδ hP hpG f hdesc hκ hκδ hακ hDC hQ hS).1

end ZFVP
