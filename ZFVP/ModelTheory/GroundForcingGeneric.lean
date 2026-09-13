import ZFVP.ModelTheory.TransitiveZFBoundedQuantifiers
import ZFVP.ModelTheory.ForcingGeneric

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingFilter (P R G : V) : Prop :=
  G ⊆ P ∧ (∃ p, p ∈ G) ∧
    (∀ p ∈ G, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R → q ∈ G) ∧
    ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, ⟨r, p⟩ₖ ∈ R ∧ ⟨r, q⟩ₖ ∈ R

def IsGroundForcingGeneric (U P R G : V) : Prop :=
  IsForcingFilter P R G ∧ ∀ D ∈ U, ForcingDense P R D → ∃ p ∈ G, p ∈ D

instance isForcingFilter_definable : ℒₛₑₜ-relation₃[V] IsForcingFilter := by
  unfold IsForcingFilter
  definability

instance isGroundForcingGeneric_definable : ℒₛₑₜ-relation₄[V] IsGroundForcingGeneric := by
  unfold IsGroundForcingGeneric
  definability

theorem forcingFilter_compatible {P R G p q : V} (hG : IsForcingFilter P R G)
    (hp : p ∈ G) (hq : q ∈ G) : ForcingCompatible P R p q := by
  obtain ⟨r, hr, hrp, hrq⟩ := hG.2.2.2 p hp q hq
  exact ⟨r, hG.1 r hr, hrp, hrq⟩

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem subset_val_iff (A B : SetDomain U) : A ⊆ B ↔ A.val ⊆ B.val :=
  forall_mem_val_iff U A (fun x ↦ x ∈ B) (fun x ↦ x ∈ B.val) (fun _ ↦ Iff.rfl)

theorem forcingCompatible_iff (P R p q : SetDomain U) :
    ForcingCompatible P R p q ↔ ForcingCompatible P.val R.val p.val q.val := by
  unfold ForcingCompatible
  apply exists_mem_val_iff U P
  intro r
  simp only [kpair_mem_val_iff U]

theorem forcingDense_iff (P R D : SetDomain U) :
    ForcingDense P R D ↔ ForcingDense P.val R.val D.val := by
  unfold ForcingDense
  rw [subset_val_iff U]
  apply and_congr_right
  intro _
  apply forall_mem_val_iff U P
  intro p
  apply exists_mem_val_iff U D
  intro q
  exact kpair_mem_val_iff U q p R

theorem forcingDenseBelow_iff (P R D p : SetDomain U) :
    ForcingDenseBelow P R D p ↔ ForcingDenseBelow P.val R.val D.val p.val := by
  unfold ForcingDenseBelow
  rw [subset_val_iff U]
  apply and_congr_right
  intro _
  apply forall_mem_val_iff U P
  intro q
  rw [← kpair_mem_val_iff U]
  apply imp_congr_right
  intro _
  apply exists_mem_val_iff U D
  intro r
  exact kpair_mem_val_iff U r q R

theorem forcingDenseExtension_val (P R D p : SetDomain U) :
    (forcingDenseExtension P R D p).val = forcingDenseExtension P.val R.val D.val p.val := by
  unfold forcingDenseExtension
  apply sep_val U
  intro q _
  rw [forcingCompatible_iff U]
  rfl

theorem groundForcingGeneric_meets_denseBelow (P R : SetDomain U) {G : V}
    (hR : IsForcingPreorder P.val R.val) (hG : IsGroundForcingGeneric U P.val R.val G)
    (D p : SetDomain U) (hp : p.val ∈ G) (hD : ForcingDenseBelow P.val R.val D.val p.val) :
    ∃ q ∈ G, q ∈ D.val := by
  have hEU := (forcingDenseExtension P R D p).property
  rw [forcingDenseExtension_val U] at hEU
  obtain ⟨q, hqG, hqE⟩ := hG.2 _ hEU (forcingDenseExtension_dense hR hD)
  rcases (mem_sep_iff.mp hqE).2 with hqD | hqI
  · exact ⟨q, hqG, hqD⟩
  · exact False.elim (hqI (forcingFilter_compatible hG.1 hqG hp))

theorem groundForcingGeneric_iff_external (P R : SetDomain U) (G : V) (hGP : G ⊆ P.val) :
    IsGroundForcingGeneric U P.val R.val G ↔
      IsExternalForcingGeneric P R {p : SetDomain U | p.val ∈ G} := by
  constructor
  · intro hG
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro p hp
      exact hGP p.val hp
    · obtain ⟨p, hp⟩ := hG.1.2.1
      exact ⟨⟨p, (inferInstance : IsTransitive U).mem_trans (hGP p hp) P.property⟩, hp⟩
    · intro p hp q hq hpq
      exact hG.1.2.2.1 p.val hp q.val hq ((kpair_mem_val_iff U p q R).mp hpq)
    · intro p hp q hq
      obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p.val hp q.val hq
      let r' : SetDomain U := ⟨r, (inferInstance : IsTransitive U).mem_trans (hGP r hr) P.property⟩
      exact ⟨r', hr, (kpair_mem_val_iff U r' p R).mpr hrp, (kpair_mem_val_iff U r' q R).mpr hrq⟩
    · intro D hD
      obtain ⟨p, hpG, hpD⟩ := hG.2 D.val D.property ((forcingDense_iff U P R D).mp hD)
      exact ⟨⟨p, (inferInstance : IsTransitive U).mem_trans (hGP p hpG) P.property⟩, hpG, hpD⟩
  · intro hG
    refine ⟨⟨hGP, ?_, ?_, ?_⟩, ?_⟩
    · obtain ⟨p, hp⟩ := hG.1.2.1
      exact ⟨p.val, hp⟩
    · intro p hp q hq hpq
      let p' : SetDomain U := ⟨p, (inferInstance : IsTransitive U).mem_trans (hGP p hp) P.property⟩
      let q' : SetDomain U := ⟨q, (inferInstance : IsTransitive U).mem_trans hq P.property⟩
      exact hG.1.2.2.1 p' hp q' hq ((kpair_mem_val_iff U p' q' R).mpr hpq)
    · intro p hp q hq
      let p' : SetDomain U := ⟨p, (inferInstance : IsTransitive U).mem_trans (hGP p hp) P.property⟩
      let q' : SetDomain U := ⟨q, (inferInstance : IsTransitive U).mem_trans (hGP q hq) P.property⟩
      obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p' hp q' hq
      exact ⟨r.val, hr, (kpair_mem_val_iff U r p' R).mp hrp, (kpair_mem_val_iff U r q' R).mp hrq⟩
    · intro D hDU hD
      let D' : SetDomain U := ⟨D, hDU⟩
      obtain ⟨p, hpG, hpD⟩ := hG.2 D' ((forcingDense_iff U P R D').mpr hD)
      exact ⟨p.val, hpG, hpD⟩

end TransitiveZF
end ZFVP
