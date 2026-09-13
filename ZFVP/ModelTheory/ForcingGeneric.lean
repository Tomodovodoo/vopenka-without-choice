import ZFVP.SetTheory.ForcingOrder
import Mathlib.Order.Ideal

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An external filter on an internally coded forcing preorder. -/
def IsExternalForcingFilter (P R : V) (G : Set V) : Prop :=
  (∀ p ∈ G, p ∈ P) ∧ G.Nonempty ∧
    (∀ p ∈ G, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R → q ∈ G) ∧
    ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, ⟨r, p⟩ₖ ∈ R ∧ ⟨r, q⟩ₖ ∈ R

/-- The quantifier over `D : V` ranges over the dense sets coded in the model. -/
def IsExternalForcingGeneric (P R : V) (G : Set V) : Prop :=
  IsExternalForcingFilter P R G ∧
    ∀ D : V, ForcingDense P R D → ∃ p ∈ G, p ∈ D

theorem externalForcingFilter_compatible {P R : V} {G : Set V}
    (hG : IsExternalForcingFilter P R G) {p q : V} (hp : p ∈ G) (hq : q ∈ G) :
    ForcingCompatible P R p q := by
  obtain ⟨r, hr, hrp, hrq⟩ := hG.2.2.2 p hp q hq
  exact ⟨r, hG.1 r hr, hrp, hrq⟩

theorem externalForcingGeneric_meets_denseBelow {P R D p : V} {G : Set V}
    (hR : IsForcingPreorder P R) (hG : IsExternalForcingGeneric P R G)
    (hp : p ∈ G) (hD : ForcingDenseBelow P R D p) : ∃ q ∈ G, q ∈ D := by
  obtain ⟨q, hq, hqE⟩ := hG.2 _ (forcingDenseExtension_dense hR hD)
  rcases (mem_sep_iff.mp hqE).2 with hqD | hqI
  · exact ⟨q, hq, hqD⟩
  · exact False.elim (hqI (externalForcingFilter_compatible hG.1 hq hp))

/-- Rasiowa--Sikorski applied externally. The model may be ill-founded. -/
theorem exists_externalForcingGeneric [Countable V] {P R p : V}
    (hR : IsForcingPreorder P R) (hp : p ∈ P) :
    ∃ G : Set V, IsExternalForcingGeneric P R G ∧ p ∈ G := by
  classical
  let Q := {q : V // q ∈ P}
  let : Preorder Q :=
    { le := fun q r ↦ ⟨r.val, q.val⟩ₖ ∈ R
      le_refl := fun q ↦ hR.2.1 q.val q.property
      le_trans := fun q r s hqr hrs ↦
        hR.2.2 s.val s.property r.val r.property q.val q.property hrs hqr }
  let I := {D : V // ForcingDense P R D}
  let : Encodable I := Encodable.ofCountable I
  let ds : I → Order.Cofinal Q := fun D ↦
    { carrier := {q | q.val ∈ D.val}
      isCofinal := by
        intro q
        obtain ⟨r, hr, hrq⟩ := D.property.2 q.val q.property
        exact ⟨⟨r, D.property.1 r hr⟩, hr, hrq⟩ }
  let J := Order.idealOfCofinals (⟨p, hp⟩ : Q) ds
  let G : Set V := {q | ∃ hq : q ∈ P, (⟨q, hq⟩ : Q) ∈ J}
  have hpJ : (⟨p, hp⟩ : Q) ∈ J := Order.mem_idealOfCofinals _ _
  have hpG : p ∈ G := ⟨hp, hpJ⟩
  refine ⟨G, ⟨?_, ?_⟩, hpG⟩
  · refine ⟨fun q hq ↦ hq.choose, ⟨p, hpG⟩, ?_, ?_⟩
    · intro q hq r hr hqr
      obtain ⟨hqP, hqJ⟩ := hq
      have hl : (⟨r, hr⟩ : Q) ≤ ⟨q, hqP⟩ := hqr
      exact ⟨hr, J.lower hl hqJ⟩
    · intro q hq r hr
      obtain ⟨hqP, hqJ⟩ := hq
      obtain ⟨hrP, hrJ⟩ := hr
      obtain ⟨s, hs, hsq, hsr⟩ := J.directed (⟨q, hqP⟩ : Q) hqJ (⟨r, hrP⟩ : Q) hrJ
      exact ⟨s.val, ⟨s.property, hs⟩, hsq, hsr⟩
  · intro D hD
    obtain ⟨q, hqD, hqJ⟩ := Order.cofinal_meets_idealOfCofinals (⟨p, hp⟩ : Q) ds (⟨D, hD⟩ : I)
    exact ⟨q.val, ⟨q.property, hqJ⟩, hqD⟩

end ZFVP
