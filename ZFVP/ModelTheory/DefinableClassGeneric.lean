import ZFVP.ModelTheory.SetDomainDefinableClasses
import ZFVP.ModelTheory.ForcingGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def IsExternalClassForcingFilter {W : Type*} (P : W → Prop) (R : W → W → Prop) (G : Set W) : Prop :=
  (∀ p ∈ G, P p) ∧ G.Nonempty ∧
    (∀ p ∈ G, ∀ q, P q → R p q → q ∈ G) ∧
    ∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, R r p ∧ R r q

def ClassForcingDense {W : Type*} (P : W → Prop) (R : W → W → Prop) (D : W → Prop) : Prop :=
  (∀ p, D p → P p) ∧ ∀ p, P p → ∃ q, D q ∧ R q p

/-- Genericity against all first-order definable dense classes with parameters.
This property does not itself assert definability of the carrier or order. -/
def IsGenericForDefinableDenseClasses {W : Type*} [SetStructure W]
    (P : W → Prop) (R : W → W → Prop) (G : Set W) : Prop :=
  IsExternalClassForcingFilter P R G ∧
    ∀ D : W → Prop, (ℒₛₑₜ-predicate D) → ClassForcingDense P R D → ∃ p ∈ G, D p

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem externalForcingGeneric_definableClasses {U P R : V} {G : Set V}
    (hP : P ⊆ U) (hG : IsExternalForcingGeneric P R G) :
    IsGenericForDefinableDenseClasses
      (fun p : SetDomain U ↦ p.val ∈ P) (fun p q ↦ ⟨p.val, q.val⟩ₖ ∈ R)
      {p : SetDomain U | p.val ∈ G} := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun p hp ↦ hG.1.1 p.val hp, ?_, ?_, ?_⟩
    · obtain ⟨p, hp⟩ := hG.1.2.1
      exact ⟨⟨p, hP p (hG.1.1 p hp)⟩, hp⟩
    · intro p hp q hq hpq
      exact hG.1.2.2.1 p.val hp q.val hq hpq
    · intro p hp q hq
      obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p.val hp q.val hq
      exact ⟨⟨r, hP r (hG.1.1 r hr)⟩, hr, hrp, hrq⟩
  · intro D hD hd
    obtain ⟨d, hdU, he⟩ := setDomain_definable_set U D hD
    have hdense : ForcingDense P R d := by
      constructor
      · intro p hp
        exact hd.1 ⟨p, hdU p hp⟩ ((he ⟨p, hdU p hp⟩).mp hp)
      · intro p hp
        obtain ⟨q, hq, hqp⟩ := hd.2 ⟨p, hP p hp⟩ hp
        exact ⟨q.val, (he q).mpr hq, hqp⟩
    obtain ⟨p, hp, hpd⟩ := hG.2 d hdense
    exact ⟨⟨p, hdU p hpd⟩, hp, (he ⟨p, hdU p hpd⟩).mp hpd⟩

end ZFVP
