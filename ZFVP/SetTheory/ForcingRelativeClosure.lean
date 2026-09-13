import ZFVP.SetTheory.ForcingDirectedMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Directed lower bounds with an exactly prescribed projected condition. -/
def IsForcingRelativeDirectedClosedAt (P R Q S π I : V) : Prop :=
  ∀ f, IsForcingDirectedFamily Q S I f → ∀ p ∈ P,
    (∀ i ∈ I, ⟨p, π ‘ (f ‘ i)⟩ₖ ∈ R) →
      ∃ q ∈ Q, (∀ i ∈ I, ⟨q, f ‘ i⟩ₖ ∈ S) ∧ π ‘ q = p

instance isForcingRelativeDirectedClosedAt_definable : Language.DefinableRel₆ ℒₛₑₜ
    (IsForcingRelativeDirectedClosedAt (V := V)) := by
  unfold IsForcingRelativeDirectedClosedAt
  definability

theorem forcingRelativeDirectedClosedAt_identity (P R I : V) :
    IsForcingRelativeDirectedClosedAt P R P R (identity P) I := by
  intro f hf p hp hb
  refine ⟨p, hp, ?_, identity_value hp⟩
  intro i hi
  simpa only [identity_value (function_value_mem hf.1 hi)] using hb i hi

theorem IsForcingRelativeDirectedClosedAt.comp {P R Q S T U π ρ I : V}
    (hPQ : IsForcingRelativeDirectedClosedAt P R Q S π I)
    (hQT : IsForcingRelativeDirectedClosedAt Q S T U ρ I)
    (hπ : π ∈ P ^ Q) (hρ : ρ ∈ Q ^ T)
    (hm : ∀ x ∈ T, ∀ y ∈ T, ⟨x, y⟩ₖ ∈ U → ⟨ρ ‘ x, ρ ‘ y⟩ₖ ∈ S) :
    IsForcingRelativeDirectedClosedAt P R T U (compose ρ π) I := by
  intro f hf p hp hb
  have hg := hf.map hρ hm
  have hpg : ∀ i ∈ I, ⟨p, π ‘ ((compose f ρ) ‘ i)⟩ₖ ∈ R := by
    intro i hi
    rw [value_compose_of_mem_function hf.1 hρ hi]
    simpa only [value_compose_of_mem_function hρ hπ (function_value_mem hf.1 hi)] using hb i hi
  obtain ⟨q, hq, hqg, hqp⟩ := hPQ _ hg p hp hpg
  obtain ⟨r, hr, hrb, hrq⟩ := hQT f hf q hq (by
    intro i hi
    simpa only [value_compose_of_mem_function hf.1 hρ hi] using hqg i hi)
  refine ⟨r, hr, hrb, ?_⟩
  rw [value_compose_of_mem_function hρ hπ hr, hrq, hqp]

end ZFVP
