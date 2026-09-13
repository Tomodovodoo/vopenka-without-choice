import ZFVP.SetTheory.CohenRepresentativeSupport
import ZFVP.SetTheory.FiniteSupportStabilization

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def cohenSupportStabilizers (τ : V) : V :=
  {p ∈ cohenConditions (ω : V) ;
    ∀ q ∈ cohenConditions (ω : V), ⟨q, p⟩ₖ ∈ cohenOrder (ω : V) →
      cohenRepresentativeLeastSupport τ q = cohenRepresentativeLeastSupport τ p}

theorem cohenSupportStabilizers_dense {τ : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ) :
    ForcingDense (cohenConditions (ω : V)) (cohenOrder (ω : V)) (cohenSupportStabilizers τ) := by
  refine ⟨fun _ hp ↦ (mem_sep_iff.mp hp).1, ?_⟩
  intro p hp
  obtain ⟨q, hq, hqp, hstable⟩ := finite_support_stabilization
    (cohen_poset (ω : V)).1 (cohenRepresentativeLeastSupport τ) (by definability)
    hp (cohenRepresentativeLeastSupport_isSupport hτ hp).finite
    (fun _ _ _ _ hrq ↦ cohenRepresentativeLeastSupport_mono hτ hrq)
  exact ⟨q, mem_sep_iff.mpr ⟨hq, hstable⟩, hqp⟩

end ZFVP
