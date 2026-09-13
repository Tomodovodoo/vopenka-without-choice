import ZFVP.SetTheory.AtomicMembership
import ZFVP.SetTheory.ForcingNames

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A retraction onto a subforcing, with exact lifting of stronger conditions. -/
structure IsForcingRetraction (P R Q S π : V) : Prop where
  maps : π ∈ P ^ Q
  inclusion : P ⊆ Q
  fixes : ∀ p ∈ P, π ‘ p = p
  monotone : ∀ p ∈ Q, ∀ q ∈ Q, ⟨p, q⟩ₖ ∈ S → ⟨π ‘ p, π ‘ q⟩ₖ ∈ R
  below : ∀ q ∈ Q, ∀ p ∈ P, ⟨q, p⟩ₖ ∈ S ↔ ⟨π ‘ q, p⟩ₖ ∈ R
  lift : ∀ q ∈ Q, ∀ p ∈ P, ⟨p, π ‘ q⟩ₖ ∈ R →
    ∃ r ∈ Q, ⟨r, q⟩ₖ ∈ S ∧ π ‘ r = p

theorem IsForcingName.mono {P Q τ : V} (hτ : IsForcingName P τ) (hPQ : P ⊆ Q) :
    IsForcingName Q τ := by
  intro σ hσ z hz
  obtain ⟨υ, p, hp, he⟩ := hτ σ hσ z hz
  exact ⟨υ, p, hPQ p hp, he⟩

set_option maxHeartbeats 800000 in
theorem IsForcingRetraction.atomicEquality_iff {P R Q S π σ τ p : V}
    (h : IsForcingRetraction P R Q S π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ Q) : p ∈ atomicEquality Q S σ τ ↔ π ‘ p ∈ atomicEquality P R σ τ := by
  have hi := forcingName_induction P
    (fun σ ↦ ∀ τ, IsForcingName P τ → ∀ p ∈ Q,
      p ∈ atomicEquality Q S σ τ ↔ π ‘ p ∈ atomicEquality P R σ τ)
    (by definability) ?_ σ hσ
  · exact hi τ hτ p hp
  intro σ hσ ih τ hτ p hp
  constructor
  · intro he
    obtain ⟨_, hl, hr⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp he
    apply (mem_atomicEquality_iff _ _ _ _ _).mpr
    refine ⟨function_value_mem h.maps hp, ?_, ?_⟩
    · intro υ s hs q hq hqp hqs
      obtain ⟨a, ha, hap, heq⟩ := h.lift p hp q hq hqp
      have has := (h.below a ha s (forcingName_condition hσ hs)).mpr (heq.symm ▸ hqs)
      obtain ⟨r, hrQ, hra, ν, t, ht, hrt, hE⟩ := hl υ s hs a ha hap has
      refine ⟨π ‘ r, function_value_mem h.maps hrQ, ?_, ν, t, ht,
        (h.below r hrQ t (forcingName_condition hτ ht)).mp hrt,
        (ih υ s hs ν (forcingName_subname hτ ht) r hrQ).mp hE⟩
      simpa only [heq] using h.monotone r hrQ a ha hra
    · intro ν t ht q hq hqp hqt
      obtain ⟨a, ha, hap, heq⟩ := h.lift p hp q hq hqp
      have hat := (h.below a ha t (forcingName_condition hτ ht)).mpr (heq.symm ▸ hqt)
      obtain ⟨r, hrQ, hra, υ, s, hs, hrs, hE⟩ := hr ν t ht a ha hap hat
      refine ⟨π ‘ r, function_value_mem h.maps hrQ, ?_, υ, s, hs,
        (h.below r hrQ s (forcingName_condition hσ hs)).mp hrs,
        (ih υ s hs ν (forcingName_subname hτ ht) r hrQ).mp hE⟩
      simpa only [heq] using h.monotone r hrQ a ha hra
  · intro he
    obtain ⟨_, hl, hr⟩ := (mem_atomicEquality_iff _ _ _ _ _).mp he
    apply (mem_atomicEquality_iff _ _ _ _ _).mpr
    refine ⟨hp, ?_, ?_⟩
    · intro υ s hs q hq hqp hqs
      obtain ⟨r, hrP, hrq, ν, t, ht, hrt, hE⟩ := hl υ s hs (π ‘ q)
        (function_value_mem h.maps hq) (h.monotone q hq p hp hqp)
        ((h.below q hq s (forcingName_condition hσ hs)).mp hqs)
      obtain ⟨a, ha, haq, hea⟩ := h.lift q hq r hrP hrq
      exact ⟨a, ha, haq, ν, t, ht,
        (h.below a ha t (forcingName_condition hτ ht)).mpr (hea.symm ▸ hrt),
        (ih υ s hs ν (forcingName_subname hτ ht) a ha).mpr (hea.symm ▸ hE)⟩
    · intro ν t ht q hq hqp hqt
      obtain ⟨r, hrP, hrq, υ, s, hs, hrs, hE⟩ := hr ν t ht (π ‘ q)
        (function_value_mem h.maps hq) (h.monotone q hq p hp hqp)
        ((h.below q hq t (forcingName_condition hτ ht)).mp hqt)
      obtain ⟨a, ha, haq, hea⟩ := h.lift q hq r hrP hrq
      exact ⟨a, ha, haq, υ, s, hs,
        (h.below a ha s (forcingName_condition hσ hs)).mpr (hea.symm ▸ hrs),
        (ih υ s hs ν (forcingName_subname hτ ht) a ha).mpr (hea.symm ▸ hE)⟩

theorem IsForcingRetraction.atomicMembership_iff {P R Q S π σ τ p : V}
    (h : IsForcingRetraction P R Q S π) (hσ : IsForcingName P σ) (hτ : IsForcingName P τ)
    (hp : p ∈ Q) : p ∈ atomicMembership Q S σ τ ↔ π ‘ p ∈ atomicMembership P R σ τ := by
  constructor
  · intro hm
    obtain ⟨_, hm⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hm
    apply (mem_atomicMembership_iff _ _ _ _ _).mpr
    refine ⟨function_value_mem h.maps hp, fun q hq hqp ↦ ?_⟩
    obtain ⟨a, ha, hap, hea⟩ := h.lift p hp q hq hqp
    obtain ⟨r, hr, hra, ν, s, hs, hrs, hE⟩ := hm a ha hap
    refine ⟨π ‘ r, function_value_mem h.maps hr, ?_, ν, s, hs,
      (h.below r hr s (forcingName_condition hτ hs)).mp hrs,
      (h.atomicEquality_iff hσ (forcingName_subname hτ hs) hr).mp hE⟩
    simpa only [hea] using h.monotone r hr a ha hra
  · intro hm
    obtain ⟨_, hm⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hm
    apply (mem_atomicMembership_iff _ _ _ _ _).mpr
    refine ⟨hp, fun q hq hqp ↦ ?_⟩
    obtain ⟨r, hr, hrq, ν, s, hs, hrs, hE⟩ := hm (π ‘ q)
      (function_value_mem h.maps hq) (h.monotone q hq p hp hqp)
    obtain ⟨a, ha, haq, hea⟩ := h.lift q hq r hr hrq
    exact ⟨a, ha, haq, ν, s, hs,
      (h.below a ha s (forcingName_condition hτ hs)).mpr (hea.symm ▸ hrs),
      (h.atomicEquality_iff hσ (forcingName_subname hτ hs) ha).mpr (hea.symm ▸ hE)⟩

end ZFVP
