import ZFVP.ModelTheory.TwoStepProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The canonical two-step lift keeps the second name and replaces the base condition. -/
noncomputable def twoStepStronger (a p : V) : V := ⟨p, kpair.π₂ a⟩ₖ

instance twoStepStronger_definable : ℒₛₑₜ-function₂[V] twoStepStronger := by
  unfold twoStepStronger
  definability

theorem twoStepStronger_lift {P R Q S t one a p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t)
    (ha : a ∈ twoStepConditions P R Q t) (hp : p ∈ P)
    (hle : ⟨p, kpair.π₁ a⟩ₖ ∈ R) :
    twoStepStronger a p ∈ twoStepConditions P R Q t ∧
      ⟨twoStepStronger a p, a⟩ₖ ∈ twoStepOrder P R Q S t ∧
      (twoStepProjection P R Q t) ‘ (twoStepStronger a p) = p := by
  obtain ⟨q, hq, τ, hτ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
  simp only [kpair.π₁_kpair] at hle
  have hpm := atomicMembership_mono hR hm hp hle
  have hr : ⟨p, τ⟩ₖ ∈ twoStepConditions P R Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hp, hτ, hpm⟩
  simp only [twoStepStronger, kpair.π₂_kpair]
  refine ⟨hr, (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr ⟨hr, ha, ?_, ?_⟩, ?_⟩
  · simpa only [kpair.π₁_kpair] using hle
  · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      forcedPreorder_refl hR htop hp ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩
        ⟨τ, h.name hτ⟩ (h.preorder p hp) hpm
  · rw [twoStepProjection_value hr, kpair.π₁_kpair]

theorem twoStepStronger_comp (a p q : V) :
    twoStepStronger (twoStepStronger a p) q = twoStepStronger a q := by
  simp only [twoStepStronger, kpair.π₂_kpair]

theorem twoStepStronger_section (p q t : V) :
    twoStepStronger ⟨p, t⟩ₖ q = ⟨q, t⟩ₖ := by
  simp only [twoStepStronger, kpair.π₂_kpair]

end ZFVP
