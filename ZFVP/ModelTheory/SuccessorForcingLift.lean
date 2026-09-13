import ZFVP.ModelTheory.TwoStepStrongerLift
import ZFVP.ModelTheory.ForcingSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Extend an earlier stronger lift through one two-step forcing. -/
noncomputable def successorForcingLiftValue (L a b : V) : V :=
  twoStepStronger a (L ‘ ⟨kpair.π₁ a, b⟩ₖ)

instance successorForcingLiftValue_definable :
    ℒₛₑₜ-function₃[V] successorForcingLiftValue := by
  unfold successorForcingLiftValue
  definability

noncomputable def successorForcingLift (C A L : V) : V :=
  definableGraph (C ×ˢ A)
    (fun z ↦ successorForcingLiftValue L (kpair.π₁ z) (kpair.π₂ z)) (by definability)

theorem successorForcingLift_value {C A L a b : V} (ha : a ∈ C) (hb : b ∈ A) :
    (successorForcingLift C A L) ‘ ⟨a, b⟩ₖ = successorForcingLiftValue L a b := by
  rw [successorForcingLift, value_definableGraph _ _ _ (mem_prod_iff.mpr ⟨a, ha, b, hb, rfl⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem successorForcingLift_lift {A B P R Q S t one π L a b : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t)
    (hπ : π ∈ A ^ P)
    (hL : ∀ x ∈ P, ∀ y ∈ A, ⟨y, π ‘ x⟩ₖ ∈ B →
      L ‘ ⟨x, y⟩ₖ ∈ P ∧ ⟨L ‘ ⟨x, y⟩ₖ, x⟩ₖ ∈ R ∧ π ‘ (L ‘ ⟨x, y⟩ₖ) = y)
    (ha : a ∈ twoStepConditions P R Q t) (hb : b ∈ A)
    (hle : ⟨b, π ‘ (kpair.π₁ a)⟩ₖ ∈ B) :
    successorForcingLiftValue L a b ∈ twoStepConditions P R Q t ∧
    ⟨successorForcingLiftValue L a b, a⟩ₖ ∈ twoStepOrder P R Q S t ∧
    (compose (twoStepProjection P R Q t) π) ‘ (successorForcingLiftValue L a b) = b := by
  have haP : kpair.π₁ a ∈ P := by
    obtain ⟨x, hx, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    simpa only [kpair.π₁_kpair] using hx
  have hl := hL _ haP b hb hle
  have hs := twoStepStronger_lift hR htop h ha hl.1 hl.2.1
  refine ⟨hs.1, hs.2.1, ?_⟩
  unfold successorForcingLiftValue
  rw [value_compose_of_mem_function (twoStep_projection hR htop h).maps hπ hs.1,
    hs.2.2, hl.2.2]

theorem successorForcingLift_project (L a b ρ : V) :
    ρ ‘ (kpair.π₁ (successorForcingLiftValue L a b)) =
      ρ ‘ (L ‘ ⟨kpair.π₁ a, b⟩ₖ) := by
  simp only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair]

/-- Old commutation equations imply commutation for the successor lift column. -/
theorem successorForcingLift_commute {L M ρ a b : V}
    (hc : ρ ‘ (L ‘ ⟨kpair.π₁ a, b⟩ₖ) = M ‘ ⟨ρ ‘ (kpair.π₁ a), b⟩ₖ) :
    ρ ‘ (kpair.π₁ (successorForcingLiftValue L a b)) =
      M ‘ ⟨ρ ‘ (kpair.π₁ a), b⟩ₖ := by
  rw [successorForcingLift_project, hc]

theorem successorForcingLift_section (L a b t : V) :
    successorForcingLiftValue L ⟨a, t⟩ₖ b = ⟨L ‘ ⟨a, b⟩ₖ, t⟩ₖ := by
  simp only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair, kpair.π₂_kpair]

end ZFVP
