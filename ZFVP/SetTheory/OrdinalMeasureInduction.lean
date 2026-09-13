import ZFVP.SetTheory.MeasuredWellFounded
import ZFVP.SetTheory.RankBounds

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalMeasure_induction (D : V) (μ : V → V) (hμ : ℒₛₑₜ-function₁ μ)
    (hord : ∀ x ∈ D, IsOrdinal (μ x)) (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (step : ∀ x ∈ D, (∀ y ∈ D, μ y ∈ μ x → P y) → P x) : ∀ x ∈ D, P x := by
  apply projectedRank_induction D μ hμ P hP
  intro x hx ih
  have : IsOrdinal (μ x) := hord x hx
  apply step x hx
  intro y hy hyx
  have : IsOrdinal (μ y) := hord y hy
  apply ih y hy
  simpa only [rank_of_ordinal] using hyx

end ZFVP
