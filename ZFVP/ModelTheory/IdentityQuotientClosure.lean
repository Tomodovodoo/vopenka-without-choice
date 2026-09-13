import ZFVP.ModelTheory.ProjectionQuotient
import ZFVP.SetTheory.ForcingSeparativeOrder
import ZFVP.SetTheory.ForcingClosure
import ZFVP.SetTheory.ForcingSectionThread

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem identityQuotient_compatible (A : ForcingContext V) {π : V}
    (hπ : π ∈ A.P ^ A.P) (he : ∀ p ∈ A.P, π ‘ p = p)
    {x y : A.Model} (hx : x ∈ A.projectionQuotient A.P π)
    (hy : y ∈ A.projectionQuotient A.P π) :
    ForcingCompatible (A.projectionQuotient A.P π)
      (A.projectionQuotientOrder A.P A.R π) x y := by
  obtain ⟨p, hp, hpG, rfl⟩ := (A.mem_projectionQuotient_iff hπ x).mp hx
  obtain ⟨q, hq, hqG, rfl⟩ := (A.mem_projectionQuotient_iff hπ y).mp hy
  rw [he p hp] at hpG
  rw [he q hq] at hqG
  obtain ⟨r, hrG, hrp, hrq⟩ := A.generic.1.2.2.2 p hpG q hqG
  have hr := A.generic.1.1 r hrG
  have hr' := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hr, (he r hr).symm ▸ hrG⟩
  refine ⟨A.check r, hr', ?_, ?_⟩
  · exact (A.projectionQuotientOrder_pair_iff A.P A.R π _ _).mpr
      ⟨A.check_kpair r p ▸ (A.check_mem_iff _ _).mpr hrp, hr', hx⟩
  · exact (A.projectionQuotientOrder_pair_iff A.P A.R π _ _).mpr
      ⟨A.check_kpair r q ▸ (A.check_mem_iff _ _).mpr hrq, hr', hy⟩

theorem identityQuotient_separative (A : ForcingContext V) {π : V}
    (hπ : π ∈ A.P ^ A.P) (he : ∀ p ∈ A.P, π ‘ p = p)
    {x y : A.Model} (hx : x ∈ A.projectionQuotient A.P π)
    (hy : y ∈ A.projectionQuotient A.P π) :
    ⟨x, y⟩ₖ ∈ forcingSeparativeOrder (A.projectionQuotient A.P π)
      (A.projectionQuotientOrder A.P A.R π) := by
  exact (kpair_mem_forcingSeparativeOrder _ _ _ _).mpr
    ⟨hx, hy, fun _ hz _ ↦ A.identityQuotient_compatible hπ he hz hy⟩

/-- The diagonal quotient starts the closure induction at every intermediate
ordinal, including sequences which do not belong to the ground model. -/
theorem identityQuotient_separative_closedAt (A : ForcingContext V) {π : V}
    (hπ : π ∈ A.P ^ A.P) (he : ∀ p ∈ A.P, π ‘ p = p) (α : A.Model) :
    IsForcingClosedAt (A.projectionQuotient A.P π)
      (forcingSeparativeOrder (A.projectionQuotient A.P π)
        (A.projectionQuotientOrder A.P A.R π)) α := by
  intro f hf
  obtain ⟨p, hpG⟩ := A.generic.1.2.1
  have hp := A.generic.1.1 p hpG
  have hp' := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hp, (he p hp).symm ▸ hpG⟩
  exact ⟨A.check p, hp', fun i hi ↦
    A.identityQuotient_separative hπ he hp' (function_value_mem hf.1 hi)⟩

/-- Every stage is the initial point of its own quotient closure induction. -/
theorem splitSystem_diagonal_quotient_closedAt (A : ForcingContext V)
    {θ P π E i : V} (h : IsSplitForcingSystem θ P π E)
    (hi : i ∈ θ) (hP : A.P = P ‘ i)
    (hπ : (π ‘ ⟨i, i⟩ₖ) ∈ (P ‘ i) ^ (P ‘ i)) (α : A.Model) :
    IsForcingClosedAt (A.projectionQuotient (P ‘ i) (π ‘ ⟨i, i⟩ₖ))
      (forcingSeparativeOrder (A.projectionQuotient (P ‘ i) (π ‘ ⟨i, i⟩ₖ))
        (A.projectionQuotientOrder (P ‘ i) A.R (π ‘ ⟨i, i⟩ₖ))) α := by
  rw [← hP]
  apply A.identityQuotient_separative_closedAt
  · rw [hP]
    exact hπ
  · intro p hp
    exact h.projId hi (hP ▸ hp)

end ForcingContext
end ZFVP
