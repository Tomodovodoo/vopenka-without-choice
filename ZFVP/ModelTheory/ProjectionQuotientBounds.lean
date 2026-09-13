import ZFVP.ModelTheory.ProjectionQuotient
import ZFVP.SetTheory.ForcingRelativeClosure
import ZFVP.SetTheory.ForcingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- A ground directed family has a quotient lower bound whenever its projections
have a common lower bound in the intermediate generic filter. -/
theorem projectionQuotient_ground_bound (A : ForcingContext V) {Q S π I f p : V}
    (hπ : π ∈ A.P ^ Q)
    (hc : IsForcingRelativeDirectedClosedAt A.P A.R Q S π I)
    (hf : IsForcingDirectedFamily Q S I f) (hp : p ∈ A.G)
    (hb : ∀ i ∈ I, ⟨p, π ‘ (f ‘ i)⟩ₖ ∈ A.R) :
    ∃ q ∈ Q, π ‘ q = p ∧ A.check q ∈ A.projectionQuotient Q π ∧
      ∀ i ∈ I, ⟨A.check q, A.check (f ‘ i)⟩ₖ ∈ A.projectionQuotientOrder Q S π := by
  obtain ⟨q, hq, hbound, he⟩ := hc f hf p (A.generic.1.1 p hp) hb
  have hqG := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hq, he.symm ▸ hp⟩
  refine ⟨q, hq, he, hqG, ?_⟩
  intro i hi
  have hfi := function_value_mem hf.1 hi
  have hfiG := A.generic.1.2.2.1 p hp (π ‘ (f ‘ i))
    (function_value_mem hπ hfi) (hb i hi)
  exact (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
    ⟨A.check_kpair q (f ‘ i) ▸ (A.check_mem_iff _ _).mpr (hbound i hi),
      hqG, (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hfi, hfiG⟩⟩

/-- A ground family can bound an intermediate sequence without representing it
exactly. The cover and the common generic projection are separate hypotheses. -/
theorem projectionQuotient_bound_of_ground_cover (A : ForcingContext V)
    {Q S π I f p : V} {α z : A.Model}
    (hπ : π ∈ A.P ^ Q) (hS : IsForcingPreorder Q S)
    (hc : IsForcingRelativeDirectedClosedAt A.P A.R Q S π I)
    (hf : IsForcingDirectedFamily Q S I f) (hp : p ∈ A.G)
    (hb : ∀ i ∈ I, ⟨p, π ‘ (f ‘ i)⟩ₖ ∈ A.R)
    (hz : z ∈ A.projectionQuotient Q π ^ α)
    (hcover : ∀ a ∈ α, ∃ i ∈ I,
      ⟨A.check (f ‘ i), z ‘ a⟩ₖ ∈ A.projectionQuotientOrder Q S π) :
    ∃ q ∈ A.projectionQuotient Q π,
      ∀ a ∈ α, ⟨q, z ‘ a⟩ₖ ∈ A.projectionQuotientOrder Q S π := by
  obtain ⟨q, _, _, hq, hbound⟩ := A.projectionQuotient_ground_bound hπ hc hf hp hb
  refine ⟨A.check q, hq, ?_⟩
  intro a ha
  obtain ⟨i, hi, hia⟩ := hcover a ha
  have hqi := hbound i hi
  have hfi := ((A.projectionQuotientOrder_pair_iff Q S π _ _).mp hqi).2.2
  exact (A.projectionQuotient_preorder hπ hS).2.2 _ hq _ hfi _
    (function_value_mem hz ha) hqi hia

end ForcingContext
end ZFVP
