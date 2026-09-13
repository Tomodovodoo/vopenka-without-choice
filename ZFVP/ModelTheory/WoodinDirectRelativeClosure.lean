import ZFVP.ModelTheory.WoodinDirectIndex
import ZFVP.SetTheory.DirectLimitRelativeClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.direct_relativeDirectedClosedAt {δ θ s K i α : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) (hi : i ∈ θ) (hα : α ∈ K ‘ i)
    (hclosed : ∀ k ∈ θ, i ⊆ k → IsForcingRelativeDirectedClosedAt
      ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i) ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) α) :
    IsForcingRelativeDirectedClosedAt ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingCodeP (forcingDirectCode θ s)) ‘ θ) ((forcingCodeR (forcingDirectCode θ s)) ‘ θ)
      ((forcingCodeπ (forcingDirectCode θ s)) ‘ ⟨i, θ⟩ₖ) α := by
  have hh := forcingDirectLimit_relativeDirectedClosedAt h.code.system.split hi
    (h.short_below_direct_cofinality hlim hinac hi hα) h.code.subset_universe hclosed
    (fun j hj k hk hjk ↦ by
      let := IsOrdinal.of_mem hk
      exact h.code.system.order.projMono j hj k hk (IsOrdinal.toIsTransitive.transitive _ hjk))
    (fun k hk j hj hkj _ hp _ hq hab ↦
      h.code.system.order.secMono h.code.system.split hk hj hkj hp hq hab)
  simpa only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingFamilyNext_new,
    forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi] using hh

end ZFVP
