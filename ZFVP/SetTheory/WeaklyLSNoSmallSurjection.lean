import ZFVP.SetTheory.WeaklyLSNoSurjection
import ZFVP.SetTheory.SmallCollapseSurjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- No member of `Vκ` surjects onto a weakly LS cardinal `κ`. -/
theorem IsWeaklyLSCardinal.no_small_surjection {κ x f : V}
    (hκ : IsWeaklyLSCardinal κ) (hx : x ∈ hierarchy κ)
    (hf : f ∈ κ ^ x) : range f ≠ κ := by
  intro hr
  have : IsOrdinal κ := hκ.1.1
  have hγ : rank x ∈ κ := (mem_hierarchy_iff_rank_mem x κ).mp hx
  obtain ⟨e, he, hre⟩ := surjection_extension (subset_hierarchy_rank x) hf hr
    (show IsNonempty κ from ⟨ω, hκ.2.1⟩)
  exact hκ.no_surjection hγ he hre

end ZFVP
