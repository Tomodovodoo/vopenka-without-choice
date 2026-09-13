import ZFVP.ModelTheory.WoodinCollapseRankWitness
import ZFVP.ModelTheory.ForcingModelChecks

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem check_woodinCollapseRankWitness (A : ForcingContext V) (β : V) :
    A.check (woodinCollapseRankWitness β) = woodinCollapseRankWitness (A.check β) := by
  simp only [woodinCollapseRankWitness, A.check_singleton, A.check_kpair, A.check_empty, A.check_succ]

/-- A checked one-entry witness is legal for any internal lower index above one.
Only its fixed coordinate, rather than inaccessibility, is transported. -/
theorem check_woodinCollapseRankWitness_mem_of_coordinate (A : ForcingContext V)
    {κ : A.Model} [IsOrdinal κ] {δ β : V} [IsOrdinal δ] [IsOrdinal β]
    (hκ : (1 : A.Model) ∈ κ) (hη : succ (succ β) ∈ δ) :
    A.check (woodinCollapseRankWitness β) ∈ woodinCollapse κ (A.check δ) := by
  rw [A.check_woodinCollapseRankWitness]
  apply woodinCollapseRankWitness_mem_of_coordinate hκ
  simpa only [A.check_succ] using (A.check_mem_iff _ _).mpr hη

theorem check_woodinCollapseRankWitness_mem (A : ForcingContext V)
    {κ : A.Model} [IsOrdinal κ] {δ β : V} [IsOrdinal δ]
    (hκ : (1 : A.Model) ∈ κ) (hδ : ∀ ξ ∈ δ, succ ξ ∈ δ) (hβ : β ∈ δ) :
    A.check (woodinCollapseRankWitness β) ∈ woodinCollapse κ (A.check δ) := by
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  exact A.check_woodinCollapseRankWitness_mem_of_coordinate hκ (hδ _ (hδ _ hβ))

end ForcingContext
end ZFVP
