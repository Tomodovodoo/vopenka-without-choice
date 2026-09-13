import ZFVP.SetTheory.WoodinCollapseClosedCut
import ZFVP.SetTheory.WoodinCollapseRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_bounded_predense_family {κ δ γ : V}
    (hδ : IsChoicelessInaccessible δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ)
    (hγ : γ ∈ δ) (D : V → V) (hD : ℒₛₑₜ-function₁ D)
    (hd : ∀ i ∈ γ, D i ⊆ woodinCollapse κ δ ∧
      ∀ p ∈ woodinCollapse κ δ, ∃ q ∈ D i, p ⊆ q) :
    ∃ β ∈ δ, IsOrdinal β ∧ ∀ i ∈ γ, ∀ p ∈ woodinCollapse κ δ,
      ∃ q ∈ D i, q ∈ hierarchy β ∧
        ∃ r ∈ woodinCollapse κ δ, p ⊆ r ∧ q ⊆ r := by
  let := hδ.1
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  let R := fun x q ↦ ∃ i ∈ γ, ∃ p ∈ woodinCollapse κ δ,
    x = ⟨i, p⟩ₖ ∧ q ∈ D i ∧ p ⊆ q
  have hR : ℒₛₑₜ-relation R := by unfold R; definability
  have hex : ∀ x ∈ hierarchy δ, (∃ q, R x q) → ∃ q ∈ hierarchy δ, R x q := by
    intro x _ ⟨q, hq⟩
    obtain ⟨i, hi, p, hp, hx, hqi, hpq⟩ := hq
    exact ⟨q, woodinCollapse_condition_mem_hierarchy hδ.regular
      (IsOrdinal.toIsTransitive.transitive _ hκδ) ((hd i hi).1 q hqi),
      i, hi, p, hp, hx, hqi, hpq⟩
  obtain ⟨β, hβ, ho, hγβ, hκβ, hs, hb, hc⟩ :=
    hδ.witnessClosed_above_regular hκ hκδ hγ R hR hex
  let := ho
  refine ⟨β, hβ, ho, ?_⟩
  intro i hi p hp
  let pc := woodinCollapseCut κ β p
  have hpc : pc ∈ woodinCollapse κ β := woodinCollapseCut_mem_of_successor_closed hs hp
  have hpcδ := woodinCollapse_mono (IsOrdinal.toIsTransitive.transitive _ hβ) pc hpc
  have hpcV := woodinCollapse_condition_mem_of_short_bounds hκ
    (IsOrdinal.toIsTransitive.transitive _ hκβ) hs hb hpc
  let := IsOrdinal.of_mem hi
  have hx : ⟨i, pc⟩ₖ ∈ hierarchy β := kpair_mem_hierarchy_limit hs
    (ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hi hγβ)) hpcV
  obtain ⟨q₀, hq₀, hpcq₀⟩ := (hd i hi).2 pc hpcδ
  obtain ⟨q, hqV, j, hj, s, _, heq, hq, hsq⟩ :=
    hc _ hx ⟨q₀, i, hi, pc, hpcδ, rfl, hq₀, hpcq₀⟩
  obtain ⟨rfl, rfl⟩ := kpair_inj heq
  have hqβ := woodinCollapse_mem_of_low_rank ((hd i hi).1 q hq) hqV
  exact ⟨q, hq, hqV, p ∪ q, woodinCollapse_union_of_cut_extension hκ
    (IsOrdinal.toIsTransitive.transitive _ hβ) hp hqβ hsq,
    subset_union_left _ _, subset_union_right _ _⟩

end ZFVP
