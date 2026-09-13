import ZFVP.SetTheory.SmallCollapseSurjection
import ZFVP.SetTheory.RankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem power_surjection {A D e : V} (he : e ∈ A ^ D) (hre : range e = A) :
    ∃ g ∈ (power A) ^ (power D), range g = power A := by
  let I : V → V := fun S ↦ range (e ↾ S)
  have hI : ℒₛₑₜ-function₁ I := by unfold I; definability
  have hmap : ∀ S ∈ power D, I S ∈ power A := by
    intro S hS
    rw [mem_power_iff]
    intro a ha
    obtain ⟨d, hd⟩ := mem_range_iff.mp ha
    have hde : ⟨d, a⟩ₖ ∈ e := (kpair_mem_restrict_iff.mp hd).1
    exact (mem_of_mem_functions he hde).2
  let g := definableGraph (power D) I hI
  have hg := definableGraph_mem_function_of_mapsTo (power D) (power A) I hI hmap
  refine ⟨g, hg, SetTheory.subset_antisymm (range_subset_of_mem_function hg) ?_⟩
  intro S hS
  let T := {d ∈ D ; e ‘ d ∈ S}
  have hT : T ∈ power D := mem_power_iff.mpr (fun d hd ↦ (mem_sep_iff.mp hd).1)
  have : IsFunction e := IsFunction.of_mem he
  have hIT : I T = S := by
    apply SetTheory.subset_antisymm
    · intro a ha
      obtain ⟨d, hd⟩ := mem_range_iff.mp ha
      obtain ⟨hde, hdT⟩ := kpair_mem_restrict_iff.mp hd
      exact (value_eq_of_kpair_mem hde) ▸ (mem_sep_iff.mp hdT).2
    · intro a ha
      obtain ⟨d, hd⟩ := mem_range_iff.mp (hre.symm ▸ (mem_power_iff.mp hS a ha))
      exact mem_range_of_kpair_mem (kpair_mem_restrict_iff.mpr
        ⟨hd, mem_sep_iff.mpr ⟨(mem_of_mem_functions he hd).1,
          (value_eq_of_kpair_mem hd).symm ▸ ha⟩⟩)
  exact mem_range_of_kpair_mem ((pair_mem_definableGraph_iff (power D) I hI T S).mpr
    ⟨hT, hIT.symm⟩)

theorem product_surjection {A D e P : V} (he : e ∈ A ^ D) (hre : range e = A) :
    ∃ g ∈ (P ×ˢ A) ^ (P ×ˢ D), range g = P ×ˢ A := by
  let I : V → V := fun z ↦ ⟨kpair.π₁ z, e ‘ (kpair.π₂ z)⟩ₖ
  have hI : ℒₛₑₜ-function₁ I := by unfold I; definability
  have hmap : ∀ z ∈ P ×ˢ D, I z ∈ P ×ˢ A := by
    intro z hz
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_prod_iff.mp hz
    simpa only [I, kpair.π₁_kpair, kpair.π₂_kpair, kpair_mem_iff] using
      And.intro hp (function_value_mem he hd)
  have hg := definableGraph_mem_function_of_mapsTo (P ×ˢ D) (P ×ˢ A) I hI hmap
  refine ⟨_, hg, SetTheory.subset_antisymm (range_subset_of_mem_function hg) ?_⟩
  intro z hz
  obtain ⟨p, hp, a, ha, rfl⟩ := mem_prod_iff.mp hz
  obtain ⟨d, hd⟩ := mem_range_iff.mp (hre.symm ▸ ha)
  have : IsFunction e := IsFunction.of_mem he
  apply mem_range_of_kpair_mem
  apply (pair_mem_definableGraph_iff (P ×ˢ D) I hI _ _).mpr
  refine ⟨kpair_mem_iff.mpr ⟨hp, (mem_of_mem_functions he hd).1⟩, ?_⟩
  simp only [I, kpair.π₁_kpair, kpair.π₂_kpair, value_eq_of_kpair_mem hd]

theorem rank_product_power_surjection {κ ν δ A e : V} [IsOrdinal κ]
    (hκ : ∀ ξ ∈ κ, succ ξ ∈ κ) (hν : ν ∈ κ) (hδ : δ ∈ κ)
    (he : e ∈ A ^ (hierarchy δ)) (hre : range e = A) :
    ∃ ε ∈ κ, ∃ g ∈ (power ((hierarchy ν) ×ˢ A)) ^ (hierarchy ε),
      range g = power ((hierarchy ν) ×ˢ A) := by
  have : IsOrdinal ν := IsOrdinal.of_mem hν
  have : IsOrdinal δ := IsOrdinal.of_mem hδ
  have hcommon : ∃ β ∈ κ, hierarchy ν ⊆ hierarchy β ∧ hierarchy δ ⊆ hierarchy β := by
    rcases IsOrdinal.subset_or_supset ν δ with h | h
    · exact ⟨δ, hδ, hierarchy_mono h, subset_refl _⟩
    · exact ⟨ν, hν, subset_refl _, hierarchy_mono h⟩
  obtain ⟨β, hβ, hνβ, hδβ⟩ := hcommon
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  obtain ⟨q, hq, hrq⟩ := product_surjection (P := hierarchy ν) he hre
  obtain ⟨g, hg, hrg⟩ := power_surjection hq hrq
  have hdom : power ((hierarchy ν) ×ˢ (hierarchy δ)) ⊆ hierarchy (succ (succ (succ β))) := by
    intro S hS
    rw [hierarchy_succ, mem_power_iff]
    intro z hz
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_prod_iff.mp (mem_power_iff.mp hS z hz)
    exact kpair_mem_hierarchy_succ_succ (hνβ p hp) (hδβ d hd)
  obtain ⟨f, hf, hrf⟩ := surjection_extension hdom hg hrg
    (show IsNonempty (power ((hierarchy ν) ×ˢ A)) from ⟨∅, by simp⟩)
  exact ⟨succ (succ (succ β)), hκ _ (hκ _ (hκ _ hβ)), f, hf, hrf⟩

end ZFVP
