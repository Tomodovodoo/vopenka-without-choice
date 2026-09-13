import ZFVP.ModelTheory.ElementaryRange
import ZFVP.ModelTheory.RankEmbeddingPairPreimages

/-! Function closure of a small rank embedding's range. Pulling a function
back through the inverse graph gives a function in the source rank. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_range_function_closed {k l : ℕ} {ν η f c δ β : V}
    (hν : Cn (k + 1) ν) (hη : Cn (l + 1) η)
    (hj : IsCodedMembershipEmbedding (hierarchy ν) (hierarchy η) f)
    (hc : IsCriticalPoint (hierarchy ν) f c) (hδc : δ ∈ c)
    (hβ : IsOrdinal β) (hβν : β ∈ ν) :
    (range f ∩ hierarchy (f ‘ β)) ^ (hierarchy δ) ⊆ range f := by
  let := hν.ordinal
  let := hη.ordinal
  let := hc.ordinal
  let := IsOrdinal.of_mem hδc
  let := hβ
  let := hierarchy_transitive ν
  let := hierarchy_transitive η
  let := hierarchy_transitive c
  let := IsFunction.of_mem hj.function
  have hβV := ordinal_subset_hierarchy ν β hβν
  have hVβ := hierarchy_mem hβν
  have hVc := hν.hierarchy_closed hc.ordinal hc.mem_domain
  have hVδc : hierarchy δ ∈ hierarchy c := hierarchy_mem hδc
  have hVδ := (hierarchy_transitive ν).mem_trans hVδc hVc
  have hfixed := rankEmbedding_fixed_below_criticalPoint hν hη hj hc
  have hfixδ : f ‘ (hierarchy δ) = hierarchy δ := hfixed _ hVδc
  have hmapβ := (rankEmbedding_value_hierarchy hν hη hj hβ hβV).2
  have hinv := converseGraph_mem_function hj.function hj.injective
  intro h hh
  let := IsFunction.of_mem hh
  have hvalue (u : V) (hu : u ∈ hierarchy δ) :
      (converseGraph f) ‘ (h ‘ u) ∈ hierarchy β := by
    obtain ⟨hur, huα⟩ := mem_inter_iff.mp (function_value_mem hh hu)
    have hsrc := function_value_mem hinv hur
    apply (hj.value_mem_iff hsrc hVβ).mp
    rw [value_converseGraph_value hj.function hj.injective hur, hmapβ]
    exact huα
  let g := definableGraph (hierarchy δ) (fun u ↦ (converseGraph f) ‘ (h ‘ u)) (by definability)
  have hg : g ∈ (hierarchy β) ^ (hierarchy δ) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ hvalue
  have hgV := (hierarchy_transitive ν).mem_trans hg
    (function_mem_hierarchy_limit hν.successor_closed hVδ hVβ)
  have hjg := hj.value_function hgV hVδ hVβ hg
  rw [hfixδ, hmapβ] at hjg
  let := IsFunction.of_mem hg
  let := IsFunction.of_mem hjg
  have he : f ‘ g = h := by
    apply functions_eq_of_domain_values
      (by rw [domain_eq_of_mem_function hjg, domain_eq_of_mem_function hh])
    intro u hu
    have huδ : u ∈ hierarchy δ := domain_eq_of_mem_function hjg ▸ hu
    have huC := (hierarchy_transitive c).mem_trans huδ hVδc
    have heval := hj.value_apply hgV hVδ (IsFunction.of_mem hg) (domain_eq_of_mem_function hg) huδ
    rw [hfixed u huC, show g ‘ u = (converseGraph f) ‘ (h ‘ u) from
      value_definableGraph _ _ _ huδ,
      value_converseGraph_value hj.function hj.injective
        (mem_inter_iff.mp (function_value_mem hh huδ)).1] at heval
    exact heval
  exact he ▸ value_mem_range hj.function hgV

end ZFVP
