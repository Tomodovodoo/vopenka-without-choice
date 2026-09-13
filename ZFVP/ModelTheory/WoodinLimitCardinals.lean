import ZFVP.ModelTheory.WoodinIterationInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinLimitCardinal (K : V) : V := ⋃ˢ range K

instance woodinLimitCardinal_definable : ℒₛₑₜ-function₁[V] woodinLimitCardinal := by
  unfold woodinLimitCardinal
  definability

theorem IsIterationTable.mem_function {θ f A : V} (h : IsIterationTable θ f)
    (hm : ∀ i ∈ θ, f ‘ i ∈ A) : f ∈ A ^ θ := by
  have : IsFunction f := h.function
  have hf : f ∈ range f ^ θ := h.domain_eq ▸ IsFunction.mem_function f
  apply mem_function_of_mem_function_of_subset hf
  intro y hy
  obtain ⟨i, hi⟩ := mem_range_iff.mp hy
  exact value_eq_of_kpair_mem hi ▸ hm i (h.domain_eq ▸ mem_domain_of_kpair_mem hi)

theorem IsWoodinIteration.limitCardinal_ordinal {δ θ s K : V}
    (h : IsWoodinIteration δ θ s K) : IsOrdinal (woodinLimitCardinal K) := by
  have : IsFunction K := h.cardinals.function
  apply IsOrdinal.sUnion
  intro y hy
  obtain ⟨i, hi⟩ := mem_range_iff.mp hy
  exact value_eq_of_kpair_mem hi ▸
    (h.inaccessible i (h.cardinals.domain_eq ▸ mem_domain_of_kpair_mem hi)).1

theorem IsWoodinIteration.cardinal_subset_limit {δ θ s K i : V}
    (h : IsWoodinIteration δ θ s K) (hi : i ∈ θ) : K ‘ i ⊆ woodinLimitCardinal K := by
  have : IsFunction K := h.cardinals.function
  exact subset_sUnion_of_mem (mem_range_of_kpair_mem
    (kpair_value_mem (h.cardinals.domain_eq.symm ▸ hi)))

theorem IsWoodinIteration.cardinal_mem_limit {δ θ s K i : V}
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ) (hi : i ∈ θ) :
    K ‘ i ∈ woodinLimitCardinal K :=
  h.cardinal_subset_limit (hlim i hi) _ (h.increasing i hi (succ i) (hlim i hi) (mem_succ_self i))

theorem IsWoodinIteration.limitCardinal_cofinal {δ θ s K x : V}
    (h : IsWoodinIteration δ θ s K) (hx : x ∈ woodinLimitCardinal K) :
    ∃ i ∈ θ, x ∈ K ‘ i := by
  have : IsFunction K := h.cardinals.function
  obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
  obtain ⟨i, hi⟩ := mem_range_iff.mp hy
  exact ⟨i, h.cardinals.domain_eq ▸ mem_domain_of_kpair_mem hi,
    (value_eq_of_kpair_mem hi).symm ▸ hxy⟩

theorem IsWoodinIteration.index_subset_cardinal {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) : ∀ i ∈ θ, i ⊆ K ‘ i := by
  have hall := transfinite_induction (fun i : V ↦ i ∈ θ → i ⊆ K ‘ i) (by definability) ?_
  · intro i hi
    let := IsOrdinal.of_mem hi
    exact hall (IsOrdinal.toOrdinal i) hi
  intro i ih hi j hj
  have hjθ : j ∈ θ := IsOrdinal.toIsTransitive.mem_trans hj hi
  let := IsOrdinal.of_mem hj
  have hjK := ih (IsOrdinal.toOrdinal j) hj hjθ
  change j ⊆ K ‘ j at hjK
  have hji := h.increasing j hjθ i hi hj
  let := (h.inaccessible i hi).1
  let := (h.inaccessible j hjθ).1
  exact ordinal_mem_of_subset_mem hjK hji

theorem IsWoodinIteration.index_subset_limit {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ i ∈ θ, succ i ∈ θ) :
    θ ⊆ woodinLimitCardinal K := by
  have : IsOrdinal (woodinLimitCardinal K) := h.limitCardinal_ordinal
  intro i hi
  let := IsOrdinal.of_mem hi
  let := (h.inaccessible i hi).1
  exact ordinal_mem_of_subset_mem (h.index_subset_cardinal i hi) (h.cardinal_mem_limit hlim hi)

theorem IsWoodinIteration.limitCardinal_below {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsRegularCardinal δ) (hθ : θ ∈ δ) :
    woodinLimitCardinal K ∈ δ := by
  let := hδ.1.1
  have : IsOrdinal (woodinLimitCardinal K) := h.limitCardinal_ordinal
  obtain ⟨β, hβ, hb⟩ := regularCardinal_maps_bounded hδ hθ
    (h.cardinals.mem_function h.bounded)
  let := IsOrdinal.of_mem hβ
  apply ordinal_mem_of_subset_mem (β := β) _ hβ
  intro x hx
  obtain ⟨i, hi, hxi⟩ := h.limitCardinal_cofinal hx
  exact IsOrdinal.toIsTransitive.mem_trans hxi (hb i hi)

end ZFVP
