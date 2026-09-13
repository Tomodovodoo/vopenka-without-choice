import ZFVP.SetTheory.WoodinCollapseReindex

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_restrict_union_disjoint {p q D : V} [IsFunction p] [IsFunction q]
    (hp : ∀ x ∈ domain p, x ∉ D) (hq : domain q ⊆ D) : (p ∪ q) ↾ D = q := by
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hz, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
    rcases mem_union_iff.mp hz with hz | hz
    · exact False.elim (hp x (mem_domain_of_kpair_mem hz) hx)
    · exact hz
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact kpair_mem_restrict_iff.mpr
      ⟨mem_union_iff.mpr (Or.inr hz), hq x (mem_domain_of_kpair_mem hz)⟩

theorem function_union_restrict_complement {p q D : V} [IsFunction p] [IsFunction q]
    (hpq : p ⊆ q) (hqD : domain q ⊆ D) : p ∪ (q ↾ (D \ domain p)) = q := by
  classical
  apply mem_ext
  intro z
  constructor
  · intro hz
    rcases mem_union_iff.mp hz with hz | hz
    · exact hpq _ hz
    · exact (mem_restrict_iff.mp hz).1
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    by_cases hx : x ∈ domain p
    · obtain ⟨t, hxt⟩ := mem_domain_iff.mp hx
      have ht : t = y := IsFunction.unique (hpq _ hxt) hz
      exact mem_union_iff.mpr (Or.inl (ht ▸ hxt))
    · exact mem_union_iff.mpr (Or.inr (kpair_mem_restrict_iff.mpr
        ⟨hz, by simp [hqD x (mem_domain_of_kpair_mem hz), hx]⟩))

noncomputable def collapseConeEncode (κ δ p q : V) : V :=
  p ∪ permutedGraph (converseGraph (collapseCoordinateMap κ δ p)) q

noncomputable def collapseConeDecode (κ δ p r : V) : V :=
  permutedGraph (collapseCoordinateMap κ δ p) (r ↾ (freeCollapseCoordinates κ δ p))

instance collapseConeEncode_definable : ℒₛₑₜ-function₄[V] collapseConeEncode := by
  unfold collapseConeEncode
  definability

instance collapseConeDecode_definable : ℒₛₑₜ-function₄[V] collapseConeDecode := by
  unfold collapseConeDecode
  definability

theorem collapseConeEncode_condition {κ δ p q : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ δ) :
    collapseConeEncode κ δ p q ∈ woodinCollapse κ δ := by
  apply woodinCollapse_binary_union hκ hp (woodinCollapse_inverse_permuted hκ hp hq)
  intro x y _z hxy hxz
  have hfree := woodinCollapse_inverse_permuted_domain hκ hp hq x (mem_domain_of_kpair_mem hxz)
  have hn : x ∉ domain p := (show x ∈ κ ×ˢ δ ∧ x ∉ domain p by
    simpa [freeCollapseCoordinates] using hfree).2
  exact False.elim (hn (mem_domain_of_kpair_mem hxy))

theorem collapseConeEncode_extends (κ δ p q : V) : p ⊆ collapseConeEncode κ δ p q :=
  fun z hz ↦ mem_union_iff.mpr (Or.inl hz)

theorem collapseConeDecode_condition {κ δ p r : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hr : r ∈ woodinCollapse κ δ) :
    collapseConeDecode κ δ p r ∈ woodinCollapse κ δ := by
  have hres := woodinCollapse_subset hr (show r ↾ (freeCollapseCoordinates κ δ p) ⊆ r from
    fun z hz ↦ (mem_restrict_iff.mp hz).1)
  have hdom : domain (r ↾ (freeCollapseCoordinates κ δ p)) ⊆ freeCollapseCoordinates κ δ p := by
    intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    exact (kpair_mem_restrict_iff.mp hxy).2
  exact woodinCollapse_permuted hres (collapseCoordinateMap_function hκ hp)
    (collapseCoordinateMap_injective hκ hp) hdom (fun z hz ↦ collapseCoordinateMap_preserves_row hz)

theorem collapseConeDecode_encode {κ δ p q : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ δ) :
    collapseConeDecode κ δ p (collapseConeEncode κ δ p q) = q := by
  let := ((mem_woodinCollapse _ _ _).mp hp).2.1
  let := ((mem_woodinCollapse _ _ _).mp hq).2.1
  let := ((mem_woodinCollapse _ _ _).mp (woodinCollapse_inverse_permuted hκ hp hq)).2.1
  unfold collapseConeDecode collapseConeEncode
  rw [function_restrict_union_disjoint (p := p) (by
    intro x hx hfree
    exact (show x ∈ κ ×ˢ δ ∧ x ∉ domain p by simpa [freeCollapseCoordinates] using hfree).2 hx)
    (woodinCollapse_inverse_permuted_domain hκ hp hq)]
  apply permutedGraph_inverse_of_values
  intro x hx
  exact value_converseGraph_value (collapseCoordinateMap_function hκ hp)
    (collapseCoordinateMap_injective hκ hp)
    ((collapseCoordinateMap_range hκ hp).symm ▸ woodinCollapse_domain hq x hx)

theorem collapseConeEncode_decode {κ δ p r : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hr : r ∈ woodinCollapse κ δ) (hpr : p ⊆ r) :
    collapseConeEncode κ δ p (collapseConeDecode κ δ p r) = r := by
  let := ((mem_woodinCollapse _ _ _).mp hp).2.1
  let := ((mem_woodinCollapse _ _ _).mp hr).2.1
  have hv : ∀ x ∈ domain (r ↾ (freeCollapseCoordinates κ δ p)),
      (converseGraph (collapseCoordinateMap κ δ p)) ‘ ((collapseCoordinateMap κ δ p) ‘ x) = x := by
    intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    exact converseGraph_value_value (collapseCoordinateMap_function hκ hp)
      (collapseCoordinateMap_injective hκ hp) (kpair_mem_restrict_iff.mp hxy).2
  unfold collapseConeEncode collapseConeDecode
  rw [permutedGraph_inverse_of_values hv]
  exact function_union_restrict_complement hpr (woodinCollapse_domain hr)

theorem collapseConeEncode_mono {κ δ p q r : V} (hqr : q ⊆ r) :
    collapseConeEncode κ δ p q ⊆ collapseConeEncode κ δ p r := by
  intro z hz
  rcases mem_union_iff.mp hz with hz | hz
  · exact mem_union_iff.mpr (Or.inl hz)
  · exact mem_union_iff.mpr (Or.inr (permutedGraph_mono hqr _ hz))

theorem collapseConeDecode_mono {κ δ p q r : V} (hqr : q ⊆ r) :
    collapseConeDecode κ δ p q ⊆ collapseConeDecode κ δ p r := by
  apply permutedGraph_mono
  intro z hz
  obtain ⟨hz, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
  exact kpair_mem_restrict_iff.mpr ⟨hqr _ hz, hx⟩

end ZFVP
