import ZFVP.SetTheory.WoodinCollapse
import ZFVP.SetTheory.CardinalSmallComplements

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCollapse_mono {κ β δ : V} [IsOrdinal β] [IsOrdinal δ]
    (hβδ : β ⊆ δ) : woodinCollapse κ β ⊆ woodinCollapse κ δ := by
  intro p hp
  obtain ⟨ht, hf, hs, hv⟩ := (mem_woodinCollapse _ _ _).mp hp
  refine (mem_woodinCollapse _ _ _).mpr ⟨?_, hf, hs, hv⟩
  intro z hz
  obtain ⟨a, ha, x, hx, rfl⟩ := mem_prod_iff.mp (ht z hz)
  obtain ⟨α, hα, η, hη, rfl⟩ := mem_prod_iff.mp ha
  exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hα, hβδ η hη⟩,
    hierarchy_mono hβδ x hx⟩

noncomputable def woodinCollapseCut (κ β p : V) : V := p ↾ (κ ×ˢ β)

instance woodinCollapseCut_definable : ℒₛₑₜ-function₃[V] woodinCollapseCut := by
  unfold woodinCollapseCut
  definability

theorem woodinCollapseCut_subset (κ β p : V) : woodinCollapseCut κ β p ⊆ p :=
  restrict_subset _ _

theorem woodinCollapseCut_mem {κ β δ p : V} (hβ : IsRegularCardinal β)
    (hp : p ∈ woodinCollapse κ δ) : woodinCollapseCut κ β p ∈ woodinCollapse κ β := by
  let := hβ.1.1
  obtain ⟨ht, hf, hs, hv⟩ := (mem_woodinCollapse _ _ _).mp hp
  let := hf
  have hc := woodinCollapse_subset hp (woodinCollapseCut_subset κ β p)
  obtain ⟨_, hcf, hcs, hcv⟩ := (mem_woodinCollapse _ _ _).mp hc
  refine (mem_woodinCollapse _ _ _).mpr ⟨?_, hcf, hcs, hcv⟩
  intro z hz
  obtain ⟨a, ha, x, hx, rfl⟩ := mem_prod_iff.mp (ht z (restrict_subset _ _ z hz))
  have haβ := (kpair_mem_restrict_iff.mp hz).2
  obtain ⟨α, hα, η, hη, rfl⟩ := mem_prod_iff.mp haβ
  let := IsOrdinal.of_mem hη
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  have hb := regularCardinal_ordinalAdd_closed hβ (hβ.2.1 (1 : V) (by simp)) hη
  exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨hα, hη⟩,
    hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hb) x
      (hv α η x (restrict_subset _ _ _ hz))⟩

theorem woodinCollapseCut_eq {κ β p : V} (hp : p ∈ woodinCollapse κ β) :
    woodinCollapseCut κ β p = p := by
  apply SetTheory.subset_antisymm (woodinCollapseCut_subset _ _ _)
  intro z hz
  obtain ⟨a, ha, x, _, rfl⟩ := mem_prod_iff.mp (((mem_woodinCollapse _ _ _).mp hp).1 z hz)
  exact kpair_mem_restrict_iff.mpr ⟨hz, ha⟩

theorem woodinCollapseCut_mono {κ β p q : V} (h : p ⊆ q) :
    woodinCollapseCut κ β p ⊆ woodinCollapseCut κ β q := by
  intro z hz
  obtain ⟨hzp, a, ha, x, rfl⟩ := mem_restrict_iff.mp hz
  exact kpair_mem_restrict_iff.mpr ⟨h _ hzp, ha⟩

theorem woodinCollapse_union_two {κ δ p q : V} (hκ : IsRegularCardinal κ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ δ)
    (hc : ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z) :
    p ∪ q ∈ woodinCollapse κ δ := by
  have hpF := ((mem_woodinCollapse _ _ _).mp hp).2.1
  have hqF := ((mem_woodinCollapse _ _ _).mp hq).2.1
  let := hpF
  let := hqF
  have hB : ∀ f ∈ ({p, q} : V), f ∈ woodinCollapse κ δ := by
    intro f hf
    rcases show f = p ∨ f = q from by simpa using hf with rfl | rfl <;> assumption
  have hC : CompatibleFunctionFamily ({p, q} : V) := by
    intro f hf g hg x y z hxy hxz
    have hff : f = p ∨ f = q := by simpa using hf
    have hgg : g = p ∨ g = q := by simpa using hg
    rcases hff with rfl | rfl <;> rcases hgg with rfl | rfl
    · exact IsFunction.unique hxy hxz
    · exact hc x y z hxy hxz
    · exact (hc x z y hxz hxy).symm
    · exact IsFunction.unique hxy hxz
  have hd : domain (p ∪ q) = domain p ∪ domain q := by
    ext x
    simp only [mem_domain_iff, mem_union_iff, exists_or]
  have hs : IsCardinalSmall κ (domain (⋃ˢ ({p, q} : V))) := by
    simpa [hd] using
      (((mem_woodinCollapse _ _ _).mp hp).2.2.1.union hκ
        ((mem_woodinCollapse _ _ _).mp hq).2.2.1)
  simpa using woodinCollapse_union hB hC hs

theorem woodinCollapseCut_extension {κ β δ p q : V} (hκ : IsRegularCardinal κ)
    (hβ : IsRegularCardinal β) [IsOrdinal δ] (hβδ : β ⊆ δ)
    (hp : p ∈ woodinCollapse κ δ) (hq : q ∈ woodinCollapse κ β)
    (hext : woodinCollapseCut κ β p ⊆ q) :
    p ∪ q ∈ woodinCollapse κ δ ∧ p ⊆ p ∪ q ∧ woodinCollapseCut κ β (p ∪ q) = q := by
  let := hβ.1.1
  have hqδ := woodinCollapse_mono hβδ q hq
  have hqF := ((mem_woodinCollapse _ _ _).mp hq).2.1
  let := hqF
  have hc : ∀ x y z, ⟨x, y⟩ₖ ∈ p → ⟨x, z⟩ₖ ∈ q → y = z := by
    intro x y z hxy hxz
    have hx := (kpair_mem_iff.mp (((mem_woodinCollapse _ _ _).mp hq).1 _ hxz)).1
    exact IsFunction.unique (hext _ (kpair_mem_restrict_iff.mpr ⟨hxy, hx⟩)) hxz
  refine ⟨woodinCollapse_union_two hκ hp hqδ hc, fun z hz ↦ mem_union_iff.mpr (Or.inl hz), ?_⟩
  apply SetTheory.subset_antisymm
  · intro z hz
    obtain ⟨hzu, a, ha, x, rfl⟩ := mem_restrict_iff.mp hz
    rcases mem_union_iff.mp hzu with h | h
    · exact hext _ (kpair_mem_restrict_iff.mpr ⟨h, ha⟩)
    · exact h
  · have hm := woodinCollapseCut_mono (κ := κ) (β := β)
      (show q ⊆ p ∪ q from fun z hz ↦ mem_union_iff.mpr (Or.inr hz))
    rwa [woodinCollapseCut_eq hq] at hm

end ZFVP
