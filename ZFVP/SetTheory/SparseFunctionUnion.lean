import ZFVP.SetTheory.SparseAppend

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsSparseFunctionOn.restrict {A p : V} (hp : IsSparseFunctionOn A p) (B : V) :
    IsSparseFunctionOn B (p ↾ B) := by
  let := hp.1
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x hx
    exact (mem_inter_iff.mp (domain_restrict_eq p B ▸ hx)).2
  · intro x hx
    have hh := mem_inter_iff.mp (domain_restrict_eq p B ▸ hx)
    rw [value_restrict hh.1 hh.2]
    exact hp.2.2 x hh.1

theorem isSparseFunctionOn_sUnion {C A : V}
    (hS : ∀ p ∈ C, IsSparseFunctionOn A p) (hC : CompatibleFunctionFamily C) :
    IsSparseFunctionOn A (⋃ˢ C) := by
  have hF : ∀ p ∈ C, IsFunction p := fun p hp ↦ (hS p hp).1
  refine ⟨isFunction_sUnion hF hC, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, hx⟩ := (mem_domain_sUnion_iff C x).mp hx
    exact (hS p hp).2.1 x hx
  · intro x hx
    obtain ⟨p, hp, hx⟩ := (mem_domain_sUnion_iff C x).mp hx
    rw [value_sUnion_of_mem hF hC hp hx]
    exact (hS p hp).2.2 x hx

theorem function_sUnion_restrict_of_coverage {C a p : V}
    (hF : ∀ q ∈ C, IsFunction q) (hC : CompatibleFunctionFamily C)
    (hp : p ∈ C) (hpa : domain p ⊆ a)
    (hcover : domain (⋃ˢ C) ∩ a ⊆ domain p) : (⋃ˢ C) ↾ a = p := by
  let := hF p hp
  let := isFunction_sUnion hF hC
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzu, x, hxa, y, rfl⟩ := mem_restrict_iff.mp hz
    have hxp := hcover x (mem_inter_iff.mpr ⟨mem_domain_of_kpair_mem hzu, hxa⟩)
    apply kpair_mem_iff_value.mpr
    refine ⟨hxp, ?_⟩
    rw [← value_sUnion_of_mem hF hC hp hxp]
    exact value_eq_of_kpair_mem hzu
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    exact kpair_mem_restrict_iff.mpr
      ⟨mem_sUnion_iff.mpr ⟨p, hp, hz⟩, hpa x (mem_domain_of_kpair_mem hz)⟩

theorem sparseFunctionUnion_restrict {C A a p : V}
    (hS : ∀ q ∈ C, IsSparseFunctionOn A q) (hC : CompatibleFunctionFamily C)
    (hp : p ∈ C) (hpa : domain p ⊆ a)
    (hcover : ∀ q ∈ C, domain q ∩ a ⊆ domain p) : (⋃ˢ C) ↾ a = p := by
  apply function_sUnion_restrict_of_coverage (fun q hq ↦ (hS q hq).1) hC hp hpa
  intro x hx
  obtain ⟨hxu, hxa⟩ := mem_inter_iff.mp hx
  obtain ⟨q, hq, hxq⟩ := (mem_domain_sUnion_iff C x).mp hxu
  exact hcover q hq x (mem_inter_iff.mpr ⟨hxq, hxa⟩)

end ZFVP
