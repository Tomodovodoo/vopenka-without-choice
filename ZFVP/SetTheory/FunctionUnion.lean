import ZFVP.SetTheory.FunctionValue

/-! Unions of compatible internal function graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def CompatibleFunctionFamily (B : V) : Prop :=
  ∀ f ∈ B, ∀ g ∈ B, ∀ x y z, ⟨x, y⟩ₖ ∈ f → ⟨x, z⟩ₖ ∈ g → y = z

instance compatibleFunctionFamily_definable : ℒₛₑₜ-predicate[V] CompatibleFunctionFamily := by
  unfold CompatibleFunctionFamily
  definability

theorem isFunction_sUnion {B : V} (hF : ∀ f ∈ B, IsFunction f)
    (hC : CompatibleFunctionFamily B) : IsFunction (⋃ˢ B) := by
  apply isFunction_iff.mpr
  apply mem_function.intro
  · intro p hp
    obtain ⟨f, hf, hpf⟩ := mem_sUnion_iff.mp hp
    have : IsFunction f := hF f hf
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hpf
    exact kpair_mem_iff.mpr ⟨mem_domain_of_kpair_mem hp, mem_range_of_kpair_mem hp⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
    refine ⟨y, hxy, ?_⟩
    intro z hxz
    obtain ⟨f, hf, hfz⟩ := mem_sUnion_iff.mp hxz
    obtain ⟨g, hg, hgy⟩ := mem_sUnion_iff.mp hxy
    exact hC f hf g hg x z y hfz hgy

theorem value_sUnion_of_mem {B f x : V} (hF : ∀ g ∈ B, IsFunction g)
    (hC : CompatibleFunctionFamily B) (hf : f ∈ B) (hx : x ∈ domain f) :
    (⋃ˢ B) ‘ x = f ‘ x := by
  have : IsFunction f := hF f hf
  have : IsFunction (⋃ˢ B) := isFunction_sUnion hF hC
  exact value_eq_of_kpair_mem (mem_sUnion_iff.mpr ⟨f, hf, kpair_value_mem hx⟩)

theorem mem_domain_sUnion_iff (B x : V) :
    x ∈ domain (⋃ˢ B) ↔ ∃ f ∈ B, x ∈ domain f := by
  simp only [mem_domain_iff, mem_sUnion_iff]
  constructor
  · rintro ⟨y, f, hf, hxy⟩
    exact ⟨f, hf, y, hxy⟩
  · rintro ⟨f, hf, y, hxy⟩
    exact ⟨y, f, hf, hxy⟩

theorem restrict_eq_of_values {f g A : V} [IsFunction f] [IsFunction g]
    (hf : A ⊆ domain f) (hg : A ⊆ domain g)
    (hv : ∀ x ∈ A, f ‘ x = g ‘ x) : f ↾ A = g ↾ A := by
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨hpf, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
    have hy : g ‘ x = y := (hv x hx).symm.trans (value_eq_of_kpair_mem hpf)
    exact kpair_mem_restrict_iff.mpr ⟨kpair_mem_iff_value.mpr ⟨hg x hx, hy⟩, hx⟩
  · intro hp
    obtain ⟨hpg, x, hx, y, rfl⟩ := mem_restrict_iff.mp hp
    have hy : f ‘ x = y := (hv x hx).trans (value_eq_of_kpair_mem hpg)
    exact kpair_mem_restrict_iff.mpr ⟨kpair_mem_iff_value.mpr ⟨hf x hx, hy⟩, hx⟩

theorem functions_eq_of_domain_values {f g : V} [IsFunction f] [IsFunction g]
    (hd : domain f = domain g) (hv : ∀ x ∈ domain f, f ‘ x = g ‘ x) : f = g := by
  have h := restrict_eq_of_values (A := domain f) (subset_refl _) (by rw [hd]) hv
  simpa only [IsFunction.restrict_eq_self f (domain f) (subset_refl _),
    IsFunction.restrict_eq_self g (domain f) (by rw [hd])] using h

@[simp] theorem restrict_empty_domain (f : V) : f ↾ (∅ : V) = ∅ := by
  apply mem_ext
  intro p
  simp [mem_restrict_iff]

end ZFVP
