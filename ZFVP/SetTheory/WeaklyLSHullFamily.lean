import ZFVP.SetTheory.WeaklyLSImageHull
import ZFVP.SetTheory.SmallCollapseSurjection

/-! The directed family of small elementary hulls used in Usuba Lemma 3.1. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def weaklyLSHullFamily (κ α x : V) : V :=
  {Z ∈ power (hierarchy α) ; IsElementaryInclusion Z (hierarchy α) ∧
    x ∈ Z ∧ HasSmallTransitiveCollapse κ Z}

instance weaklyLSHullFamily_definable : ℒₛₑₜ-function₃[V] weaklyLSHullFamily := by
  have hh : ℒₛₑₜ-relation₄ (fun F κ α x : V ↦ ∀ Z, Z ∈ F ↔
      Z ∈ power (hierarchy α) ∧ IsElementaryInclusion Z (hierarchy α) ∧
        x ∈ Z ∧ HasSmallTransitiveCollapse κ Z) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [weaklyLSHullFamily, mem_sep_iff]
  rfl

theorem mem_weaklyLSHullFamily (κ α x Z : V) :
    Z ∈ weaklyLSHullFamily κ α x ↔ IsElementaryInclusion Z (hierarchy α) ∧
      x ∈ Z ∧ HasSmallTransitiveCollapse κ Z := by
  simp only [weaklyLSHullFamily, mem_sep_iff, mem_power_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.subset, h⟩⟩

theorem IsWeaklyLSCardinal.hullFamily_covers {κ α x : V}
    (hκ : IsWeaklyLSCardinal κ) [IsOrdinal α] (hκα : κ ⊆ α) (hx : x ∈ hierarchy α)
    {γ : V} (hγκ : γ ∈ κ) :
    ∃ Z ∈ weaklyLSHullFamily κ α x, hierarchy γ ⊆ Z := by
  obtain ⟨Z, hZ, hγZ, hxZ, hs⟩ := hκ.2.2 γ hγκ α inferInstance hκα x hx
  exact ⟨Z, (mem_weaklyLSHullFamily _ _ _ _).mpr ⟨hZ, hxZ, hs⟩, hγZ⟩

theorem IsWeaklyLSCardinal.hullFamily_nonempty {κ α x : V}
    (hκ : IsWeaklyLSCardinal κ) [IsOrdinal α] (hκα : κ ⊆ α) (hx : x ∈ hierarchy α) :
    IsNonempty (weaklyLSHullFamily κ α x) := by
  obtain ⟨Z, hZ, _⟩ := hκ.hullFamily_covers hκα hx hκ.2.1
  exact ⟨Z, hZ⟩

theorem IsWeaklyLSCardinal.hullFamily_directed {κ α x : V}
    (hκ : IsWeaklyLSCardinal κ) [IsOrdinal α] (hκα : κ ⊆ α) (hx : x ∈ hierarchy α) :
    ∀ Z₀ ∈ weaklyLSHullFamily κ α x, ∀ Z₁ ∈ weaklyLSHullFamily κ α x,
      ∃ Z₂ ∈ weaklyLSHullFamily κ α x, Z₀ ⊆ Z₂ ∧ Z₁ ⊆ Z₂ := by
  let := hκ.1.1
  have hsucc (β : V) (hβ : β ∈ κ) : succ β ∈ κ :=
    initial_succ_mem hκ.1 (IsOrdinal.toIsTransitive.transitive _ hκ.2.1) hβ
  intro Z₀ hZ₀ Z₁ hZ₁
  obtain ⟨he₀, hx₀, hs₀⟩ := (mem_weaklyLSHullFamily _ _ _ _).mp hZ₀
  obtain ⟨he₁, hx₁, hs₁⟩ := (mem_weaklyLSHullFamily _ _ _ _).mp hZ₁
  obtain ⟨γ₀, hγ₀, e₀, hf₀, hr₀⟩ := hs₀.rank_surjection he₀.source_nonempty hsucc
  obtain ⟨γ₁, hγ₁, e₁, hf₁, hr₁⟩ := hs₁.rank_surjection he₁.source_nonempty hsucc
  let := IsFunction.of_mem hf₀
  let := IsFunction.of_mem hf₁
  let := IsOrdinal.of_mem hγ₀
  let := IsOrdinal.of_mem hγ₁
  obtain ⟨γ, hγκ, hγ₀γ, hγ₁γ⟩ := ordinal_common_upper_bound hγ₀ hγ₁
  let := IsOrdinal.of_mem hγκ
  have hd₀ : domain e₀ ⊆ hierarchy γ := by
    rw [domain_eq_of_mem_function hf₀]
    exact hierarchy_mono hγ₀γ
  have hd₁ : domain e₁ ⊆ hierarchy γ := by
    rw [domain_eq_of_mem_function hf₁]
    exact hierarchy_mono hγ₁γ
  obtain ⟨Z, he, hxZ, hs, h₀, h₁⟩ := hκ.hull_for_two_images hγκ hκα hx hd₀ hd₁
    (hr₀.symm ▸ he₀.subset) (hr₁.symm ▸ he₁.subset)
  exact ⟨Z, (mem_weaklyLSHullFamily _ _ _ _).mpr ⟨he, hxZ, hs⟩,
    hr₀ ▸ h₀, hr₁ ▸ h₁⟩

end ZFVP
