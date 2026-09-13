import ZFVP.SetTheory.DefinableGraph

/-! Evaluation of internal function graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem value_eq_of_kpair_mem {f x y : V} [IsFunction f] (hxy : ⟨x, y⟩ₖ ∈ f) :
    f ‘ x = y := by
  apply mem_ext
  intro z
  change z ∈ {z ∈ ⋃ˢ range f ; ∃ y, z ∈ y ∧ ⟨x, y⟩ₖ ∈ f} ↔ z ∈ y
  rw [mem_sep_iff]
  constructor
  · rintro ⟨_, w, hzw, hxw⟩
    exact IsFunction.unique hxw hxy ▸ hzw
  · intro hz
    exact ⟨mem_sUnion_iff.mpr ⟨y, mem_range_of_kpair_mem hxy, hz⟩, y, hz, hxy⟩

theorem kpair_value_mem {f x : V} [IsFunction f] (hx : x ∈ domain f) :
    ⟨x, f ‘ x⟩ₖ ∈ f := by
  obtain ⟨y, hxy⟩ := mem_domain_iff.mp hx
  rw [value_eq_of_kpair_mem hxy]
  exact hxy

theorem kpair_mem_iff_value {f x y : V} [IsFunction f] :
    ⟨x, y⟩ₖ ∈ f ↔ x ∈ domain f ∧ f ‘ x = y := by
  constructor
  · intro h
    exact ⟨mem_domain_of_kpair_mem h, value_eq_of_kpair_mem h⟩
  · rintro ⟨hx, rfl⟩
    exact kpair_value_mem hx

theorem function_value_mem {A B f x : V} (hf : f ∈ B ^ A) (hx : x ∈ A) :
    f ‘ x ∈ B := by
  have : IsFunction f := IsFunction.of_mem hf
  have hd : x ∈ domain f := (domain_eq_of_mem_function hf).symm ▸ hx
  exact (mem_of_mem_functions hf (kpair_value_mem hd)).2

theorem identity_value {A x : V} (hx : x ∈ A) : (SetTheory.identity A) ‘ x = x :=
  value_eq_of_kpair_mem (kpair_mem_identity_iff.mpr ⟨hx, rfl⟩)

theorem value_eq_empty_of_not_mem_domain {f x : V} (hx : x ∉ domain f) :
    f ‘ x = ∅ := by
  apply mem_ext
  intro z
  simp only [value, mem_sep_iff, not_mem_empty, iff_false, not_and]
  rintro _ ⟨y, _, hxy⟩
  exact hx (mem_domain_of_kpair_mem hxy)

theorem value_restrict {f A x : V} [IsFunction f] (hx : x ∈ domain f) (hA : x ∈ A) :
    (f ↾ A) ‘ x = f ‘ x :=
  value_eq_of_kpair_mem (kpair_mem_restrict_iff.mpr ⟨kpair_value_mem hx, hA⟩)

theorem definableGraph_mem_function (A : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    definableGraph A F hF ∈ (repl F hF A) ^ A := by
  apply mem_function.intro
  · intro p hp
    obtain ⟨y, hy, rfl⟩ := (mem_definableGraph_iff A F hF p).mp hp
    simp only [kpair_mem_iff]
    exact ⟨hy, repl_spec hF |>.mpr ⟨y, hy, rfl⟩⟩
  · intro y hy
    refine ⟨F y, (pair_mem_definableGraph_iff A F hF y (F y)).mpr ⟨hy, rfl⟩, ?_⟩
    intro z hz
    exact ((pair_mem_definableGraph_iff A F hF y z).mp hz).2

instance definableGraph_isFunction (A : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    IsFunction (definableGraph A F hF) :=
  IsFunction.of_mem (definableGraph_mem_function A F hF)

theorem value_definableGraph (A : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {x : V} (hx : x ∈ A) : (definableGraph A F hF) ‘ x = F x := by
  exact value_eq_of_kpair_mem ((pair_mem_definableGraph_iff A F hF x (F x)).mpr ⟨hx, rfl⟩)

theorem definableGraph_mem_function_of_mapsTo (A B : V) (F : V → V)
    (hF : ℒₛₑₜ-function₁ F) (h : ∀ x ∈ A, F x ∈ B) :
    definableGraph A F hF ∈ B ^ A := by
  apply mem_function_of_mem_function_of_subset (definableGraph_mem_function A F hF)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (repl_spec hF).mp hy
  exact h x hx

end ZFVP
