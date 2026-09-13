import ZFVP.SetTheory.InverseFunction

/-! The Schröder–Bernstein theorem inside a model of ZF: injections `f : A → B` and `g : B → A`
yield a bijection. The proof uses the greatest post-fixed point of the monotone operator
`X ↦ A \ g[B \ f[X]]`, so no recursion is required. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The image of `X` under the graph `f`. -/
noncomputable def graphImage (f X : V) : V := {y ∈ range f ; ∃ x ∈ X, ⟨x, y⟩ₖ ∈ f}

theorem mem_graphImage_iff (f X y : V) : y ∈ graphImage f X ↔ ∃ x ∈ X, ⟨x, y⟩ₖ ∈ f := by
  simp only [graphImage, mem_sep_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨by obtain ⟨x, _, hx⟩ := h; exact mem_range_of_kpair_mem hx, h⟩⟩

instance graphImage_definable : ℒₛₑₜ-function₂[V] graphImage := by
  have h : ℒₛₑₜ-relation₃ (fun Y f X : V ↦ ∀ y, y ∈ Y ↔ ∃ x ∈ X, ⟨x, y⟩ₖ ∈ f) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = graphImage (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_graphImage_iff]

theorem graphImage_mono {f X Y : V} (h : X ⊆ Y) : graphImage f X ⊆ graphImage f Y := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (mem_graphImage_iff f X y).mp hy
  exact (mem_graphImage_iff f Y y).mpr ⟨x, h x hx, hxy⟩

theorem graphImage_subset {A B f X : V} (hf : f ∈ B ^ A) : graphImage f X ⊆ B := by
  intro y hy
  obtain ⟨x, _, hxy⟩ := (mem_graphImage_iff f X y).mp hy
  exact (kpair_mem_iff.mp (subset_prod_of_mem_function hf _ hxy)).2

/-- The Schröder–Bernstein operator `X ↦ A \ g[B \ f[X]]`. -/
noncomputable def bernsteinStep (f g A B X : V) : V := A \ graphImage g (B \ graphImage f X)

theorem bernsteinStep_mono {f g A B X Y : V} (h : X ⊆ Y) :
    bernsteinStep f g A B X ⊆ bernsteinStep f g A B Y := by
  intro z hz
  obtain ⟨hzA, hz⟩ := mem_sdiff_iff.mp hz
  refine mem_sdiff_iff.mpr ⟨hzA, fun hz' ↦ hz ?_⟩
  refine graphImage_mono (fun y hy ↦ ?_) z hz'
  obtain ⟨hyB, hy⟩ := mem_sdiff_iff.mp hy
  exact mem_sdiff_iff.mpr ⟨hyB, fun hy' ↦ hy (graphImage_mono h y hy')⟩

/-- The post-fixed points of the operator. -/
noncomputable def bernsteinPostFixed (f g A B : V) : V :=
  sep (℘ A) (fun X ↦ X ⊆ A \ graphImage g (B \ graphImage f X))
    (by have := graphImage_definable (V := V); definability)

/-- The greatest post-fixed point. -/
noncomputable def bernsteinSet (f g A B : V) : V := ⋃ˢ bernsteinPostFixed f g A B

theorem bernsteinSet_subset (f g A B : V) : bernsteinSet f g A B ⊆ A := by
  intro z hz
  obtain ⟨X, hX, hzX⟩ := mem_sUnion_iff.mp hz
  exact mem_power_iff.mp (mem_sep_iff.mp hX).1 z hzX

theorem bernsteinSet_fixed (f g A B : V) :
    bernsteinSet f g A B = bernsteinStep f g A B (bernsteinSet f g A B) := by
  have h1 : bernsteinSet f g A B ⊆ bernsteinStep f g A B (bernsteinSet f g A B) := by
    intro z hz
    obtain ⟨X, hX, hzX⟩ := mem_sUnion_iff.mp hz
    have hXC : X ⊆ bernsteinSet f g A B := fun w hw ↦ mem_sUnion_iff.mpr ⟨X, hX, hw⟩
    exact bernsteinStep_mono hXC z ((mem_sep_iff.mp hX).2 z hzX)
  refine subset_antisymm h1 ?_
  intro z hz
  refine mem_sUnion_iff.mpr ⟨bernsteinStep f g A B (bernsteinSet f g A B), ?_, hz⟩
  refine mem_sep_iff.mpr ⟨mem_power_iff.mpr (fun w hw ↦ (mem_sdiff_iff.mp hw).1), ?_⟩
  exact bernsteinStep_mono h1

theorem sdiff_bernsteinSet {f g A B : V} (hg : g ∈ A ^ B) :
    A \ bernsteinSet f g A B = graphImage g (B \ graphImage f (bernsteinSet f g A B)) := by
  apply mem_ext
  intro z
  rw [mem_sdiff_iff]
  constructor
  · rintro ⟨hzA, hz⟩
    by_contra hz'
    exact hz (bernsteinSet_fixed f g A B ▸ mem_sdiff_iff.mpr ⟨hzA, hz'⟩)
  · intro hz
    refine ⟨graphImage_subset hg z hz, fun hzC ↦ ?_⟩
    rw [bernsteinSet_fixed f g A B] at hzC
    exact (mem_sdiff_iff.mp hzC).2 hz

/-- The Schröder–Bernstein bijection. -/
noncomputable def bernsteinBijection (f g A B : V) : V :=
  (f ↾ (bernsteinSet f g A B)) ∪ ((converseGraph g) ↾ (A \ bernsteinSet f g A B))

theorem pair_mem_bernsteinBijection_iff (f g A B x y : V) :
    ⟨x, y⟩ₖ ∈ bernsteinBijection f g A B ↔
      (⟨x, y⟩ₖ ∈ f ∧ x ∈ bernsteinSet f g A B) ∨
        (⟨y, x⟩ₖ ∈ g ∧ x ∈ A ∧ x ∉ bernsteinSet f g A B) := by
  simp only [bernsteinBijection, mem_union_iff, kpair_mem_restrict_iff, pair_mem_converseGraph,
    mem_sdiff_iff]

/-- Schröder–Bernstein: injections both ways yield a bijection. -/
theorem schroeder_bernstein {A B f g : V} (hf : f ∈ B ^ A) (hfi : Injective f)
    (hg : g ∈ A ^ B) (hgi : Injective g) :
    ∃ h ∈ B ^ A, Injective h ∧ range h = B := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  set C := bernsteinSet f g A B with hCdef
  have hCA : C ⊆ A := bernsteinSet_subset f g A B
  have hcomp : A \ C = graphImage g (B \ graphImage f C) := sdiff_bernsteinSet hg
  have hmem := pair_mem_bernsteinBijection_iff f g A B
  have hnotC : ∀ x, x ∈ A → x ∉ C → ∃ y, y ∈ B ∧ y ∉ graphImage f C ∧ ⟨y, x⟩ₖ ∈ g := by
    intro x hxA hxC
    have : x ∈ graphImage g (B \ graphImage f C) := hcomp ▸ mem_sdiff_iff.mpr ⟨hxA, hxC⟩
    obtain ⟨y, hy, hyx⟩ := (mem_graphImage_iff _ _ _).mp this
    obtain ⟨hyB, hyf⟩ := mem_sdiff_iff.mp hy
    exact ⟨y, hyB, hyf, hyx⟩
  refine ⟨bernsteinBijection f g A B, ?_, ?_, ?_⟩
  · apply mem_function.intro
    · intro p hp
      have hp' : p ∈ (f ↾ C) ∪ ((converseGraph g) ↾ (A \ C)) := hp
      rcases mem_union_iff.mp hp' with hp' | hp'
      · obtain ⟨hpf, x, hxC, y, rfl⟩ := mem_restrict_iff.mp hp'
        exact kpair_mem_iff.mpr ⟨hCA x hxC, (kpair_mem_iff.mp (subset_prod_of_mem_function hf _ hpf)).2⟩
      · obtain ⟨hpg, x, hxAC, y, rfl⟩ := mem_restrict_iff.mp hp'
        have hyx : ⟨y, x⟩ₖ ∈ g := (pair_mem_converseGraph _ _ _).mp hpg
        exact kpair_mem_iff.mpr ⟨(mem_sdiff_iff.mp hxAC).1,
          (kpair_mem_iff.mp (subset_prod_of_mem_function hg _ hyx)).1⟩
    · intro x hxA
      by_cases hxC : x ∈ C
      · refine ⟨f ‘ x, (hmem x _).mpr (Or.inl ⟨kpair_value_mem (by rwa [domain_eq_of_mem_function hf]), hxC⟩), ?_⟩
        intro y hy
        rcases (hmem x y).mp hy with ⟨hy, _⟩ | ⟨_, _, hxC'⟩
        · exact value_eq_of_kpair_mem hy ▸ rfl
        · exact (hxC' hxC).elim
      · obtain ⟨y, hyB, hyf, hyx⟩ := hnotC x hxA hxC
        refine ⟨y, (hmem x y).mpr (Or.inr ⟨hyx, hxA, hxC⟩), ?_⟩
        intro y' hy'
        rcases (hmem x y').mp hy' with ⟨_, hxC'⟩ | ⟨hy'x, _, _⟩
        · exact (hxC hxC').elim
        · exact hgi y' y x hy'x hyx
  · intro x₁ x₂ y h₁ h₂
    rcases (hmem x₁ y).mp h₁ with ⟨h₁, hx₁⟩ | ⟨h₁, hx₁A, hx₁⟩ <;>
      rcases (hmem x₂ y).mp h₂ with ⟨h₂, hx₂⟩ | ⟨h₂, hx₂A, hx₂⟩
    · exact hfi x₁ x₂ y h₁ h₂
    · obtain ⟨y', _, hy'f, hy'x⟩ := hnotC x₂ hx₂A hx₂
      have := hgi y' y x₂ hy'x h₂
      subst this
      exact (hy'f ((mem_graphImage_iff _ _ _).mpr ⟨x₁, hx₁, h₁⟩)).elim
    · obtain ⟨y', _, hy'f, hy'x⟩ := hnotC x₁ hx₁A hx₁
      have := hgi y' y x₁ hy'x h₁
      subst this
      exact (hy'f ((mem_graphImage_iff _ _ _).mpr ⟨x₂, hx₂, h₂⟩)).elim
    · exact IsFunction.unique h₁ h₂
  · apply mem_ext
    intro y
    rw [mem_range_iff]
    constructor
    · rintro ⟨x, hxy⟩
      rcases (hmem x y).mp hxy with ⟨hxy, _⟩ | ⟨hyx, _, _⟩
      · exact (kpair_mem_iff.mp (subset_prod_of_mem_function hf _ hxy)).2
      · exact (kpair_mem_iff.mp (subset_prod_of_mem_function hg _ hyx)).1
    · intro hyB
      by_cases hyf : y ∈ graphImage f C
      · obtain ⟨x, hxC, hxy⟩ := (mem_graphImage_iff _ _ _).mp hyf
        exact ⟨x, (hmem x y).mpr (Or.inl ⟨hxy, hxC⟩)⟩
      · have hyx : ⟨y, g ‘ y⟩ₖ ∈ g := kpair_value_mem (by rwa [domain_eq_of_mem_function hg])
        have hgy : g ‘ y ∈ A \ C := hcomp ▸ (mem_graphImage_iff _ _ _).mpr ⟨y, mem_sdiff_iff.mpr ⟨hyB, hyf⟩, hyx⟩
        obtain ⟨hgyA, hgyC⟩ := mem_sdiff_iff.mp hgy
        exact ⟨g ‘ y, (hmem _ y).mpr (Or.inr ⟨hyx, hgyA, hgyC⟩)⟩

/-- Equinumerous sets are in bijection. -/
theorem exists_bijection_of_cardEQ {A B : V} (h : A ≋ B) :
    ∃ h ∈ B ^ A, Injective h ∧ range h = B := by
  obtain ⟨⟨f, hf, hfi⟩, ⟨g, hg, hgi⟩⟩ := h
  exact schroeder_bernstein hf hfi hg hgi

end ZFVP
