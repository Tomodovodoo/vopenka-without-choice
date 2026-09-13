import ZFVP.SetTheory.InternalOrderType
import ZFVP.SetTheory.Hartogs

/-! Pulling a well-order back along an injective definable map, and two facts about infinite
initial ordinals: `succ μ ≤# μ` for infinite `μ`, and initial infinite ordinals are closed under
successor. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The pullback of the relation `R` along the map `e`, restricted to `D`. -/
noncomputable def pulledRelation (D : V) (e : V → V) (he : ℒₛₑₜ-function₁ e) (R : V) : V :=
  sep (D ×ˢ D) (fun p ↦ ⟨e (kpair.π₁ p), e (kpair.π₂ p)⟩ₖ ∈ R) (by have := he; definability)

theorem pair_mem_pulledRelation_iff (D : V) (e : V → V) (he : ℒₛₑₜ-function₁ e) (R x y : V) :
    ⟨x, y⟩ₖ ∈ pulledRelation D e he R ↔ x ∈ D ∧ y ∈ D ∧ ⟨e x, e y⟩ₖ ∈ R := by
  simp only [pulledRelation, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

/-- The pullback of a well-order along an injective map is a well-order. -/
theorem pulledRelation_wellOrder {D T R : V} (e : V → V) (he : ℒₛₑₜ-function₁ e)
    (hR : IsInternalWellOrder R T) (hmaps : ∀ x ∈ D, e x ∈ T)
    (hinj : ∀ x ∈ D, ∀ y ∈ D, e x = e y → x = y) :
    IsInternalWellOrder (pulledRelation D e he R) D := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, ?_, ?_, ?_⟩
  · intro A hAD hA
    obtain ⟨a, ha⟩ := hA.nonempty
    let E : V := repl e he A
    have hE : ∀ z, z ∈ E ↔ ∃ x ∈ A, z = e x := fun z ↦ repl_spec he
    have hET : E ⊆ T := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (hE z).mp hz
      exact hmaps x (hAD x hx)
    have hEne : IsNonempty E := ⟨e a, (hE _).mpr ⟨a, ha, rfl⟩⟩
    obtain ⟨m, hmE, hmin⟩ := hR.2.1 E hET hEne
    obtain ⟨x, hxA, rfl⟩ := (hE m).mp hmE
    refine ⟨x, hxA, fun y hyA hyx ↦ ?_⟩
    obtain ⟨_, _, hyx'⟩ := (pair_mem_pulledRelation_iff D e he R y x).mp hyx
    exact hmin (e y) ((hE _).mpr ⟨y, hyA, rfl⟩) hyx'
  · intro x hx y hy z hz hxy hyz
    obtain ⟨_, _, hxy'⟩ := (pair_mem_pulledRelation_iff D e he R x y).mp hxy
    obtain ⟨_, _, hyz'⟩ := (pair_mem_pulledRelation_iff D e he R y z).mp hyz
    exact (pair_mem_pulledRelation_iff D e he R x z).mpr
      ⟨hx, hz, hR.2.2.1 _ (hmaps x hx) _ (hmaps y hy) _ (hmaps z hz) hxy' hyz'⟩
  · intro x hx y hy
    rcases hR.2.2.2 _ (hmaps x hx) _ (hmaps y hy) with h | h | h
    · exact Or.inl ((pair_mem_pulledRelation_iff D e he R x y).mpr ⟨hx, hy, h⟩)
    · exact Or.inr (Or.inl (hinj x hx y hy h))
    · exact Or.inr (Or.inr ((pair_mem_pulledRelation_iff D e he R y x).mpr ⟨hy, hx, h⟩))

theorem succ_injective_ordinal {x y : V} [IsOrdinal x] [IsOrdinal y] (h : succ x = succ y) : x = y := by
  have hx : x ∈ succ y := h ▸ mem_succ_self x
  have hy : y ∈ succ x := h.symm ▸ mem_succ_self y
  rcases mem_succ_iff.mp hx with hxy | hxy
  · exact hxy
  rcases mem_succ_iff.mp hy with hyx | hyx
  · exact hyx.symm
  exact (mem_irrefl x (IsOrdinal.toIsTransitive.mem_trans hxy hyx)).elim

/-- The shift injection witnessing `succ μ ≤# μ` for infinite `μ`. -/
noncomputable def shiftInjection (μ : V) : V :=
  sep (succ μ ×ˢ μ) (fun p ↦ (kpair.π₁ p = μ ∧ kpair.π₂ p = ∅) ∨
    (kpair.π₁ p ≠ μ ∧ kpair.π₁ p ∈ (ω : V) ∧ kpair.π₂ p = succ (kpair.π₁ p)) ∨
    (kpair.π₁ p ≠ μ ∧ kpair.π₁ p ∉ (ω : V) ∧ kpair.π₂ p = kpair.π₁ p)) (by definability)

theorem pair_mem_shiftInjection_iff (μ x y : V) :
    ⟨x, y⟩ₖ ∈ shiftInjection μ ↔ x ∈ succ μ ∧ y ∈ μ ∧
      ((x = μ ∧ y = ∅) ∨ (x ≠ μ ∧ x ∈ (ω : V) ∧ y = succ x) ∨ (x ≠ μ ∧ x ∉ (ω : V) ∧ y = x)) := by
  simp only [shiftInjection, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

/-- An infinite ordinal is equinumerous with its successor. -/
theorem succ_cardLE_of_omega_subset {μ : V} [IsOrdinal μ] (hω : (ω : V) ⊆ μ) : succ μ ≤# μ := by
  have hmem := pair_mem_shiftInjection_iff μ
  refine ⟨shiftInjection μ, ?_, ?_⟩
  · apply mem_function.intro
    · intro p hp
      exact (mem_sep_iff.mp hp).1
    · intro x hx
      by_cases hxμ : x = μ
      · subst hxμ
        refine ⟨∅, (hmem _ _).mpr ⟨hx, hω ∅ empty_mem_ω, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
        intro y hy
        rcases ((hmem _ _).mp hy).2.2 with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact (h rfl).elim
        · exact (h rfl).elim
      · have hxμ' : x ∈ μ := by
          rcases mem_succ_iff.mp hx with h | h
          · exact (hxμ h).elim
          · exact h
        by_cases hxω : x ∈ (ω : V)
        · refine ⟨succ x, (hmem _ _).mpr ⟨hx, hω _ (ω_succ_closed hxω), Or.inr (Or.inl ⟨hxμ, hxω, rfl⟩)⟩, ?_⟩
          intro y hy
          rcases ((hmem _ _).mp hy).2.2 with ⟨h, _⟩ | ⟨_, _, h⟩ | ⟨_, h, _⟩
          · exact (hxμ h).elim
          · exact h
          · exact (h hxω).elim
        · refine ⟨x, (hmem _ _).mpr ⟨hx, hxμ', Or.inr (Or.inr ⟨hxμ, hxω, rfl⟩)⟩, ?_⟩
          intro y hy
          rcases ((hmem _ _).mp hy).2.2 with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩
          · exact (hxμ h).elim
          · exact (hxω h).elim
          · exact h
  · intro x₁ x₂ y h₁ h₂
    obtain ⟨hx₁, _, c₁⟩ := (hmem _ _).mp h₁
    obtain ⟨hx₂, _, c₂⟩ := (hmem _ _).mp h₂
    have hord : ∀ x, x ∈ succ μ → IsOrdinal x := fun x hx ↦ by
      rcases mem_succ_iff.mp hx with rfl | hx
      · infer_instance
      · exact IsOrdinal.of_mem hx
    have ho₁ := hord x₁ hx₁
    have ho₂ := hord x₂ hx₂
    rcases c₁ with ⟨rfl, rfl⟩ | ⟨hn₁, hω₁, rfl⟩ | ⟨hn₁, hω₁, rfl⟩ <;>
      rcases c₂ with ⟨rfl, h₂'⟩ | ⟨hn₂, hω₂, h₂'⟩ | ⟨hn₂, hω₂, h₂'⟩
    · rfl
    · exact (not_mem_empty (h₂' ▸ mem_succ_self x₂)).elim
    · exact (hω₂ (h₂' ▸ empty_mem_ω)).elim
    · exact (not_mem_empty (h₂'.symm ▸ mem_succ_self x₁)).elim
    · exact succ_injective_ordinal h₂'
    · exact (hω₂ (h₂' ▸ ω_succ_closed hω₁)).elim
    · exact (hω₁ (h₂'.symm ▸ empty_mem_ω)).elim
    · exact (hω₁ (h₂'.symm ▸ ω_succ_closed hω₂)).elim
    · exact h₂'

/-- An infinite initial ordinal is closed under successor. -/
theorem initial_succ_mem {lam μ : V} (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam)
    (hμ : μ ∈ lam) : succ μ ∈ lam := by
  have := hlam.1
  have : IsOrdinal μ := IsOrdinal.of_mem hμ
  rcases IsOrdinal.mem_trichotomy (α := succ μ) (β := lam) with h | h | h
  · exact h
  · exfalso
    have hshift : (ω : V) ⊆ μ → False := by
      intro hωμ
      have hc : succ μ ≤# μ := succ_cardLE_of_omega_subset hωμ
      rw [h] at hc
      exact hlam.2 μ hμ hc
    rcases IsOrdinal.subset_or_supset (α := (ω : V)) (β := μ) with hωμ | hμω
    · exact hshift hωμ
    · have hμω' : μ ∈ (ω : V) := by
        rcases IsOrdinal.subset_iff.mp hμω with heq | hm
        · exact (hshift (by rw [heq])).elim
        · exact hm
      have hs : succ μ ∈ lam := hω _ (ω_succ_closed hμω')
      rw [h] at hs
      exact mem_irrefl lam hs
  · exfalso
    rcases mem_succ_iff.mp h with h | h
    · rw [h] at hμ
      exact mem_irrefl μ hμ
    · exact mem_irrefl lam (IsOrdinal.toIsTransitive.mem_trans h hμ)

end ZFVP
