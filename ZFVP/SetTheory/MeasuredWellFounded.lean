import ZFVP.SetTheory.InternalWellFounded

/-! Definable ordinal measures establish internal well-foundedness. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalMeasure_internallyWellFounded (R D : V) (μ : V → V)
    (hμ : ℒₛₑₜ-function₁ μ) (hord : ∀ x ∈ D, IsOrdinal (μ x))
    (hdec : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ R → μ x ∈ μ y) :
    IsInternallyWellFounded R D := by
  intro A hAD hA
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨α, hα, _⟩ := leastOrdinal_existsUnique (fun α ↦ ∃ x ∈ A, μ x = α)
    (by definability) ⟨μ a, hord a (hAD a ha), a, ha, rfl⟩
  obtain ⟨x, hx, hμx⟩ := hα.2.1
  refine ⟨x, hx, ?_⟩
  intro y hy hyx
  have hlt := hdec y (hAD y hy) x (hAD x hx) hyx
  rw [hμx] at hlt
  have hle := hα.2.2 (μ y) (hord y (hAD y hy)) ⟨y, hy, rfl⟩
  exact mem_irrefl (μ y) (hle (μ y) hlt)

theorem projectedRank_internallyWellFounded (R D : V) (f : V → V)
    (hf : ℒₛₑₜ-function₁ f)
    (hdec : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ R → rank (f x) ∈ rank (f y)) :
    IsInternallyWellFounded R D :=
  ordinalMeasure_internallyWellFounded R D (fun x ↦ rank (f x)) (by definability)
    (fun _ _ ↦ inferInstance) hdec

theorem projectedRank_induction (D : V) (f : V → V) (hf : ℒₛₑₜ-function₁ f)
    (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (step : ∀ x ∈ D, (∀ y ∈ D, rank (f y) ∈ rank (f x) → P y) → P x) :
    ∀ x ∈ D, P x := by
  let R : V := {p ∈ D ×ˢ D ; rank (f (kpair.π₁ p)) ∈ rank (f (kpair.π₂ p))}
  have he (x y : V) : ⟨x, y⟩ₖ ∈ R ↔ x ∈ D ∧ y ∈ D ∧ rank (f x) ∈ rank (f y) := by
    simp [R, and_assoc]
  have hw : IsInternallyWellFounded R D := projectedRank_internallyWellFounded R D f hf
    (fun x _ y _ hxy ↦ ((he x y).mp hxy).2.2)
  apply internalWellFounded_induction hw P hP
  intro x hx ih
  exact step x hx (fun y hy hlt ↦ ih y hy ((he y x).mpr ⟨hy, hx, hlt⟩))

end ZFVP
