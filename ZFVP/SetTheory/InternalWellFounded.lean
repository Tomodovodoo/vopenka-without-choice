import ZFVP.SetTheory.LeastRankWitnesses

/-! Well-foundedness relative to the internal subsets of an internal set.
This is distinct from external well-foundedness of a model's membership. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternallyWellFounded (R D : V) : Prop :=
  ∀ A : V, A ⊆ D → IsNonempty A → ∃ x ∈ A, ∀ y ∈ A, ⟨y, x⟩ₖ ∉ R

theorem internallyWellFounded_iff_library (R D : V) : IsInternallyWellFounded R D ↔
    IsWellFoundedRel (fun x ↦ x ∈ D) (fun x y ↦ ⟨x, y⟩ₖ ∈ R) :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.wf⟩

instance isInternallyWellFounded_definable : ℒₛₑₜ-relation[V] IsInternallyWellFounded := by
  unfold IsInternallyWellFounded
  definability

theorem internalWellFounded_induction {R D : V} (hR : IsInternallyWellFounded R D)
    (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (step : ∀ x ∈ D, (∀ y ∈ D, ⟨y, x⟩ₖ ∈ R → P y) → P x) : ∀ x ∈ D, P x := by
  intro x hx
  by_contra hPx
  let B : V := {y ∈ D ; ¬P y}
  have hBD : B ⊆ D := by
    intro y hy
    exact (show y ∈ D ∧ ¬P y from by simpa [B] using hy).1
  have hB : IsNonempty B := ⟨x, by simpa [B] using And.intro hx hPx⟩
  obtain ⟨y, hy, hmin⟩ := hR B hBD hB
  have hy' : y ∈ D ∧ ¬P y := by simpa [B] using hy
  apply hy'.2
  apply step y hy'.1
  intro z hz hzy
  by_contra hPz
  exact hmin z (by simpa [B] using And.intro hz hPz) hzy

theorem rank_decreasing_internallyWellFounded (R D : V)
    (hdec : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ R → rank x ∈ rank y) :
    IsInternallyWellFounded R D := by
  intro A hAD hA
  have hex : ∃ y : V, (fun _ y ↦ y ∈ A) (∅ : V) y := hA.nonempty
  obtain ⟨α, hα, _⟩ := leastWitnessRank_existsUnique (fun _ y ↦ y ∈ A)
    (by definability) ∅ hex
  obtain ⟨x, hx, hrx⟩ := hα.2.1
  refine ⟨x, hx, ?_⟩
  intro y hy hxy
  have hlt := hdec y (hAD y hy) x (hAD x hx) hxy
  rw [hrx] at hlt
  have hle := hα.2.2 (rank y) inferInstance ⟨y, hy, rfl⟩
  exact mem_irrefl (rank y) (hle (rank y) hlt)

theorem rank_kpair_left_lt (x y : V) : rank x ∈ rank ⟨x, y⟩ₖ := by
  have h₁ : rank x ∈ rank ({x} : V) := rank_mem (by simp)
  have h₂ : rank ({x} : V) ∈ rank ⟨x, y⟩ₖ := rank_mem (by simp [kpair])
  exact IsOrdinal.toIsTransitive.mem_trans h₁ h₂

theorem rank_kpair_right_lt (x y : V) : rank y ∈ rank ⟨x, y⟩ₖ := by
  have h₁ : rank y ∈ rank ({x, y} : V) := rank_mem (by simp)
  have h₂ : rank ({x, y} : V) ∈ rank ⟨x, y⟩ₖ := rank_mem (by simp [kpair])
  exact IsOrdinal.toIsTransitive.mem_trans h₁ h₂

theorem rank_lt_of_mem_range {x f : V} (hx : x ∈ range f) : rank x ∈ rank f := by
  obtain ⟨i, hi⟩ := mem_range_iff.mp hx
  exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt i x) (rank_mem hi)

end ZFVP
