import ZFVP.SetTheory.Hierarchy
import ZFVP.SetTheory.FunctionValue

/-! Transfinite iteration of a definable operation with unions at limits: `iterate F A 0 = A`,
`iterate F A (succ ξ) = F (iterate F A ξ)` and `iterate F A λ = ⋃_{ξ < λ} iterate F A ξ` at
limits. For inflationary `F` the iteration is monotone. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The recursion step: on the graph `s` of the earlier stages, the start at stage `0`, the
operation at successors and the union at limits. -/
noncomputable def iterStep (F : V → V) (A s : V) : V := by
  classical
  exact if ∃ ξ, domain s = succ ξ then F (s ‘ (⋃ˢ domain s)) else
    if domain s = ∅ then A else ⋃ˢ range s

theorem iterStep_definable {F : V → V} (hF : ℒₛₑₜ-function₁ F) (A : V) :
    ℒₛₑₜ-function₁ (iterStep F A) := by
  have h : ℒₛₑₜ-relation (fun y s : V ↦
      ((∃ ξ, domain s = succ ξ) ∧ y = F (s ‘ (⋃ˢ domain s))) ∨
      ((¬ ∃ ξ, domain s = succ ξ) ∧ domain s = ∅ ∧ y = A) ∨
      ((¬ ∃ ξ, domain s = succ ξ) ∧ domain s ≠ ∅ ∧ y = ⋃ˢ range s)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = iterStep F A (v 1) ↔ _
  have hns : ∀ x : V, ¬ (∅ : V) = succ x := fun x hx ↦ not_mem_empty (hx ▸ mem_succ_self x)
  by_cases h1 : ∃ ξ, domain (v 1) = succ ξ
  · simp only [iterStep]
    rw [if_pos h1]
    simp [h1]
  · by_cases h2 : domain (v 1) = ∅
    · simp only [iterStep]
      rw [if_neg h1, if_pos h2]
      simp [h1, h2, hns]
    · simp only [iterStep]
      rw [if_neg h1, if_neg h2]
      simp [h1, h2]

/-- The transfinite iteration of `F` starting at `A`. -/
noncomputable def iterate (F : V → V) (hF : ℒₛₑₜ-function₁ F) (A : V) (α : V) : V :=
  Replacement.transfiniteRec (iterStep F A) (iterStep_definable hF A) α

theorem iterate_definable {F : V → V} (hF : ℒₛₑₜ-function₁ F) (A : V) :
    ℒₛₑₜ-function₁ (iterate F hF A) :=
  Replacement.transfiniteRec_definable (iterStep_definable hF A)

theorem iterate_recursion {F : V → V} (hF : ℒₛₑₜ-function₁ F) (A : V) (α : Ordinal V) :
    iterate F hF A (α : V) = iterStep F A (definableGraph (α : V) (iterate F hF A) (iterate_definable hF A)) :=
  Replacement.transfiniteRec_spec (iterStep F A) (iterStep_definable hF A) α

theorem sUnion_succ_ordinal (ξ : V) [IsOrdinal ξ] : ⋃ˢ (succ ξ) = ξ := by
  apply mem_ext
  intro x
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases mem_succ_iff.mp hy with rfl | hy
    · exact hxy
    · exact IsOrdinal.toIsTransitive.mem_trans hxy hy
  · intro hx
    exact ⟨ξ, mem_succ_self ξ, hx⟩

theorem iterate_zero {F : V → V} (hF : ℒₛₑₜ-function₁ F) (A : V) : iterate F hF A ∅ = A := by
  have h := iterate_recursion hF A (IsOrdinal.toOrdinal (∅ : V))
  change iterate F hF A ∅ = iterStep F A (definableGraph ∅ _ _) at h
  rw [h]
  have hd : domain (definableGraph (∅ : V) (iterate F hF A) (iterate_definable hF A)) = ∅ :=
    domain_definableGraph _ _ _
  have hs : ¬ ∃ ξ : V, domain (definableGraph (∅ : V) (iterate F hF A) (iterate_definable hF A)) = succ ξ := by
    rintro ⟨ξ, hξ⟩
    rw [hd] at hξ
    exact not_mem_empty (hξ ▸ mem_succ_self ξ)
  simp only [iterStep]
  rw [if_neg hs, if_pos hd]

theorem iterate_succ {F : V → V} (hF : ℒₛₑₜ-function₁ F) (A ξ : V) [IsOrdinal ξ] :
    iterate F hF A (succ ξ) = F (iterate F hF A ξ) := by
  have h := iterate_recursion hF A (IsOrdinal.toOrdinal (succ ξ))
  change iterate F hF A (succ ξ) = iterStep F A (definableGraph (succ ξ) _ _) at h
  rw [h]
  have hd : domain (definableGraph (succ ξ) (iterate F hF A) (iterate_definable hF A)) = succ ξ :=
    domain_definableGraph _ _ _
  have hs : ∃ ζ : V, domain (definableGraph (succ ξ) (iterate F hF A) (iterate_definable hF A)) = succ ζ :=
    ⟨ξ, hd⟩
  simp only [iterStep]
  rw [if_pos hs, hd, sUnion_succ_ordinal]
  congr 1
  exact value_eq_of_kpair_mem ((mem_definableGraph_iff _ _ _ _).mpr ⟨ξ, mem_succ_self ξ, rfl⟩)

/-- A limit ordinal: nonzero and not a successor. -/
def IsLimitOrdinal (lam : V) : Prop := IsOrdinal lam ∧ lam ≠ ∅ ∧ ¬ ∃ ξ, lam = succ ξ

theorem iterate_limit {F : V → V} (hF : ℒₛₑₜ-function₁ F) (A lam : V) (hlam : IsLimitOrdinal lam) :
    iterate F hF A lam = ⋃ˢ repl (iterate F hF A) (iterate_definable hF A) lam := by
  have : IsOrdinal lam := hlam.1
  have h := iterate_recursion hF A (IsOrdinal.toOrdinal lam)
  change iterate F hF A lam = iterStep F A (definableGraph lam _ _) at h
  rw [h]
  have hd : domain (definableGraph lam (iterate F hF A) (iterate_definable hF A)) = lam :=
    domain_definableGraph _ _ _
  have hs : ¬ ∃ ζ : V, domain (definableGraph lam (iterate F hF A) (iterate_definable hF A)) = succ ζ := by
    rw [hd]
    exact hlam.2.2
  have h0 : domain (definableGraph lam (iterate F hF A) (iterate_definable hF A)) ≠ ∅ := by
    rw [hd]
    exact hlam.2.1
  simp only [iterStep]
  rw [if_neg hs, if_neg h0, range_definableGraph]

theorem mem_iterate_limit_iff {F : V → V} (hF : ℒₛₑₜ-function₁ F) (A lam : V)
    (hlam : IsLimitOrdinal lam) (x : V) :
    x ∈ iterate F hF A lam ↔ ∃ ξ ∈ lam, x ∈ iterate F hF A ξ := by
  rw [iterate_limit hF A lam hlam, mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨ξ, hξ, rfl⟩ := (repl_spec _).mp hy
    exact ⟨ξ, hξ, hxy⟩
  · rintro ⟨ξ, hξ, hx⟩
    exact ⟨_, (repl_spec _).mpr ⟨ξ, hξ, rfl⟩, hx⟩

theorem ordinal_cases (α : V) [IsOrdinal α] : α = ∅ ∨ (∃ ξ, IsOrdinal ξ ∧ α = succ ξ) ∨ IsLimitOrdinal α := by
  by_cases h0 : α = ∅
  · exact Or.inl h0
  by_cases hs : ∃ ξ, α = succ ξ
  · obtain ⟨ξ, rfl⟩ := hs
    exact Or.inr (Or.inl ⟨ξ, IsOrdinal.of_mem (mem_succ_self ξ), rfl⟩)
  · exact Or.inr (Or.inr ⟨inferInstance, h0, hs⟩)

/-- For an inflationary operation the iteration is monotone. -/
theorem iterate_mono {F : V → V} (hF : ℒₛₑₜ-function₁ F) (hincl : ∀ x, x ⊆ F x) (A : V) :
    ∀ η : Ordinal V, ∀ ξ ∈ (η : V), iterate F hF A ξ ⊆ iterate F hF A η := by
  have hdef : ℒₛₑₜ-function₁ (iterate F hF A) := iterate_definable hF A
  apply transfinite_induction (fun η : V ↦ ∀ ξ ∈ η, iterate F hF A ξ ⊆ iterate F hF A η)
    (by definability)
  intro η ih ξ hξ
  have hηo : IsOrdinal (η : V) := η.ordinal
  rcases ordinal_cases (η : V) with h0 | ⟨ζ, hζ, hζe⟩ | hlim
  · rw [h0] at hξ
    exact (not_mem_empty hξ).elim
  · have hζo : IsOrdinal ζ := hζ
    rw [hζe] at hξ ⊢
    rw [iterate_succ]
    rcases mem_succ_iff.mp hξ with rfl | hξζ
    · exact hincl _
    · have hζη : (IsOrdinal.toOrdinal ζ : Ordinal V) < η := by
        change ζ ∈ (η : V)
        rw [hζe]
        exact mem_succ_self ζ
      intro x hx
      exact hincl _ x (ih (IsOrdinal.toOrdinal ζ) hζη ξ hξζ x hx)
  · intro x hx
    rw [mem_iterate_limit_iff hF A _ hlim]
    exact ⟨ξ, hξ, hx⟩

end ZFVP
