import ZFVP.SetTheory.PiTwoPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def leastPrefixCutoffBody (Ξ : SetTheorySemisentence 5) : SetTheorySemisentence 5 :=
  “P R one κ δ. !IsOrdinal.dfn δ ∧ !Ξ P R one κ δ ∧
    ∀ β ∈ δ, ¬!Ξ P R one κ β”

theorem leastPrefixCutoffBody_levy {Ξ : SetTheorySemisentence 5} (hΞ : IsPiFormula 2 Ξ)
    (pol : LevyPolarity) : IsLevyFormula pol 3 (leastPrefixCutoffBody Ξ) :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.raise (hΞ.subst _)) (.raise (.boundedAll (.bvar 4) (hΞ.subst _).neg)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem isLeastOrdinal_iff_no_smaller (F : V → Prop) (δ : V) :
    IsLeastOrdinal F δ ↔ IsOrdinal δ ∧ F δ ∧ ∀ β ∈ δ, ¬F β := by
  constructor
  · rintro ⟨hd, hF, hmin⟩
    let := hd
    refine ⟨hd, hF, ?_⟩
    intro β hβ hFb
    exact mem_irrefl β (hmin β (IsOrdinal.of_mem hβ) hFb β hβ)
  · rintro ⟨hd, hF, hmin⟩
    let := hd
    refine ⟨hd, hF, ?_⟩
    intro β hb hFb
    let := hb
    rcases IsOrdinal.mem_trichotomy δ β with hlt | he | hgt
    · exact IsOrdinal.toIsTransitive.transitive _ hlt
    · exact he ▸ subset_refl δ
    · exact False.elim (hmin β hgt hFb)

/-- Least positive witnesses have both third-level bounds. This does not assert
a Sigma3 bound for the default-zero branch of the total selector. -/
theorem leastWoodinPrefixCutoff_deltaThree_uniform :
    ∃ Λ : SetTheorySemisentence 5, (∀ pol, IsLevyFormula pol 3 Λ) ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ P R one κ δ : V, IsForcingPreorder P R → IsForcingTop P R one →
          (∅ : V) ∈ κ →
          (Λ.Evalb ![P, R, one, κ, δ] ↔ IsLeastOrdinal (IsWoodinPrefixCutoff P R one κ) δ) := by
  obtain ⟨Ξ, hΞ, he⟩ := woodinPrefixCutoff_piTwo_uniform.{u}
  refine ⟨leastPrefixCutoffBody Ξ, leastPrefixCutoffBody_levy hΞ, ?_⟩
  intro V _ _ _ P R one κ δ hR ht hk
  have hb : (leastPrefixCutoffBody Ξ).Evalb ![P, R, one, κ, δ] ↔
      IsOrdinal δ ∧ Ξ.Evalb ![P, R, one, κ, δ] ∧ ∀ β ∈ δ, ¬Ξ.Evalb ![P, R, one, κ, β] := by
    simp [leastPrefixCutoffBody, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb, isLeastOrdinal_iff_no_smaller]
  simp only [he V P R one κ _ hR ht hk]

theorem woodinPrefixCutoff_eq_iff_least_of_exists {P R one κ δ : V}
    (hex : ∃ η, IsWoodinPrefixCutoff P R one κ η) :
    δ = woodinPrefixCutoff P R one κ ↔ IsLeastOrdinal (IsWoodinPrefixCutoff P R one κ) δ := by
  obtain ⟨η, hη⟩ := hex
  have hs := woodinPrefixCutoff_spec hη
  constructor
  · rintro rfl
    exact hs
  · intro hd
    exact subset_antisymm (hd.2.2 _ hs.1 hs.2.1) (hs.2.2 _ hd.1 hd.2.1)

end ZFVP
