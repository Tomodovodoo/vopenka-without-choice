import ZFVP.SetTheory.LevyForcingWitnessBound
import ZFVP.SetTheory.DeltaOneSaturatedName
import ZFVP.SetTheory.DeltaOneUnionName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingWitnessPoolEntryFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 5 :=
  (forcingWitnessEntryFormula θ).subst ![.bvar 0, .bvar 1, .bvar 3, .bvar 2, .bvar 4]

def levyWitnessNameGraphFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 4 :=
  “E P R a. ∃ α, ∃ H, !(leastForcingWitnessBoundBody θ) α P R a ∧
    !piOneHierarchyFormula H α ∧
      !(saturatedNameGraphFormula (forcingWitnessPoolEntryFormula θ) (forcingWitnessPoolEntryFormula θ)) E P R H a”

def levyUniqueNameGraphFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 4 :=
  “N P R a. ∃ E, !(levyWitnessNameGraphFormula θ) E P R a ∧ !sigmaOneUnionNameFormula N P R E”

theorem forcingWitnessPoolEntryFormula_sigma {k : ℕ} {θ : SetTheorySemisentence 5}
    (hθ : IsSigmaFormula (k + 1) θ) : IsSigmaFormula (k + 1) (forcingWitnessPoolEntryFormula θ) :=
  (forcingWitnessEntryFormula_sigma hθ).subst _

theorem levyWitnessNameGraphFormula_sigma {k : ℕ} {θ : SetTheorySemisentence 5}
    (hθ : IsSigmaFormula (k + 1) θ) : IsSigmaFormula (k + 2) (levyWitnessNameGraphFormula θ) :=
  .exs (.exs (.and ((leastForcingWitnessBoundBody_levy hθ .sigma).subst _)
    (.and ((piOneHierarchyFormula_piOne.raise.mono (by omega)).subst _)
      ((saturatedNameGraphFormula_levy
        (forcingWitnessPoolEntryFormula_sigma hθ).raise
        (forcingWitnessPoolEntryFormula_sigma hθ).raise).subst _))))

theorem levyUniqueNameGraphFormula_sigma {k : ℕ} {θ : SetTheorySemisentence 5}
    (hθ : IsSigmaFormula (k + 1) θ) : IsSigmaFormula (k + 2) (levyUniqueNameGraphFormula θ) :=
  .exs (.and ((levyWitnessNameGraphFormula_sigma hθ).subst _)
    ((sigmaOneUnionNameFormula_sigmaOne.mono (by omega)).subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_forcingWitnessPoolEntryFormula (θ : SetTheorySemisentence 5) (P R a ν p : V) :
    (forcingWitnessPoolEntryFormula θ).Evalb ![P, R, ν, a, p] ↔
      IsForcingName P ν ∧ θ.Evalb ![P, R, a, ν, p] := by
  simp [forcingWitnessPoolEntryFormula, forcingWitnessEntryFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, Semiformula.Evalb]

theorem eval_levyWitnessNameGraphFormula (θ : SetTheorySemisentence 5) (E P R a b : V)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    (he : ∀ ν : V, IsForcingName P ν → ∀ p : V,
      θ.Evalb ![P, R, a, ν, p] ↔ p ∈ F b ν) :
    (levyWitnessNameGraphFormula θ).Evalb ![E, P, R, a] ↔ E = forcingWitnessName P F hF b := by
  have hs := leastOrdinalOrZero_spec (IsForcingWitnessBound P F)
    (forcingWitnessBound_definable P F hF) b (forcingWitnessBound_exists P F hF b)
  let : IsOrdinal (forcingWitnessBound P F hF b) := hs.1
  have hb : (levyWitnessNameGraphFormula θ).Evalb ![E, P, R, a] ↔
      ∃ α H : V, (leastForcingWitnessBoundBody θ).Evalb ![α, P, R, a] ∧
        (IsOrdinal α ∧ H = hierarchy α) ∧
        (saturatedNameGraphFormula (forcingWitnessPoolEntryFormula θ) (forcingWitnessPoolEntryFormula θ)).Evalb ![E, P, R, H, a] := by
    simp [levyWitnessNameGraphFormula, IsHierarchySegment, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  have hentry (ν p : V) : (forcingWitnessPoolEntryFormula θ).Evalb ![P, R, ν, a, p] ↔
      IsForcingName P ν ∧ p ∈ F b ν := by
    rw [eval_forcingWitnessPoolEntryFormula]
    exact and_congr_right fun hn ↦ he ν hn p
  have hpool (H : V) :
      (saturatedNameGraphFormula (forcingWitnessPoolEntryFormula θ) (forcingWitnessPoolEntryFormula θ)).Evalb ![E, P, R, H, a] ↔
      (∀ z ∈ E, ∃ ν ∈ H, ∃ p ∈ P, z = ⟨ν, p⟩ₖ ∧ IsForcingName P ν ∧ p ∈ F b ν) ∧
        ∀ ν ∈ H, ∀ p ∈ P, (IsForcingName P ν ∧ p ∈ F b ν) → ⟨ν, p⟩ₖ ∈ E := by
    simp [saturatedNameGraphFormula, hentry, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [hb]
  simp only [eval_leastForcingWitnessBoundBody θ P R a b _ F hF he]
  constructor
  · rintro ⟨α, H, rfl, ⟨_, rfl⟩, h⟩
    obtain ⟨hf, hb⟩ := (hpool _).mp h
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨ν, hν, p, hp, rfl, hn, ht⟩ := hf z hz
      exact (mem_forcingWitnessName_iff _ _ _ _ _ _).mpr ⟨hν, hp, hn, ht⟩
    · intro hz
      obtain ⟨ν, hν, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
      exact hb ν hν p hp ((mem_forcingWitnessName_iff _ _ _ _ _ _).mp hz).2.2
  · intro hE
    refine ⟨forcingWitnessBound P F hF b, hierarchy (forcingWitnessBound P F hF b), rfl,
      ⟨inferInstance, rfl⟩, (hpool _).mpr ?_⟩
    rw [hE]
    constructor
    · intro z hz
      obtain ⟨ν, hν, p, hp, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
      exact ⟨ν, hν, p, hp, rfl, ((mem_forcingWitnessName_iff _ _ _ _ _ _).mp hz).2.2⟩
    · intro ν hν p hp h
      exact (mem_forcingWitnessName_iff _ _ _ _ _ _).mpr ⟨hν, hp, h⟩

theorem eval_levyUniqueNameGraphFormula (θ : SetTheorySemisentence 5) (N P R a b : V)
    (F : V → V → V) (hF : ℒₛₑₜ-function₂ F)
    (he : ∀ ν : V, IsForcingName P ν → ∀ p : V,
      θ.Evalb ![P, R, a, ν, p] ↔ p ∈ F b ν) :
    (levyUniqueNameGraphFormula θ).Evalb ![N, P, R, a] ↔ N = forcingUniqueName P R F hF b := by
  have hb : (levyUniqueNameGraphFormula θ).Evalb ![N, P, R, a] ↔
      ∃ E : V, (levyWitnessNameGraphFormula θ).Evalb ![E, P, R, a] ∧ N = forcingUnionName P R E := by
    simp [levyUniqueNameGraphFormula, eval_sigmaOneUnionNameFormula,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [hb]
  simp only [eval_levyWitnessNameGraphFormula θ _ P R a b F hF he]
  simp [forcingUniqueName]

end ZFVP
