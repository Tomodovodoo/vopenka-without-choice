import ZFVP.ModelTheory.InfinitaryAdequateStandardModel
import ZFVP.ModelTheory.InfinitaryAdequateInitialModel

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u
namespace KeislerDerivation
open HenkinConstruction HenkinLanguage
variable {L : Language.{u}} [L.Eq] [L.Encodable]

/-- Standard uncountability completeness for the exact nonempty equality
calculus: the model is constructed from consistency, with size at most aleph-one. -/
theorem exists_standard_model (Γ : Set (Sentence L))
    (hc : Consistent Γ) (hΓ : Γ.Countable) :
    ∃ N : Type, ∃ _ : Nonempty N, ∃ s : Structure L N,
      @Structure.Eq L N s _ ∧ Cardinal.mk N ≤ Cardinal.aleph 1 ∧
        ∀ φ ∈ Γ, @Formula.Eval L N s 0 φ Fin.elim0 := by
  obtain ⟨M, hM, ht⟩ := exists_adequate_initial_model Γ hc hΓ
  obtain ⟨N, hN, s, hEq, hsize, f, hf, htruth⟩ :=
    WeakModel.exists_standard_elementary_extension hM (originalSeed_countable hΓ)
  let : Nonempty N := hN
  let : Structure (limit L) N := s
  let : Structure.Eq (limit L) N := hEq
  let η : L →ᵥ limit L := Language.Hom.add₁ L (Language.constant ℕ)
  let s₀ : Structure L N := s.lMap η
  have hEq₀ : @Structure.Eq L N s₀ _ := by
    constructor
    intro a b
    exact Structure.Eq.eq (L := limit L) a b
  refine ⟨N, hN, s₀, hEq₀, hsize, ?_⟩
  intro φ hφ
  have h := (htruth (φ.lMap η) (originalSeed_mem hφ) Fin.elim0).mpr (ht φ hφ)
  have hb : f ∘ (Fin.elim0 : Fin 0 → M.Domain) = (Fin.elim0 : Fin 0 → N) := Subsingleton.elim _ _
  rw [hb] at h
  exact (Formula.eval_lMap η s φ Fin.elim0).mp h

/-- The reverse implication uses soundness in structures with actual equality. -/
theorem consistent_iff_has_standard_model (Γ : Set (Sentence L)) (hΓ : Γ.Countable) :
    Consistent Γ ↔
      ∃ N : Type, ∃ _ : Nonempty N, ∃ s : Structure L N,
        @Structure.Eq L N s _ ∧ Cardinal.mk N ≤ Cardinal.aleph 1 ∧
          ∀ φ ∈ Γ, @Formula.Eval L N s 0 φ Fin.elim0 := by
  constructor
  · exact fun hc ↦ exists_standard_model Γ hc hΓ
  · rintro ⟨N, hN, s, hEq, _, ht⟩
    let : Nonempty N := hN
    let : Structure L N := s
    let : Structure.Eq L N := hEq
    exact consistent_of_model ht

theorem satisfiable_of_consistent (φ : Sentence L) (hc : Consistent {φ}) : Satisfiable φ := by
  obtain ⟨N, hN, s, hEq, hsize, ht⟩ := exists_standard_model {φ} hc (Set.countable_singleton φ)
  exact ⟨N, hN, s, ht φ (Set.mem_singleton φ)⟩

/-- Failure of standard satisfiability supplies an actual derivation of false,
which can be fed to the countable soundness-support extraction. -/
theorem refutation_of_not_satisfiable (φ : Sentence L) (hφ : ¬Satisfiable φ) :
    KeislerDerivation {φ} (.neg (.fo .verum : Sentence L)) := by
  classical
  by_contra h
  exact hφ (satisfiable_of_consistent φ h)

end KeislerDerivation
end ZFVP.Infinitary
