import ZFVP.ModelTheory.InfinitaryAdequateHenkin
import ZFVP.ModelTheory.InfinitaryWeakModelExistence

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction
open HenkinLanguage
universe u
variable {L : Language.{u}} [L.Eq] [L.Encodable]

omit [L.Eq] in
theorem originalSeed_mem {Γ : Set (Sentence L)} {φ : Sentence L} (hφ : φ ∈ Γ) :
    ⟨0, φ.lMap (Language.Hom.add₁ L (Language.constant ℕ))⟩ ∈
      FragmentClosure.carrier (SequenceClosure.carrier (originalSeed Γ)) :=
  FragmentClosure.subset_carrier _ (SequenceClosure.subset_carrier _ ⟨φ, hφ, rfl⟩)

/-- Syntactic consistency supplies the adequate initial model for the actual
extension construction, in the fixed countable Henkin language. -/
theorem exists_adequate_initial_model (Γ : Set (Sentence L))
    (hc : KeislerDerivation.Consistent Γ) (hΓ : Γ.Countable) :
    ∃ M : WeakModel.{u,u} (limit L), M.Adequate (originalSeed Γ) ∧
      ∀ φ ∈ Γ, Formula.WeakEval M.Q
        (φ.lMap (Language.Hom.add₁ L (Language.constant ℕ))) Fin.elim0 := by
  obtain ⟨H⟩ := exists_sequenceFragmentExtension Γ hc hΓ (originalSeed Γ)
    (originalSeed_countable hΓ) (originalSeed_supported Γ)
  refine ⟨H.asWeakModel, H.asWeakModel_adequate, ?_⟩
  intro φ hφ
  exact (H.weak_sentence_truth _ (originalSeed_mem hφ)).mpr (H.includes ⟨φ, hφ, rfl⟩)

end HenkinConstruction
end ZFVP.Infinitary
