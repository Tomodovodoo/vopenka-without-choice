import ZFVP.ModelTheory.InfinitaryHenkinWeakTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction
open HenkinLanguage KeislerDerivation FragmentClosure
universe u
variable {L : Language.{u}} [L.Eq] [L.Encodable]

def originalSeed (Γ : Set (Sentence L)) : Set (TaggedFormula (limit L)) :=
  (fun φ : Sentence L ↦ ⟨0, φ.lMap (Language.Hom.add₁ L (Language.constant ℕ))⟩) '' Γ

theorem originalSeed_countable {Γ : Set (Sentence L)} (hΓ : Γ.Countable) :
    (originalSeed Γ).Countable := hΓ.image _

theorem originalSeed_supported (Γ : Set (Sentence L)) :
    ∀ a ∈ originalSeed Γ, FiniteSupport a.2 := by
  rintro a ⟨φ, hφ, rfl⟩
  exact finiteSupport_original φ

/-- Syntactic consistency gives a countable model with an extensional monotone
weak quantifier. Standard uncountability completeness requires a further extension
construction; this theorem makes no such identification. -/
theorem exists_countable_weak_model (Γ : Set (Sentence L))
    (hc : Consistent Γ) (hΓ : Γ.Countable) :
    ∃ M : Type u, ∃ _ : Countable M, ∃ _ : Nonempty M, ∃ s : Structure L M,
      @Structure.Eq L M s _ ∧ ∃ Q : Set M → Prop, Monotone Q ∧
        ∀ φ ∈ Γ, @Formula.WeakEval L M s Q 0 φ Fin.elim0 := by
  obtain ⟨H⟩ := exists_closedFragmentExtension Γ hc hΓ (originalSeed Γ)
    (originalSeed_countable hΓ) (originalSeed_supported Γ)
  let η : L →ᵥ limit L := Language.Hom.add₁ L (Language.constant ℕ)
  let s : Structure L H.Domain := H.termStructure.lMap η
  have hEq : @Structure.Eq L H.Domain s _ := by
    constructor
    intro a b
    exact Structure.Eq.eq (L := limit L) a b
  refine ⟨H.Domain, inferInstance, inferInstance, s, hEq, H.weakQuantifier,
    fun _ _ h ↦ H.weakQuantifier_mono h, ?_⟩
  intro φ hφ
  have hm : φ.lMap η ∈ H.carrier := H.includes ⟨φ, hφ, rfl⟩
  have hf : ⟨0, φ.lMap η⟩ ∈ FragmentClosure.carrier (originalSeed Γ) :=
    subset_carrier _ ⟨φ, hφ, rfl⟩
  have ht := (H.weak_sentence_truth _ hf).mpr hm
  exact (Formula.weakEval_lMap η H.termStructure H.weakQuantifier φ Fin.elim0).mp ht

end HenkinConstruction
end ZFVP.Infinitary

