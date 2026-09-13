import ZFVP.ModelTheory.CodedZFVPExternal
import ZFVP.SetTheory.CnExtendibleVopenkaSharp

/-! A computable level for a finite set of arbitrary-language Vopenka sentences.
The input sentences themselves bound their defining formulas, so no formula
preimage has to be selected to compute the level.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem levySyntacticBound_le_vopenkaSentence (φ : SetTheorySemisentence 2) :
    levySyntacticBound φ ≤ levySyntacticBound (vopenkaSentence φ) := by
  unfold vopenkaSentence
  change _ ≤ _ + 2
  apply le_trans ?_ (Nat.le_add_right _ _)
  change _ ≤ _ + 2
  apply le_trans ?_ (Nat.le_add_right _ _)
  change _ ≤ max _ _
  apply le_trans ?_ (Nat.le_max_right _ _)
  change _ ≤ max _ _
  apply le_trans ?_ (Nat.le_max_right _ _)
  change _ ≤ _ + 2
  apply le_trans ?_ (Nat.le_add_right _ _)
  change _ ≤ _ + 2
  apply le_trans ?_ (Nat.le_add_right _ _)
  change _ ≤ _ + 2
  apply le_trans ?_ (Nat.le_add_right _ _)
  change _ ≤ max _ _
  apply le_trans ?_ (Nat.le_max_right _ _)
  change _ ≤ max _ _
  apply le_trans ?_ (Nat.le_max_left _ _)
  rw [levySyntacticBound_rew]

def effectiveLanguageReductionLevel (u : Finset SetTheorySentence) : ℕ :=
  u.sup levySyntacticBound + 1

theorem one_le_effectiveLanguageReductionLevel (u : Finset SetTheorySentence) :
    1 ≤ effectiveLanguageReductionLevel u := Nat.le_add_left 1 _

theorem isPiFormula_of_vopenkaSentence_mem {u : Finset SetTheorySentence}
    {φ : SetTheorySemisentence 2} (hφ : vopenkaSentence φ ∈ u) :
    IsPiFormula (effectiveLanguageReductionLevel u + 1) φ := by
  apply (isLevyFormula_syntacticBound φ .pi).mono
  have h := (levySyntacticBound_le_vopenkaSentence φ).trans (Finset.le_sup hφ)
  unfold effectiveLanguageReductionLevel
  omega

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem models_vopenkaSentence_of_effective_pi_vopenka {u : Finset SetTheorySentence}
    (hVP : ∀ φ : SetTheorySemisentence 2,
      IsPiFormula (effectiveLanguageReductionLevel u + 1) φ → VopenkaInstance (V := V) φ)
    {σ : SetTheorySentence} (hu : σ ∈ u) (hσ : σ ∈ vopenkaTheory) : V↓[ℒₛₑₜ] ⊧ σ := by
  obtain ⟨φ, rfl⟩ := hσ
  exact (eval_vopenkaSentence φ).mpr (hVP φ (isPiFormula_of_vopenkaSentence_mem hu))

theorem cnExtendible_unbounded_implies_effective_finite_vopenka (u : Finset SetTheorySentence)
    (hE : ∀ α : V, IsOrdinal α → ∃ κ : V,
      α ∈ κ ∧ IsCnExtendible (effectiveLanguageReductionLevel u) κ)
    {σ : SetTheorySentence} (hu : σ ∈ u) (hσ : σ ∈ vopenkaTheory) : V↓[ℒₛₑₜ] ⊧ σ :=
  models_vopenkaSentence_of_effective_pi_vopenka
    (fun φ hφ ↦ cnExtendible_unbounded_implies_pi_vopenka_sharp hE φ hφ) hu hσ

/-- The arbitrary-language Pi fragment at the computed finite level. -/
def effectivePiVopenkaTheory (u : Finset SetTheorySentence) : Theory ℒₛₑₜ :=
  𝗭𝗙 ∪ {σ | ∃ φ : SetTheorySemisentence 2,
    IsPiFormula (effectiveLanguageReductionLevel u + 1) φ ∧ vopenkaSentence φ = σ}

instance (u : Finset SetTheorySentence) : 𝗘𝗤 ℒₛₑₜ ⪯ effectivePiVopenkaTheory u :=
  Entailment.WeakerThan.ofSubset fun _ hφ ↦ Or.inl (ZermeloFraenkel.axiom_of_equality _ hφ)

/-- The computed fragment proves every Vopenka sentence in the finite input. -/
theorem provable_vopenkaSentence_of_effective_pi_scheme (u : Finset SetTheorySentence)
    {σ : SetTheorySentence} (hu : σ ∈ u) (hσ : σ ∈ vopenkaTheory) :
    effectivePiVopenkaTheory u ⊢ σ := by
  obtain ⟨φ, rfl⟩ := hσ
  exact Entailment.by_axm (Or.inr ⟨φ, isPiFormula_of_vopenkaSentence_mem hu, rfl⟩)

end ZFVP
