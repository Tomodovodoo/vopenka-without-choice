import ZFVP.SetTheory.CnExtendibleVopenka
import ZFVP.ModelTheory.CodedZFVPExternal

/-! # Finite fragments of the Vopenka scheme sit at one Levy level

For every finite set of instances of the arbitrary-language Vopenka scheme there is an
`N ≥ 1` with `ZF + VP(Π_{N+1}) ⊢ F₀`. The sentence-indexed bound chooses formula preimages
noncomputably, so this module does not prove the paper's effective computation claim.

Here `VP(Π_{N+1})` is itself the arbitrary-language scheme. The paper instead reduces to a
fixed finite relational signature using endomorphism-rigid labels and a satisfaction code.
That fixed-language coding lemma is not proved in this module.
`ZFVP.VopenkaInstance` in `ZFVP/SetTheory/VopenkaScheme.lean` already
quantifies over an arbitrary internal language code `L : V`, and `ZFVP/ModelTheory/LanguageCode.lean`
lets the symbol sets of `L` be arbitrary internal sets with no enumeration attached. So the
antecedent formalized here is stronger than the paper's fixed-signature antecedent.
No `InternalChoice` hypothesis appears anywhere below.

What is left is the arithmetic of the level `N`. Each instance is named by a formula
`φ : SetTheorySemisentence 2` whose Levy complexity is bounded by the syntactic count
`levySyntacticBound φ`. Taking the max over the finite set, together with the two fixed
dictionary bounds that `cnExtendible_unbounded_implies_pi_vopenka` needs, gives the `N`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

section Preimage

open Classical in
/-- A formula whose Vopenka sentence is `σ`, when there is one, and `⊤` otherwise.
Used so that a member of `vopenkaTheory` can be handed back a name without knowing that
`vopenkaSentence` is injective. -/
noncomputable def vopenkaPreimage (σ : SetTheorySentence) : SetTheorySemisentence 2 :=
  if h : ∃ φ : SetTheorySemisentence 2, vopenkaSentence φ = σ then h.choose else ⊤

theorem vopenkaPreimage_spec {σ : SetTheorySentence} (hσ : σ ∈ vopenkaTheory) :
    vopenkaSentence (vopenkaPreimage σ) = σ := by
  have h : ∃ φ : SetTheorySemisentence 2, vopenkaSentence φ = σ := hσ
  rw [vopenkaPreimage, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

end Preimage

section Level

/-- The syntactic level attached to a finite set of Vopenka sentences: the largest of the two
fixed dictionary bounds and the Levy bounds of the chosen names of the members. -/
noncomputable def languageReductionBase (u : Finset SetTheorySentence) : ℕ :=
  max (max coreSyntaxDictionaryBound codedElementaryEmbeddingBound)
    (u.sup fun σ ↦ levySyntacticBound (vopenkaPreimage σ))

/-- The paper's `N` for a finite set of Vopenka sentences. -/
noncomputable def languageReductionLevel (u : Finset SetTheorySentence) : ℕ :=
  languageReductionBase u + 1

theorem languageReductionLevel_eq (u : Finset SetTheorySentence) :
    languageReductionLevel u = languageReductionBase u + 1 := rfl

theorem one_le_languageReductionLevel (u : Finset SetTheorySentence) :
    1 ≤ languageReductionLevel u := Nat.le_add_left 1 _

theorem coreSyntaxDictionaryBound_le (u : Finset SetTheorySentence) :
    coreSyntaxDictionaryBound ≤ languageReductionBase u + 1 :=
  le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) (Nat.le_succ _)

theorem codedElementaryEmbeddingBound_le (u : Finset SetTheorySentence) :
    codedElementaryEmbeddingBound ≤ languageReductionBase u + 1 :=
  le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (Nat.le_succ _)

/-- Every member of `u` has a name of Levy complexity at most `N + 1`, which is the level
that `cnExtendible_unbounded_implies_pi_vopenka` consumes. -/
theorem isPiFormula_vopenkaPreimage {u : Finset SetTheorySentence} {σ : SetTheorySentence}
    (hσ : σ ∈ u) : IsPiFormula (languageReductionLevel u + 1) (vopenkaPreimage σ) := by
  refine (isLevyFormula_syntacticBound (vopenkaPreimage σ) .pi).mono ?_
  have h1 : levySyntacticBound (vopenkaPreimage σ) ≤ languageReductionBase u :=
    le_trans (Finset.le_sup (f := fun σ ↦ levySyntacticBound (vopenkaPreimage σ)) hσ)
      (Nat.le_max_right _ _)
  simp only [languageReductionLevel]
  omega

end Level

section Instances

/-- The level attached to a finite set of Vopenka instances given as formulas. -/
noncomputable def instanceReductionLevel (F : Finset (SetTheorySemisentence 2)) : ℕ :=
  max (max coreSyntaxDictionaryBound codedElementaryEmbeddingBound) (F.sup levySyntacticBound) + 1

theorem one_le_instanceReductionLevel (F : Finset (SetTheorySemisentence 2)) :
    1 ≤ instanceReductionLevel F := Nat.le_add_left 1 _

end Instances

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A model of the `Π_{N+1}` fragment of the Vopenka scheme satisfies every member of `u`
that is a Vopenka sentence, for `N = languageReductionLevel u`. -/
theorem models_vopenkaSentence_of_pi_vopenka {u : Finset SetTheorySentence}
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula (languageReductionLevel u + 1) φ →
      VopenkaInstance (V := V) φ)
    {σ : SetTheorySentence} (hu : σ ∈ u) (hσ : σ ∈ vopenkaTheory) : V↓[ℒₛₑₜ] ⊧ σ := by
  rw [← vopenkaPreimage_spec hσ, eval_vopenkaSentence]
  exact hVP _ (isPiFormula_vopenkaPreimage hu)

/-- The paper's statement for a finite set of instances given as formulas: the `Π_{N+1}`
fragment gives all of them, with `N = instanceReductionLevel F`. -/
theorem vopenkaInstance_of_pi_vopenka (F : Finset (SetTheorySemisentence 2))
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula (instanceReductionLevel F + 1) φ →
      VopenkaInstance (V := V) φ) :
    ∀ φ ∈ F, VopenkaInstance (V := V) φ := by
  intro φ hφ
  refine hVP φ ((isLevyFormula_syntacticBound φ .pi).mono ?_)
  have h1 : levySyntacticBound φ ≤ F.sup levySyntacticBound := Finset.le_sup hφ
  have h2 : F.sup levySyntacticBound ≤
      max (max coreSyntaxDictionaryBound codedElementaryEmbeddingBound)
        (F.sup levySyntacticBound) := Nat.le_max_right _ _
  simp only [instanceReductionLevel]
  omega

/-- Unboundedly many `C(N)`-extendible cardinals give every member of `u` that is a Vopenka
sentence, for the single level `N = languageReductionLevel u`. -/
theorem cnExtendible_unbounded_implies_finite_vopenka (u : Finset SetTheorySentence)
    (hE : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible (languageReductionLevel u) κ)
    {σ : SetTheorySentence} (hu : σ ∈ u) (hσ : σ ∈ vopenkaTheory) : V↓[ℒₛₑₜ] ⊧ σ :=
  models_vopenkaSentence_of_pi_vopenka
    (fun φ hφ ↦ cnExtendible_unbounded_implies_pi_vopenka
      (coreSyntaxDictionaryBound_le u) (codedElementaryEmbeddingBound_le u) hE φ hφ) hu hσ

/-- The `Π_{N+1}` fragment of the Vopenka scheme, as an external theory. -/
def piVopenkaTheory (u : Finset SetTheorySentence) : Theory ℒₛₑₜ :=
  𝗭𝗙 ∪ {σ | ∃ φ : SetTheorySemisentence 2,
    IsPiFormula (languageReductionLevel u + 1) φ ∧ vopenkaSentence φ = σ}

instance (u : Finset SetTheorySentence) : 𝗘𝗤 ℒₛₑₜ ⪯ piVopenkaTheory u :=
  Entailment.WeakerThan.ofSubset fun _ hφ ↦ Or.inl (ZermeloFraenkel.axiom_of_equality _ hφ)

/-- The provability form: `ZF` plus the `Π_{N+1}` instances of the Vopenka scheme proves every
Vopenka sentence in `u`. -/
theorem provable_vopenkaSentence_of_pi_scheme (u : Finset SetTheorySentence)
    {σ : SetTheorySentence} (hu : σ ∈ u) (hσ : σ ∈ vopenkaTheory) : piVopenkaTheory u ⊢ σ := by
  apply SetTheory.provable_of_models.{0} (piVopenkaTheory u) σ
  intro M _ _ _
  let hZF : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun φ hφ ↦ Theory.models M (piVopenkaTheory u) (Or.inl hφ)⟩
  refine models_vopenkaSentence_of_pi_vopenka (V := M) (fun φ hφ ↦ ?_) hu hσ
  exact (eval_vopenkaSentence φ).mp
    (Theory.models M (piVopenkaTheory u) (Or.inr ⟨φ, hφ, rfl⟩))

end ZFVP
