import ZFVP.ModelTheory.InternalModelSchemas

/-! An internal ZF-model predicate with full internally coded axiom schemes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def setSentenceFormula (φ : SetTheorySentence) : SetTheorySemisentence 1 :=
  (Rew.bind (fun i : Fin 0 ↦ Fin.elim0 i) (fun _ : Option Empty ↦ .bvar 0)) ▹ relativize φ

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def SetSentenceTrue (φ : SetTheorySentence) (A : V) : Prop :=
  (relativize φ).Eval ![] (fun _ ↦ A)

instance setSentenceFormula_defined (φ : SetTheorySentence) :
    ℒₛₑₜ-predicate[V] (SetSentenceTrue φ) via setSentenceFormula φ := by
  refine ⟨fun v ↦ ?_⟩
  let ρ : Rew ℒₛₑₜ (Option Empty) 0 Empty 1 :=
    Rew.bind (fun i : Fin 0 ↦ Fin.elim0 i) (fun _ ↦ .bvar 0)
  change (ρ ▹ relativize φ).Evalb v ↔ (relativize φ).Eval ![] (fun _ ↦ v 0)
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val v Empty.elim ∘ ρ ∘ Semiterm.bvar) = ![] := by
    funext i; exact Fin.elim0 i
  have hf : (Semiterm.val v Empty.elim ∘ ρ ∘ Semiterm.fvar) = (fun _ ↦ v 0) := by
    funext i; rfl
  rw [hb, hf]

instance setSentenceTrue_definable (φ : SetTheorySentence) : ℒₛₑₜ-predicate[V] (SetSentenceTrue φ) :=
  (setSentenceFormula_defined φ).to_definable

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem setSentenceTrue_iff_models (φ : SetTheorySentence) (A : V) [Nonempty (SetDomain A)] :
    SetSentenceTrue φ A ↔ (SetDomain A)↓[ℒₛₑₜ] ⊧ φ := by
  have he := eval_relativize A φ ![] Empty.elim
  have hv : (fun x : Option Empty ↦ x.elim A (fun i ↦ (Empty.elim i : SetDomain A).val)) =
      (fun _ ↦ A) := by
    funext x
    cases x with
    | none => rfl
    | some e => exact Empty.elim e
  rw [hv] at he
  simpa only [SetSentenceTrue, models_iff, Semiformula.Realize, Matrix.empty_eq] using he

def InternalFixedZFAxioms (A : V) : Prop := IsNonempty A ∧
  SetSentenceTrue Axiom.empty A ∧ SetSentenceTrue Axiom.extentionality A ∧
  SetSentenceTrue Axiom.pairing A ∧ SetSentenceTrue Axiom.union A ∧
  SetSentenceTrue Axiom.power A ∧ SetSentenceTrue Axiom.infinity A ∧ SetSentenceTrue Axiom.foundation A

def IsInternalZFModel (A : V) : Prop :=
  InternalFixedZFAxioms A ∧ InternalSeparation A ∧ InternalReplacement A

instance internalFixedZFAxioms_definable : ℒₛₑₜ-predicate[V] InternalFixedZFAxioms := by
  unfold InternalFixedZFAxioms
  definability

instance isInternalZFModel_definable : ℒₛₑₜ-predicate[V] IsInternalZFModel := by
  unfold IsInternalZFModel
  definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem internalFixedZFAxioms_of_zermelo (A : V) [Nonempty (SetDomain A)]
    [(SetDomain A)↓[ℒₛₑₜ] ⊧* 𝗭] : InternalFixedZFAxioms A := by
  have hm {φ : SetTheorySentence} (hφ : φ ∈ 𝗭) : SetSentenceTrue φ A :=
    (setSentenceTrue_iff_models φ A).mpr (Theory.models (SetDomain A) 𝗭 hφ)
  obtain ⟨x⟩ := ‹Nonempty (SetDomain A)›
  exact ⟨⟨x.val, x.property⟩, hm Zermelo.axiom_of_empty_set, hm Zermelo.axiom_of_extentionality,
    hm Zermelo.axiom_of_pairing, hm Zermelo.axiom_of_union, hm Zermelo.axiom_of_power_set,
    hm Zermelo.axiom_of_infinity, hm Zermelo.axiom_of_foundation⟩

theorem rank_isInternalZFModel {θ : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hs : ∀ β ∈ θ, succ β ∈ θ) (hθ : NoLowRankCofinalMaps θ) :
    IsInternalZFModel (hierarchy θ) := by
  let := rankDomain_nonempty hω
  let := rankDomain_models_zermelo hω hs
  exact ⟨internalFixedZFAxioms_of_zermelo _, rank_internalSeparation hs, rank_internalReplacement hs hθ⟩

end ZFVP
