import ZFVP.ModelTheory.GeneratedZFVPModels

/-! The generated recursive presentation and the external ZF+VP theory prove the same sentences. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {M : Type*} [SetStructure M]

theorem eval_prefix_one_definable {k : ℕ} (φ : SetTheorySemisentence (k + 1)) (b : Fin k → M) :
    ℒₛₑₜ-predicate (fun x : M ↦ φ.Evalb (prefixVector ![x] b)) := by
  have hφ : Language.Definable ℒₛₑₜ (fun v : Fin (k + 1) → M ↦ φ.Evalb v) :=
    (show Defined (fun v : Fin (k + 1) → M ↦ φ.Evalb v) φ from ⟨fun _ ↦ Iff.rfl⟩).to_definable
  apply Language.Definable.substitution hφ (f := fun i v ↦ prefixVector ![v 0] b i)
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change Language.DefinableFunction ℒₛₑₜ (fun v : Fin 1 → M ↦ v 0)
    definability
  · change Language.DefinableFunction ℒₛₑₜ (fun _ : Fin 1 → M ↦ b j)
    definability

theorem eval_prefix_two_definable {k : ℕ} (φ : SetTheorySemisentence (k + 2)) (b : Fin k → M) :
    ℒₛₑₜ-relation (fun x y : M ↦ φ.Evalb (prefixVector ![x, y] b)) := by
  have hφ : Language.Definable ℒₛₑₜ (fun v : Fin (k + 2) → M ↦ φ.Evalb v) :=
    (show Defined (fun v : Fin (k + 2) → M ↦ φ.Evalb v) φ from ⟨fun _ ↦ Iff.rfl⟩).to_definable
  apply Language.Definable.substitution hφ (f := fun i v ↦ prefixVector ![v 0, v 1] b i)
  intro i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun l ↦ ?_) j) i
  · change Language.DefinableFunction ℒₛₑₜ (fun v : Fin 2 → M ↦ v 0)
    definability
  · change Language.DefinableFunction ℒₛₑₜ (fun v : Fin 2 → M ↦ v 1)
    definability
  · change Language.DefinableFunction ℒₛₑₜ (fun _ : Fin 2 → M ↦ b l)
    definability

variable [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem zf_models_generated_separation (k : ℕ) (φ : SetTheorySemisentence (k + 1)) :
    M↓[ℒₛₑₜ] ⊧ ∀¹* separationTemplate.instantiateTail k φ := by
  have h : ∀ b : Fin k → M, (separationTemplate.instantiateTail k φ).Evalb b := by
    intro b
    apply (MembershipTemplate.eval_instantiateTail φ separationTemplate (![] : Fin 0 → M) b).mpr
    apply (eval_separationTemplate _).mpr
    intro a
    exact separation_exists a _ (eval_prefix_one_definable φ b)
  simpa [models_iff, Semiformula.Evalb] using h

theorem zf_models_generated_replacement (k : ℕ) (φ : SetTheorySemisentence (k + 2)) :
    M↓[ℒₛₑₜ] ⊧ ∀¹* replacementTemplate.instantiateTail k φ := by
  have h : ∀ b : Fin k → M, (replacementTemplate.instantiateTail k φ).Evalb b := by
    intro b
    apply (MembershipTemplate.eval_instantiateTail φ replacementTemplate (![] : Fin 0 → M) b).mpr
    apply (eval_replacementTemplate _).mpr
    intro a ha
    exact replacement_rel_exists_of_mem_existsUnique a _ ha (eval_prefix_two_definable φ b)
  simpa [models_iff, Semiformula.Evalb] using h

theorem vopenkaSentence_models_template (φ : SetTheorySemisentence 2)
    (h : M↓[ℒₛₑₜ] ⊧ vopenkaSentence φ) : M↓[ℒₛₑₜ] ⊧ vopenkaTemplate.instantiate φ := by
  change (vopenkaTemplate.instantiate φ).Evalb (![] : Fin 0 → M)
  apply (MembershipTemplate.eval_instantiate φ vopenkaTemplate ![]).mpr
  apply (eval_vopenkaTemplateWith isStructureCodeFormula codedElementaryEmbeddingFormula _).mpr
  simpa [models_iff, vopenkaSentence, Semiformula.Evalb] using h

theorem externalZFVP_models_generated (M : Type*) [SetStructure M] [Nonempty M]
    [M↓[ℒₛₑₜ] ⊧* zfVPTheory] : M↓[ℒₛₑₜ] ⊧* generatedZFVPTheory := by
  let hz : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun φ hφ ↦ Theory.models M zfVPTheory (Or.inl hφ)⟩
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | fixed h =>
    simp only [fixedZFTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_empty_set
    · exact Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_extentionality
    · exact Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_pairing
    · exact Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_union
    · exact Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_power_set
    · exact Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_infinity
    · exact Theory.models M 𝗭𝗙 ZermeloFraenkel.axiom_of_foundation
    · exact eval_equalityBasisSentence
  | separation k φ => exact zf_models_generated_separation k φ
  | replacement k φ => exact zf_models_generated_replacement k φ
  | vopenka φ => exact vopenkaSentence_models_template φ (Theory.models M zfVPTheory (Or.inr ⟨φ, rfl⟩))

instance generatedZFVPTheory_weaker_external : generatedZFVPTheory ⪯ zfVPTheory := by
  let heq : 𝗘𝗤 ℒₛₑₜ ⪯ zfVPTheory := Entailment.WeakerThan.ofSubset
    (fun φ hφ ↦ Or.inl (ZermeloFraenkel.axiom_of_equality φ hφ))
  apply Entailment.WeakerThan.ofAxm!
  intro φ hφ
  apply SetTheory.provable_of_models.{0} zfVPTheory φ
  intro N _ _ _
  let := externalZFVP_models_generated N
  exact Theory.models N generatedZFVPTheory hφ

theorem generatedZFVPTheory_provable_iff (φ : SetTheorySentence) :
    generatedZFVPTheory ⊢ φ ↔ zfVPTheory ⊢ φ :=
  ⟨Entailment.WeakerThan.pbl, Entailment.WeakerThan.pbl⟩

end ZFVP
