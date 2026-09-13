import ZFVP.ModelTheory.EqualityBasisCompleteness
import ZFVP.ModelTheory.CodedZFVPExternal
import ZFVP.Syntax.CloseTailParameters

/-! Models of the generated sentence theory satisfy the full external ZF+VP theory. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {M : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* generatedZFVPTheory]

theorem generatedZFVP_models_separation (φ : SetTheorySemiproposition 1) :
    M↓[ℒₛₑₜ] ⊧ Axiom.separationSchema φ := by
  have h := Theory.models M generatedZFVPTheory (GeneratedZFVPAxiom.separation φ.fvSup (closeTailParameters φ))
  have hh : ∀ b : Fin φ.fvSup → M,
      (separationTemplate.instantiateTail φ.fvSup (closeTailParameters φ)).Evalb b := by
    simpa [models_iff, Semiformula.Evalb] using h
  simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
  intro e a
  have ht := (MembershipTemplate.eval_instantiateTail (closeTailParameters φ) separationTemplate
    (![] : Fin 0 → M) (fun i : Fin φ.fvSup ↦ e i.val)).mp (hh _)
  have hs := (eval_separationTemplate _).mp ht
  obtain ⟨c, hc⟩ := hs a
  refine ⟨c, fun x ↦ ?_⟩
  exact (hc x).trans (and_congr Iff.rfl (eval_closeTailParameters φ ![x] e))

theorem generatedZFVP_models_replacement (φ : SetTheorySemiproposition 2) :
    M↓[ℒₛₑₜ] ⊧ Axiom.replacementSchema φ := by
  have h := Theory.models M generatedZFVPTheory (GeneratedZFVPAxiom.replacement φ.fvSup (closeTailParameters φ))
  have hh : ∀ b : Fin φ.fvSup → M,
      (replacementTemplate.instantiateTail φ.fvSup (closeTailParameters φ)).Evalb b := by
    simpa [models_iff, Semiformula.Evalb] using h
  simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl]
  intro e hf a
  have ht := (MembershipTemplate.eval_instantiateTail (closeTailParameters φ) replacementTemplate
    (![] : Fin 0 → M) (fun i : Fin φ.fvSup ↦ e i.val)).mp (hh _)
  have hs := (eval_replacementTemplate _).mp ht
  have he (x y : M) := eval_closeTailParameters φ ![x, y] e
  have hhf : ∀ x : M, x ∈ a → ∃! y : M,
      (closeTailParameters φ).Evalb (prefixVector ![x, y] (fun i : Fin φ.fvSup ↦ e i.val)) := by
    intro x _
    obtain ⟨y, hy, hu⟩ := hf x
    exact ⟨y, (he x y).mpr hy, fun z hz ↦ hu z ((he x z).mp hz)⟩
  obtain ⟨c, hc⟩ := hs a hhf
  refine ⟨c, fun y ↦ ?_⟩
  exact (hc y).trans (exists_congr (fun x ↦ and_congr Iff.rfl (he x y)))

theorem generatedZFVP_models_zf : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  have hf (φ : SetTheorySentence) (hφ : φ ∈ fixedZFTheory) : M↓[ℒₛₑₜ] ⊧ φ :=
    Theory.models M generatedZFVPTheory (GeneratedZFVPAxiom.fixed hφ)
  refine ⟨?_⟩
  intro φ hφ
  cases hφ with
  | axiom_of_equality φ hφ => exact Theory.models M (𝗘𝗤 ℒₛₑₜ) hφ
  | axiom_of_empty_set => exact hf _ (by simp [fixedZFTheory])
  | axiom_of_extentionality => exact hf _ (by simp [fixedZFTheory])
  | axiom_of_pairing => exact hf _ (by simp [fixedZFTheory])
  | axiom_of_union => exact hf _ (by simp [fixedZFTheory])
  | axiom_of_power_set => exact hf _ (by simp [fixedZFTheory])
  | axiom_of_infinity => exact hf _ (by simp [fixedZFTheory])
  | axiom_of_foundation => exact hf _ (by simp [fixedZFTheory])
  | axiom_of_separation φ => exact generatedZFVP_models_separation φ
  | axiom_of_replacement φ => exact generatedZFVP_models_replacement φ

theorem generatedZFVP_models_vopenka (φ : SetTheorySemisentence 2) : M↓[ℒₛₑₜ] ⊧ vopenkaSentence φ := by
  have h := Theory.models M generatedZFVPTheory (GeneratedZFVPAxiom.vopenka φ)
  change (vopenkaTemplate.instantiate φ).Evalb (![] : Fin 0 → M) at h
  have ht := (MembershipTemplate.eval_instantiate φ vopenkaTemplate ![]).mp h
  have hs := (eval_vopenkaTemplateWith isStructureCodeFormula codedElementaryEmbeddingFormula
    (fun w : Fin 2 → M ↦ φ.Evalb w)).mp ht
  simpa [models_iff, vopenkaSentence, Semiformula.Evalb] using hs

theorem generatedZFVP_models_external : M↓[ℒₛₑₜ] ⊧* zfVPTheory := by
  let := generatedZFVP_models_zf (M := M)
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with hφ | ⟨ψ, rfl⟩
  · exact Theory.models M 𝗭𝗙 hφ
  · exact generatedZFVP_models_vopenka ψ

instance zfVPTheory_weaker_generated : zfVPTheory ⪯ generatedZFVPTheory := by
  apply Entailment.WeakerThan.ofAxm!
  intro φ hφ
  apply SetTheory.provable_of_models.{0} generatedZFVPTheory φ
  intro N _ _ _
  let := generatedZFVP_models_external (M := N)
  exact Theory.models N zfVPTheory hφ

end ZFVP
