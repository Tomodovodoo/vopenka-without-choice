import ZFVP.ModelTheory.WoodinCanonicalTailNameAction
import ZFVP.ModelTheory.WoodinCollapseDisplacementNameUniform
import ZFVP.ModelTheory.WoodinNormalizationInverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance tailFunctionValueName_uniform_definable : ℒₛₑₜ-function₄[V] tailFunctionValueName :=
  tailApplicationGraphFormula_defined.to_definable

instance normalizedTailFunctionValueName_uniform_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (normalizedTailFunctionValueName (V := V)) := by
  unfold normalizedTailFunctionValueName
  apply Language.DefinableFunction₄.comp
  · definability
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability

instance normalizedTailTwoStepValue_uniform_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (normalizedTailTwoStepValue (V := V)) := by
  unfold normalizedTailTwoStepValue
  apply Language.DefinableFunction₂.comp
  · definability
  · apply Language.DefinableFunction₅.comp <;> definability

instance normalizedTailTwoStepMap_uniform_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 6 → V ↦
      normalizedTailTwoStepMap (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 7 → V ↦ ∀ w, w ∈ v 0 ↔
      ∃ z ∈ normalizedNameTwoStep (v 1) (v 2) (v 3) (v 4) (v 5),
        w = ⟨z, normalizedTailTwoStepValue (v 1) (v 2) (v 3) (v 6) z⟩ₖ) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional
    · definability
    · apply Language.Definable.exs
      apply Language.Definable.and
      · apply Language.DefinableRel.comp (P := Membership.mem)
        · apply Language.DefinableFunction₅.comp <;> definability
        · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₂.comp (F := kpair)
          · definability
          · apply Language.DefinableFunction₅.comp (F := normalizedTailTwoStepValue) <;> definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = normalizedTailTwoStepMap (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) ↔ _
  rw [mem_ext_iff]
  simp only [normalizedTailTwoStepMap, mem_definableGraph_iff]

theorem normalizedTailTwoStepMap_comp {n : ℕ} {a b c d e f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦ normalizedTailTwoStepMap
      (a v) (b v) (c v) (d v) (e v) (f v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f])
    normalizedTailTwoStepMap_uniform_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf])

theorem sparseTailNameMap_comp_definable {n : ℕ}
    {a P R top δ Q f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hP : Language.DefinableFunction ℒₛₑₜ P)
    (hR : Language.DefinableFunction ℒₛₑₜ R) (ht : Language.DefinableFunction ℒₛₑₜ top)
    (hδ : Language.DefinableFunction ℒₛₑₜ δ) (hQ : Language.DefinableFunction ℒₛₑₜ Q)
    (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦
      sparseTailNameMap (a v) (P v) (R v) (top v) (δ v) (Q v) (f v)) := by
  have hW : Language.DefinableFunction ℒₛₑₜ (fun v ↦
      normalizedNamePool (P v) (R v) (top v) (δ v) (Q v)) := by
    apply Language.DefinableFunction₅.comp <;> assumption
  unfold sparseTailNameMap
  dsimp only
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₃.comp <;> assumption
  · apply Language.DefinableFunction₂.comp
    · exact normalizedTailTwoStepMap_comp hP hR ht hδ hQ hf
    · apply Language.DefinableFunction₃.comp <;> assumption

theorem woodinCollapseDisplacementName_comp {n : ℕ} {a b c d e f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦ woodinCollapseDisplacementName
      (a v) (b v) (c v) (d v) (e v) (f v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f])
    woodinCollapseDisplacementName_uniform_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf])

theorem sparseCanonicalPrefixDisplacement_comp {n : ℕ}
    {a P R top κ δ p q : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hP : Language.DefinableFunction ℒₛₑₜ P)
    (hR : Language.DefinableFunction ℒₛₑₜ R) (ht : Language.DefinableFunction ℒₛₑₜ top)
    (hκ : Language.DefinableFunction ℒₛₑₜ κ) (hδ : Language.DefinableFunction ℒₛₑₜ δ)
    (hp : Language.DefinableFunction ℒₛₑₜ p) (hq : Language.DefinableFunction ℒₛₑₜ q) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦
      sparseCanonicalPrefixDisplacement (a v) (P v) (R v) (top v) (κ v) (δ v) (p v) (q v)) := by
  unfold sparseCanonicalPrefixDisplacement
  apply sparseTailNameMap_comp_definable ha hP hR ht hδ
  · apply Language.DefinableFunction₅.comp <;> assumption
  · apply woodinCollapseDisplacementName_comp hP hR
    · apply Language.DefinableFunction₂.comp <;> assumption
    · apply Language.DefinableFunction₂.comp <;> assumption
    · exact hp
    · exact hq

theorem sparseCanonicalHartogsDisplacement_comp {n : ℕ}
    {a P R top γ δ p q : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hP : Language.DefinableFunction ℒₛₑₜ P)
    (hR : Language.DefinableFunction ℒₛₑₜ R) (ht : Language.DefinableFunction ℒₛₑₜ top)
    (hγ : Language.DefinableFunction ℒₛₑₜ γ) (hδ : Language.DefinableFunction ℒₛₑₜ δ)
    (hp : Language.DefinableFunction ℒₛₑₜ p) (hq : Language.DefinableFunction ℒₛₑₜ q) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦
      sparseCanonicalHartogsDisplacement (a v) (P v) (R v) (top v) (γ v) (δ v) (p v) (q v)) := by
  unfold sparseCanonicalHartogsDisplacement
  apply sparseTailNameMap_comp_definable ha hP hR ht hδ
  · apply Language.DefinableFunction₅.comp <;> assumption
  · apply woodinCollapseDisplacementName_comp hP hR
    · apply Language.DefinableFunction₃.comp hP hR
      apply Language.DefinableFunction₂.comp <;> assumption
    · apply Language.DefinableFunction₂.comp <;> assumption
    · exact hp
    · exact hq

end ZFVP

