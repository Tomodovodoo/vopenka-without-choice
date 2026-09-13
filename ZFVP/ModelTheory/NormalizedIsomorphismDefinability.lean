import ZFVP.ModelTheory.NormalizedTwoStepIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance normalizedTwoStepIsoValue_uniform_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (normalizedTwoStepIsoValue (V := V)) := by
  unfold normalizedTwoStepIsoValue
  apply Language.DefinableFunction₂.comp
  · definability
  · apply Language.DefinableFunction₅.comp <;> definability

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₅.comp

instance normalizedTwoStepIsoMap_uniform_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 9 → V ↦
      normalizedTwoStepIsoMap (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 10 → V ↦ ∀ w, w ∈ v 0 ↔
      ∃ z ∈ normalizedNameTwoStep (v 1) (v 2) (v 3) (v 4) (v 5),
        w = ⟨z, normalizedTwoStepIsoValue (v 6) (v 7) (v 8) (v 9) z⟩ₖ) := by
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
          · apply Language.DefinableFunction₅.comp (F := normalizedTwoStepIsoValue) <;> definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = normalizedTwoStepIsoMap (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) ↔ _
  rw [mem_ext_iff]
  simp only [normalizedTwoStepIsoMap, mem_definableGraph_iff]

theorem normalizedTwoStepIsoMap_comp {n : ℕ} {a b c d e f g h i : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f)
    (hg : Language.DefinableFunction ℒₛₑₜ g) (hh : Language.DefinableFunction ℒₛₑₜ h)
    (hi : Language.DefinableFunction ℒₛₑₜ i) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦ normalizedTwoStepIsoMap
      (a v) (b v) (c v) (d v) (e v) (f v) (g v) (h v) (i v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f, g, h, i])
    normalizedTwoStepIsoMap_uniform_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf, hg, hh, hi])

end ZFVP
