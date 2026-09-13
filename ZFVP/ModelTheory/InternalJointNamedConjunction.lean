import ZFVP.ModelTheory.InternalNamedConjunction
import ZFVP.ModelTheory.InternalJointSourceNaming

/-! Finite assignments characterize realization of a finite named theory while
respecting source names and a disjoint family of prescribed names. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def nameContextOverlayValue (n b f i : V) : V := by
  classical
  exact if i ∈ n then b ‘ i else f ‘ i

instance nameContextOverlayValue_definable : ℒₛₑₜ-function₄[V] nameContextOverlayValue := by
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 5 → V ↦
      (v 4 ∈ v 1 ∧ v 0 = (v 2) ‘ (v 4)) ∨
        (v 4 ∉ v 1 ∧ v 0 = (v 3) ‘ (v 4))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = nameContextOverlayValue (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold nameContextOverlayValue
  split <;> simp_all

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def nameContextOverlay (n b f : V) : V :=
  definableGraph (ω : V) (nameContextOverlayValue n b f) (by definability)

instance nameContextOverlay_definable : ℒₛₑₜ-function₃[V] nameContextOverlay := by
  have h : ℒₛₑₜ-relation₄[V] (fun g n b f ↦ ∀ p, p ∈ g ↔
      ∃ i ∈ (ω : V), p = ⟨i, nameContextOverlayValue n b f i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [nameContextOverlay, mem_definableGraph_iff]
  rfl

theorem nameContextOverlay_value (n b f : V) {i : V} (hi : i ∈ (ω : V)) :
    (nameContextOverlay n b f) ‘ i = nameContextOverlayValue n b f i :=
  value_definableGraph _ _ _ hi

theorem nameContextOverlay_inside (b f : V) {n i : V}
    (hi : i ∈ (ω : V)) (hin : i ∈ n) : (nameContextOverlay n b f) ‘ i = b ‘ i := by
  rw [nameContextOverlay_value _ _ _ hi]
  simp only [nameContextOverlayValue, hin, ite_true]

theorem nameContextOverlay_outside (b f : V) {n i : V}
    (hi : i ∈ (ω : V)) (hin : i ∉ n) : (nameContextOverlay n b f) ‘ i = f ‘ i := by
  rw [nameContextOverlay_value _ _ _ hi]
  simp only [nameContextOverlayValue, hin, ite_false]

theorem nameContextOverlay_mem {D n b f : V} (hb : b ∈ D ^ n) (hf : f ∈ D ^ (ω : V)) :
    nameContextOverlay n b f ∈ D ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  unfold nameContextOverlayValue
  split
  · exact function_value_mem hb ‹i ∈ n›
  · exact function_value_mem hf hi

theorem nameContextOverlay_restrict {D n b f : V} (hn : n ⊆ (ω : V))
    (hb : b ∈ D ^ n) (hf : f ∈ D ^ (ω : V)) : (nameContextOverlay n b f) ↾ n = b := by
  have hg := nameContextOverlay_mem hb hf
  have : IsFunction (nameContextOverlay n b f) := IsFunction.of_mem hg
  apply function_eq_of_values (function_restrict_mem hg hn) hb
  intro i hi
  rw [value_restrict (by rw [domain_eq_of_mem_function hg]; exact hn i hi) hi]
  exact nameContextOverlay_inside b f (hn i hi) hi

theorem exists_jointSourceAssignment_extending {D I j k c n b : V} (hD : IsNonempty D)
    (hj : j ∈ (ω : V) ^ D) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ i ∈ range j, i ∉ range k) (hc : c ∈ D ^ I)
    (hn : n ⊆ (ω : V)) (hb : b ∈ D ^ n)
    (hbj : ∀ x ∈ D, j ‘ x ∈ n → b ‘ (j ‘ x) = x)
    (hbk : ∀ i ∈ I, k ‘ i ∈ n → b ‘ (k ‘ i) = c ‘ i) :
    ∃ f ∈ D ^ (ω : V), (∀ x ∈ D, f ‘ (j ‘ x) = x) ∧
      (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧ f ↾ n = b := by
  classical
  obtain ⟨f, hf, hfj, hfk⟩ := exists_jointSourceAssignment hD hj hji hk hki hdis hc
  refine ⟨nameContextOverlay n b f, nameContextOverlay_mem hb hf, ?_, ?_,
    nameContextOverlay_restrict hn hb hf⟩
  · intro x hx
    by_cases hxn : j ‘ x ∈ n
    · rw [nameContextOverlay_inside b f (function_value_mem hj hx) hxn]
      exact hbj x hx hxn
    · rw [nameContextOverlay_outside b f (function_value_mem hj hx) hxn]
      exact hfj x hx
  · intro i hi
    by_cases hin : k ‘ i ∈ n
    · rw [nameContextOverlay_inside b f (function_value_mem hk hi) hin]
      exact hbk i hi hin
    · rw [nameContextOverlay_outside b f (function_value_mem hk hi) hin]
      exact hfk i hi

theorem exists_internal_jointNamedConjunction {M I j k c A : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ I) (hki : Injective k)
    (hdis : ∀ i ∈ range j, i ∉ range k) (hc : c ∈ structureDomain M ^ I)
    (hA : IsInternallyFinite A) (hsub : A ⊆ namedFormulaSet membershipLanguageCode (ω : V)) :
    ∃ n ∈ (ω : V), namedTheorySupport A ⊆ n ∧
      ∃ χ ∈ formulaSet membershipLanguageCode ∅ n,
        ((∃ f, SourceNaming M j f ∧ (∀ i ∈ I, f ‘ (k ‘ i) = c ‘ i) ∧
          ∀ p ∈ A, NamedHolds membershipLanguageCode M f p) ↔
        ∃ b ∈ structureDomain M ^ n, Satisfies membershipLanguageCode ∅ M ∅ n χ b ∧
          (∀ x ∈ structureDomain M, j ‘ x ∈ n → b ‘ (j ‘ x) = x) ∧
          ∀ i ∈ I, k ‘ i ∈ n → b ‘ (k ‘ i) = c ‘ i) := by
  obtain ⟨n, hn, hs, χ, hχ, heq⟩ := exists_internal_namedConjunction hA hsub
  have hnω : n ⊆ (ω : V) := IsTransitive.ω.transitive n hn
  refine ⟨n, hn, hs, χ, hχ, ?_⟩
  constructor
  · rintro ⟨f, hf, hfk, hAf⟩
    have : IsFunction f := IsFunction.of_mem hf.1
    refine ⟨f ↾ n, function_restrict_mem hf.1 hnω, (heq M hM f hf.1).mp hAf, ?_, ?_⟩
    · intro x hx hxn
      rw [value_restrict (by rw [domain_eq_of_mem_function hf.1]; exact function_value_mem hj hx) hxn]
      exact hf.2 x hx
    · intro i hi hin
      rw [value_restrict (by rw [domain_eq_of_mem_function hf.1]; exact function_value_mem hk hi) hin]
      exact hfk i hi
  · rintro ⟨b, hb, hbχ, hbj, hbk⟩
    obtain ⟨f, hf, hfj, hfk, hfb⟩ := exists_jointSourceAssignment_extending hM.domain_nonempty
      hj hji hk hki hdis hc hnω hb hbj hbk
    refine ⟨f, ⟨hf, hfj⟩, hfk, (heq M hM f hf).mpr ?_⟩
    rw [hfb]
    exact hbχ

end ZFVP
