import ZFVP.ModelTheory.InternalNamedSyntax
import ZFVP.ModelTheory.InternalNamedDiagram

/-! Finite satisfiability over an actual source with fixed names. The definition
tests every internally finite fragment of the entire background requirements.
Decision density follows by combining two finite obstructions. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

def SourceNaming (M j f : V) : Prop :=
  f ∈ structureDomain M ^ (ω : V) ∧ ∀ x ∈ structureDomain M, f ‘ (j ‘ x) = x

instance sourceNaming_definable : ℒₛₑₜ-relation₃[V] SourceNaming := by
  unfold SourceNaming
  definability

def NamedSourceRealization (L M j S : V) : Prop :=
  ∃ f, SourceNaming M j f ∧ ∀ p ∈ S, NamedHolds L M f p

instance namedSourceRealization_definable : ℒₛₑₜ-relation₄[V] NamedSourceRealization := by
  unfold NamedSourceRealization
  definability

def FinitelySourceRealized (L M j B : V) : Prop :=
  B ⊆ namedFormulaSet L (ω : V) ∧
    ∀ S, IsInternallyFinite S → S ⊆ B → NamedSourceRealization L M j S

instance finitelySourceRealized_definable : ℒₛₑₜ-relation₄[V] FinitelySourceRealized := by
  unfold FinitelySourceRealized
  definability

theorem NamedSourceRealization.mono {L M j S T : V} (h : NamedSourceRealization L M j S) (hTS : T ⊆ S) :
    NamedSourceRealization L M j T := by
  obtain ⟨f, hf, hh⟩ := h
  exact ⟨f, hf, fun p hp ↦ hh p (hTS p hp)⟩

theorem FinitelySourceRealized.mono {L M j B C : V} (h : FinitelySourceRealized L M j B) (hCB : C ⊆ B) :
    FinitelySourceRealized L M j C :=
  ⟨fun p hp ↦ h.1 p (hCB p hp), fun S hS hSC ↦ h.2 S hS (fun p hp ↦ hCB p (hSC p hp))⟩

theorem finitelySourceRealized_of_realization {L M j B : V}
    (hB : B ⊆ namedFormulaSet L (ω : V)) (hr : NamedSourceRealization L M j B) :
    FinitelySourceRealized L M j B := ⟨hB, fun _ _ hSB ↦ hr.mono hSB⟩

theorem namedElementaryDiagram_valid {L M j : V} (hL : IsLanguageCode L)
    (hj : j ∈ (ω : V) ^ structureDomain M) :
    namedElementaryDiagram L M j ⊆ namedFormulaSet L (ω : V) := by
  intro p hp
  obtain ⟨n, _, φ, hφ, b, hb, rfl, _⟩ := namedElementaryDiagram_cases hL hp
  exact (pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, compose_function hb hj⟩

theorem namedElementaryDiagram_finitelySourceRealized {L M j : V}
    (hM : IsStructureCode L M) (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j) :
    FinitelySourceRealized L M j (namedElementaryDiagram L M j) := by
  obtain ⟨a, ha⟩ := hM.domain_nonempty
  obtain ⟨hr, hs⟩ := namedElementaryDiagram_source_realization hM hj hji ha
  apply finitelySourceRealized_of_realization (namedElementaryDiagram_valid hM.language hj)
  exact ⟨injectionRetraction j (ω : V) a,
    ⟨hr, fun x hx ↦ injectionRetraction_value hj hji hx⟩, hs⟩

theorem finitelySourceRealized_insert_iff {L M j B p : V}
    (hB : B ⊆ namedFormulaSet L (ω : V)) (hp : p ∈ namedFormulaSet L (ω : V)) :
    FinitelySourceRealized L M j (B ∪ {p}) ↔
      ∀ S, IsInternallyFinite S → S ⊆ B →
        ∃ f, SourceNaming M j f ∧ (∀ q ∈ S, NamedHolds L M f q) ∧ NamedHolds L M f p := by
  constructor
  · intro h S hS hSB
    have hSp : IsInternallyFinite (S ∪ ({p} : V)) :=
      internallyFinite_union hS (by simpa using internallyFinite_insert internallyFinite_empty p)
    obtain ⟨f, hf, hs⟩ := h.2 (S ∪ {p}) hSp (by
      intro q hq
      rcases mem_union_iff.mp hq with hq | hq
      · exact mem_union_iff.mpr (Or.inl (hSB q hq))
      · exact mem_union_iff.mpr (Or.inr hq))
    exact ⟨f, hf, fun q hq ↦ hs q (mem_union_iff.mpr (Or.inl hq)), hs p (by simp)⟩
  · intro h
    refine ⟨?_, fun T hT hTB ↦ ?_⟩
    · intro q hq
      rcases mem_union_iff.mp hq with hq | hq
      · exact hB q hq
      · simpa only [mem_singleton_iff.mp hq] using hp
    · let S : V := {q ∈ T ; q ∈ B}
      have hST : S ⊆ T := fun q hq ↦ (mem_sep_iff.mp hq).1
      have hSB : S ⊆ B := fun q hq ↦ (mem_sep_iff.mp hq).2
      obtain ⟨f, hf, hs, hfp⟩ := h S (internallyFinite_of_cardLE hT (cardLE_of_subset hST)) hSB
      refine ⟨f, hf, fun q hq ↦ ?_⟩
      rcases mem_union_iff.mp (hTB q hq) with hqB | hqp
      · exact hs q (mem_sep_iff.mpr ⟨hq, hqB⟩)
      · simpa only [mem_singleton_iff.mp hqp] using hfp

theorem FinitelySourceRealized.decide {L M j B p : V} (hL : IsLanguageCode L)
    (hB : FinitelySourceRealized L M j B) (hp : p ∈ namedFormulaSet L (ω : V)) :
    FinitelySourceRealized L M j (B ∪ {p}) ∨
      FinitelySourceRealized L M j (B ∪ {namedNegation L p}) := by
  classical
  by_cases hpos : FinitelySourceRealized L M j (B ∪ {p})
  · exact Or.inl hpos
  · apply Or.inr
    have hex : ∃ S, IsInternallyFinite S ∧ S ⊆ B ∧
        ¬∃ f, SourceNaming M j f ∧ (∀ q ∈ S, NamedHolds L M f q) ∧ NamedHolds L M f p := by
      by_contra hh
      apply hpos
      apply (finitelySourceRealized_insert_iff hB.1 hp).mpr
      intro S hS hSB
      by_contra hr
      exact hh ⟨S, hS, hSB, hr⟩
    obtain ⟨S, hS, hSB, hno⟩ := hex
    apply (finitelySourceRealized_insert_iff hB.1 (namedNegation_mem hL hp)).mpr
    intro T hT hTB
    obtain ⟨f, hf, hh⟩ := hB.2 (S ∪ T) (internallyFinite_union hS hT) (by
      intro q hq
      rcases mem_union_iff.mp hq with hq | hq
      · exact hSB q hq
      · exact hTB q hq)
    have hs : ∀ q ∈ S, NamedHolds L M f q := fun q hq ↦ hh q (mem_union_iff.mpr (Or.inl hq))
    have hnp : ¬NamedHolds L M f p := fun hfp ↦ hno ⟨f, hf, hs, hfp⟩
    exact ⟨f, hf, fun q hq ↦ hh q (mem_union_iff.mpr (Or.inr hq)),
      (namedHolds_negation hL hf.1 hp).mpr hnp⟩

end ZFVP
