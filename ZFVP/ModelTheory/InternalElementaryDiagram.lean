import ZFVP.ModelTheory.CodedElementaryEmbedding
import ZFVP.ModelTheory.SchmerlInternalCodedSyntaxCountable
import ZFVP.ModelTheory.SchmerlInternalCodedHullClosure
import ZFVP.Syntax.NegationSemantics

/-! The elementary diagram as an actual set of formula/parameter entries.
Realizing its positive entries already gives full coded elementarity, since
the diagram contains the negation of every false formula. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def codedTupleDiagram (L M n b : V) : V :=
  sep (formulaSet L ∅ n) (fun φ ↦ Satisfies L ∅ M ∅ n φ b) (by unfold Satisfies; definability)

@[simp] theorem mem_codedTupleDiagram (L M n b φ : V) :
    φ ∈ codedTupleDiagram L M n b ↔ φ ∈ formulaSet L ∅ n ∧ Satisfies L ∅ M ∅ n φ b := mem_sep_iff

instance codedTupleDiagram_definable : ℒₛₑₜ-function₄[V] codedTupleDiagram := by
  let : ℒₛₑₜ-function₄[V] satisfactionGraph := satisfactionGraphFormula_defined.to_definable
  have h : Language.Definable ℒₛₑₜ (fun v : Fin 5 → V ↦
      ∀ φ, φ ∈ v 0 ↔ φ ∈ formulaSet (v 1) ∅ (v 3) ∧ Satisfies (v 1) ∅ (v 2) ∅ (v 3) φ (v 4)) := by
    unfold Satisfies
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = codedTupleDiagram (v 1) (v 2) (v 3) (v 4) ↔
    (∀ φ, φ ∈ v 0 ↔ φ ∈ formulaSet (v 1) ∅ (v 3) ∧ Satisfies (v 1) ∅ (v 2) ∅ (v 3) φ (v 4))
  rw [mem_ext_iff]
  simp only [mem_codedTupleDiagram]

noncomputable def codedElementaryDiagram (L M : V) : V :=
  {p ∈ formulaFamily L ∅ ×ˢ finiteSequences (structureDomain M) ;
    kpair.π₂ p ∈ structureDomain M ^ (kpair.π₁ (kpair.π₁ p)) ∧
      kpair.π₂ (kpair.π₁ p) ∈ codedTupleDiagram L M (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ p)}

theorem mem_codedElementaryDiagram_iff (L M p : V) : p ∈ codedElementaryDiagram L M ↔
    p ∈ formulaFamily L ∅ ×ˢ finiteSequences (structureDomain M) ∧
      kpair.π₂ p ∈ structureDomain M ^ (kpair.π₁ (kpair.π₁ p)) ∧
        kpair.π₂ (kpair.π₁ p) ∈ codedTupleDiagram L M (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ p) := mem_sep_iff

instance codedElementaryDiagram_definable : ℒₛₑₜ-function₂[V] codedElementaryDiagram := by
  have h : ℒₛₑₜ-relation₃[V] (fun D L M ↦ ∀ p, p ∈ D ↔
      p ∈ formulaFamily L ∅ ×ˢ finiteSequences (structureDomain M) ∧
        kpair.π₂ p ∈ structureDomain M ^ (kpair.π₁ (kpair.π₁ p)) ∧
          kpair.π₂ (kpair.π₁ p) ∈ codedTupleDiagram L M (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedElementaryDiagram_iff]
  rfl

theorem pair_mem_codedElementaryDiagram {L M n φ b : V} (hL : IsLanguageCode L) :
    ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ codedElementaryDiagram L M ↔
      φ ∈ formulaSet L ∅ n ∧ b ∈ structureDomain M ^ n ∧ Satisfies L ∅ M ∅ n φ b := by
  rw [mem_codedElementaryDiagram_iff]
  simp only [kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, mem_codedTupleDiagram]
  constructor
  · rintro ⟨_, hb, hφ, hs⟩
    exact ⟨hφ, hb, hs⟩
  · rintro ⟨hφ, hb, hs⟩
    exact ⟨⟨(mem_formulaSet_iff _ _ _ _).mp hφ,
      (mem_finiteSequences_iff _ _).mpr ⟨n, formulaSet_context hL hφ, hb⟩⟩, hb, hφ, hs⟩

theorem codedElementaryDiagram_cases {L M p : V} (hL : IsLanguageCode L)
    (hp : p ∈ codedElementaryDiagram L M) :
    ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet L ∅ n, ∃ b ∈ structureDomain M ^ n,
      p = ⟨⟨n, φ⟩ₖ, b⟩ₖ ∧ Satisfies L ∅ M ∅ n φ b := by
  have hp' := (mem_codedElementaryDiagram_iff L M p).mp hp
  obtain ⟨r, hr, b, _, rfl⟩ := mem_prod_iff.mp hp'.1
  obtain ⟨n, hn, φ, rfl⟩ := formulaFamily_context hL ∅ hr
  obtain ⟨hφ, hb, hs⟩ := (pair_mem_codedElementaryDiagram hL).mp hp
  exact ⟨n, hn, φ, hφ, b, hb, rfl, hs⟩

theorem codedElementaryDiagram_countable (hAC : InternalChoice V) {L M : V}
    (hL : IsLanguageCode L) (hF : IsInternallyCountable (functionSymbols L))
    (hR : IsInternallyCountable (relationSymbols L)) (hM : IsInternallyCountable (structureDomain M)) :
    IsInternallyCountable (codedElementaryDiagram L M) := by
  apply internallyCountable_subset
    ((prod_cardLE_prod (Schmerl.formulaFamily_countable hAC hL hF hR internallyCountable_empty)
      (Schmerl.internallyCountable_finiteSequences hAC hM)).trans omega_prod_cardLE_omega)
  exact fun p hp ↦ ((mem_codedElementaryDiagram_iff L M p).mp hp).1

def RealizesCodedElementaryDiagram (L M N f : V) : Prop :=
  f ∈ structureDomain N ^ structureDomain M ∧
    ∀ p ∈ codedElementaryDiagram L M,
      Satisfies L ∅ N ∅ (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) (compose (kpair.π₂ p) f)

instance realizesCodedElementaryDiagram_definable : ℒₛₑₜ-relation₄[V] RealizesCodedElementaryDiagram := by
  let : ℒₛₑₜ-function₄[V] satisfactionGraph := satisfactionGraphFormula_defined.to_definable
  unfold RealizesCodedElementaryDiagram Satisfies
  definability

theorem realizesCodedElementaryDiagram_iff {L M N f : V}
    (hM : IsStructureCode L M) (hN : IsStructureCode L N) :
    RealizesCodedElementaryDiagram L M N f ↔ IsCodedElementaryEmbedding L M N f := by
  constructor
  · rintro ⟨hf, hd⟩
    refine ⟨hM, hN, hf, ?_⟩
    intro n hn φ hφ b hb
    have hc : ∀ ψ ∈ formulaSet L ∅ n, Satisfies L ∅ M ∅ n ψ b →
        Satisfies L ∅ N ∅ n ψ (compose b f) := by
      intro ψ hψ hs
      have hh := hd ⟨⟨n, ψ⟩ₖ, b⟩ₖ ((pair_mem_codedElementaryDiagram hM.language).mpr ⟨hψ, hb, hs⟩)
      simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hh
    constructor
    · exact hc φ hφ
    · intro hs
      by_contra hh
      have hnφ := negateFormula_mem hM.language hφ
      have hneg := hc _ hnφ ((satisfies_negateFormula hM.language hφ hb).mpr hh)
      exact ((satisfies_negateFormula hM.language hφ (compose_function hb hf)).mp hneg) hs
  · intro h
    refine ⟨h.function, fun p hp ↦ ?_⟩
    obtain ⟨n, hn, φ, hφ, b, hb, rfl, hs⟩ := codedElementaryDiagram_cases hM.language hp
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using (h.satisfies_iff hn hφ hb).mp hs

end ZFVP
