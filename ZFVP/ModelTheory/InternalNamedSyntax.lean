import ZFVP.ModelTheory.InternalElementaryDiagram
import ZFVP.Syntax.InternalFiniteConjunction

/-! Raw finite formulas with an actual finite tuple of fixed names. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def namedFormulaSet (L A : V) : V :=
  {p ∈ formulaFamily L ∅ ×ˢ finiteSequences A ; kpair.π₂ p ∈ A ^ (kpair.π₁ (kpair.π₁ p))}

theorem mem_namedFormulaSet (L A p : V) : p ∈ namedFormulaSet L A ↔
    p ∈ formulaFamily L ∅ ×ˢ finiteSequences A ∧ kpair.π₂ p ∈ A ^ (kpair.π₁ (kpair.π₁ p)) := mem_sep_iff

instance namedFormulaSet_definable : ℒₛₑₜ-function₂[V] namedFormulaSet := by
  have h : ℒₛₑₜ-relation₃[V] (fun S L A ↦ ∀ p, p ∈ S ↔
      p ∈ formulaFamily L ∅ ×ˢ finiteSequences A ∧ kpair.π₂ p ∈ A ^ (kpair.π₁ (kpair.π₁ p))) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_namedFormulaSet]
  rfl

theorem pair_mem_namedFormulaSet_iff {L A n φ b : V} (hL : IsLanguageCode L) :
    ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ namedFormulaSet L A ↔ φ ∈ formulaSet L ∅ n ∧ b ∈ A ^ n := by
  rw [mem_namedFormulaSet]
  simp only [kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨⟨hφ, _⟩, hb⟩
    exact ⟨(mem_formulaSet_iff _ _ _ _).mpr hφ, hb⟩
  · rintro ⟨hφ, hb⟩
    exact ⟨⟨(mem_formulaSet_iff _ _ _ _).mp hφ,
      (mem_finiteSequences_iff _ _).mpr ⟨n, formulaSet_context hL hφ, hb⟩⟩, hb⟩

theorem namedFormulaSet_cases {L A p : V} (hL : IsLanguageCode L) (hp : p ∈ namedFormulaSet L A) :
    ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet L ∅ n, ∃ b ∈ A ^ n, p = ⟨⟨n, φ⟩ₖ, b⟩ₖ := by
  obtain ⟨r, hr, b, _, he⟩ := mem_prod_iff.mp ((mem_namedFormulaSet _ _ _).mp hp).1
  obtain ⟨n, hn, φ, rfl⟩ := formulaFamily_context hL ∅ hr
  subst p
  obtain ⟨hφ, hb⟩ := (pair_mem_namedFormulaSet_iff hL).mp hp
  exact ⟨n, hn, φ, hφ, b, hb, rfl⟩

theorem namedFormulaSet_countable (hAC : InternalChoice V) {L A : V}
    (hL : IsLanguageCode L) (hF : IsInternallyCountable (functionSymbols L))
    (hR : IsInternallyCountable (relationSymbols L)) (hA : IsInternallyCountable A) :
    IsInternallyCountable (namedFormulaSet L A) :=
  internallyCountable_subset
    ((prod_cardLE_prod (Schmerl.formulaFamily_countable hAC hL hF hR internallyCountable_empty)
      (Schmerl.internallyCountable_finiteSequences hAC hA)).trans omega_prod_cardLE_omega)
    (fun _p hp ↦ ((mem_namedFormulaSet _ _ _).mp hp).1)

def NamedHolds (L M f p : V) : Prop :=
  Satisfies L ∅ M ∅ (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) (compose (kpair.π₂ p) f)

instance namedHolds_definable : ℒₛₑₜ-relation₄[V] NamedHolds := by
  let : ℒₛₑₜ-function₄[V] satisfactionGraph := satisfactionGraphFormula_defined.to_definable
  unfold NamedHolds Satisfies
  definability

@[simp] theorem namedHolds_pair (L M f n φ b : V) :
    NamedHolds L M f ⟨⟨n, φ⟩ₖ, b⟩ₖ ↔ Satisfies L ∅ M ∅ n φ (compose b f) := by
  simp only [NamedHolds, kpair.π₁_kpair, kpair.π₂_kpair]

noncomputable def namedNegation (L p : V) : V :=
  ⟨⟨kpair.π₁ (kpair.π₁ p), negateFormula L ∅ (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p))⟩ₖ, kpair.π₂ p⟩ₖ

instance namedNegation_definable : ℒₛₑₜ-function₂[V] namedNegation := by
  unfold namedNegation
  definability

@[simp] theorem namedNegation_pair (L n φ b : V) :
    namedNegation L ⟨⟨n, φ⟩ₖ, b⟩ₖ = ⟨⟨n, negateFormula L ∅ n φ⟩ₖ, b⟩ₖ := by
  simp only [namedNegation, kpair.π₁_kpair, kpair.π₂_kpair]

theorem namedNegation_mem {L A p : V} (hL : IsLanguageCode L) (hp : p ∈ namedFormulaSet L A) :
    namedNegation L p ∈ namedFormulaSet L A := by
  obtain ⟨n, _, φ, hφ, b, hb, rfl⟩ := namedFormulaSet_cases hL hp
  rw [namedNegation_pair]
  exact (pair_mem_namedFormulaSet_iff hL).mpr ⟨negateFormula_mem hL hφ, hb⟩

theorem namedHolds_negation {L M A f p : V} (hL : IsLanguageCode L)
    (hf : f ∈ structureDomain M ^ A) (hp : p ∈ namedFormulaSet L A) :
    NamedHolds L M f (namedNegation L p) ↔ ¬NamedHolds L M f p := by
  obtain ⟨n, _, φ, hφ, b, hb, rfl⟩ := namedFormulaSet_cases hL hp
  rw [namedNegation_pair, namedHolds_pair, namedHolds_pair]
  exact satisfies_negateFormula hL hφ (compose_function hb hf)

end ZFVP
