import ZFVP.ModelTheory.InternalNamedSupport
import ZFVP.SetTheory.FiniteNaturalSets
import ZFVP.Syntax.BinaryRelationInternalSemantics

/-! A finite set of named formulas is equivalent to one raw formula in a
common internal finite context. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def namedFormulaInContext (n p : V) : V :=
  renameMembershipFormula (kpair.π₁ (kpair.π₁ p)) n
    (kpair.π₂ p) (kpair.π₂ (kpair.π₁ p))

instance namedFormulaInContext_definable : ℒₛₑₜ-function₂[V] namedFormulaInContext := by
  unfold namedFormulaInContext
  definability

@[simp] theorem namedFormulaInContext_pair (n k φ b : V) :
    namedFormulaInContext n ⟨⟨k, φ⟩ₖ, b⟩ₖ = renameMembershipFormula k n b φ := by
  simp only [namedFormulaInContext, kpair.π₁_kpair, kpair.π₂_kpair]

theorem namedTuple_mem_of_support {A n k φ b : V} (hb : b ∈ A ^ k)
    (hs : namedFormulaSupport ⟨⟨k, φ⟩ₖ, b⟩ₖ ⊆ n) : b ∈ n ^ k := by
  have : IsFunction b := IsFunction.of_mem hb
  apply mem_function.intro
  · intro p hp
    obtain ⟨i, hi, x, _, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hb p hp)
    exact kpair_mem_iff.mpr ⟨hi, hs x (by
      simpa only [namedFormulaSupport, kpair.π₂_kpair] using mem_range_of_kpair_mem hp)⟩
  · intro i hi
    exact (mem_function_iff.mp hb).2 i hi

theorem namedFormulaInContext_mem {n p : V} (hn : n ∈ (ω : V))
    (hp : p ∈ namedFormulaSet membershipLanguageCode (ω : V))
    (hs : namedFormulaSupport p ⊆ n) :
    namedFormulaInContext n p ∈ formulaSet membershipLanguageCode ∅ n := by
  obtain ⟨k, hk, φ, hφ, b, hb, rfl⟩ := namedFormulaSet_cases membershipLanguageCode_valid hp
  rw [namedFormulaInContext_pair]
  exact renameMembershipFormula_mem hk hn (namedTuple_mem_of_support hb hs) hφ

theorem namedFormulaInContext_satisfies {M f n p : V}
    (hM : IsStructureCode membershipLanguageCode M) (hf : f ∈ structureDomain M ^ (ω : V))
    (hn : n ∈ (ω : V)) (hp : p ∈ namedFormulaSet membershipLanguageCode (ω : V))
    (hs : namedFormulaSupport p ⊆ n) :
    Satisfies membershipLanguageCode ∅ M ∅ n (namedFormulaInContext n p) (f ↾ n) ↔
      NamedHolds membershipLanguageCode M f p := by
  obtain ⟨k, hk, φ, hφ, b, hb, rfl⟩ := namedFormulaSet_cases membershipLanguageCode_valid hp
  have hbn := namedTuple_mem_of_support hb hs
  have hfn := function_restrict_mem hf (IsTransitive.ω.transitive n hn)
  rw [namedFormulaInContext_pair, namedHolds_pair,
    codedMembershipSatisfies_rename hM hk hn hbn hφ hfn, graph_compose_restrict hbn]

theorem exists_internal_namedConjunction {A : V} (hA : IsInternallyFinite A)
    (hsub : A ⊆ namedFormulaSet membershipLanguageCode (ω : V)) :
    ∃ n ∈ (ω : V), namedTheorySupport A ⊆ n ∧
      ∃ χ ∈ formulaSet membershipLanguageCode ∅ n,
        ∀ M, IsStructureCode membershipLanguageCode M →
          ∀ f ∈ structureDomain M ^ (ω : V),
            ((∀ p ∈ A, NamedHolds membershipLanguageCode M f p) ↔
              Satisfies membershipLanguageCode ∅ M ∅ n χ (f ↾ n)) := by
  obtain ⟨n, hn, hsupport⟩ := internallyFinite_naturals_bounded
    (namedTheorySupport_finite membershipLanguageCode_valid hsub hA)
    (namedTheorySupport_subset membershipLanguageCode_valid hsub)
  have hs : ∀ p ∈ A, namedFormulaSupport p ⊆ n := by
    intro p hp x hx
    exact hsupport x ((mem_namedTheorySupport A x).mpr ⟨p, hp, hx⟩)
  let C : V := repl (namedFormulaInContext n) (by definability) A
  have hC : IsInternallyFinite C := internallyFinite_repl _ _ hA
  have hCsub : C ⊆ formulaSet membershipLanguageCode ∅ n := by
    intro ψ hψ
    obtain ⟨p, hp, rfl⟩ := (repl_spec _).mp hψ
    exact namedFormulaInContext_mem hn (hsub p hp) (hs p hp)
  obtain ⟨χ, hχ, hχeq⟩ := exists_internal_finiteConjunction membershipLanguageCode_valid hn hC hCsub
  refine ⟨n, hn, hsupport, χ, hχ, ?_⟩
  intro M hM f hf
  rw [hχeq M ∅ (f ↾ n) (function_restrict_mem hf (IsTransitive.ω.transitive n hn))]
  constructor
  · intro hh ψ hψ
    obtain ⟨p, hp, rfl⟩ := (repl_spec _).mp hψ
    exact (namedFormulaInContext_satisfies hM hf hn (hsub p hp) (hs p hp)).mpr (hh p hp)
  · intro hh p hp
    apply (namedFormulaInContext_satisfies hM hf hn (hsub p hp) (hs p hp)).mp
    exact hh _ ((repl_spec _).mpr ⟨p, hp, rfl⟩)

end ZFVP
