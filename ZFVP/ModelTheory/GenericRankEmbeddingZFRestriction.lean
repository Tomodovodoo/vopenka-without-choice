import ZFVP.ModelTheory.EndExtensionCodedEmbedding
import ZFVP.ModelTheory.GenericRankEmbeddingRestriction

/-! Arbitrary-language restriction between rank stages that model ZF.

Full syntax and satisfaction are absolute between transitive ZF models, so this
route requires no numerical bound on the syntactic presentation of the
dictionary. The C(n) hypotheses below are used for the fixed-critical-point and
rank-closure lemmas, not to estimate the complexity of coded satisfaction.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem structureCodeFormula_correct (v : Fin 2 → SetDomain U) :
    isStructureCodeFormula.Evalb v ↔ IsStructureCode (v 0).val (v 1).val :=
  (Defined.eval_iff (R := fun w : Fin 2 → SetDomain U ↦ IsStructureCode (w 0) (w 1)) v).trans
    ((MembershipEndExtension.transitiveSubtype U).structureCode_iff (v 0) (v 1)).symm

theorem satisfiesFormula_correct (v : Fin 7 → SetDomain U) (hL : IsLanguageCode (v 0).val) :
    satisfiesFormula.Evalb v ↔
      Satisfies (v 0).val (v 1).val (v 2).val (v 3).val (v 4).val (v 5).val (v 6).val := by
  let j := MembershipEndExtension.transitiveSubtype U
  have hLi : IsLanguageCode (v 0) := (j.languageCode_iff (v 0)).mp hL
  exact (Defined.eval_iff (R := fun w : Fin 7 → SetDomain U ↦
    Satisfies (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)) v).trans
    (j.satisfies_iff hLi (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)).symm

end TransitiveZF

theorem rankEmbedding_structureCode_iff_zf {δ ε f L M : V}
    [IsOrdinal δ] [IsOrdinal ε]
    [Nonempty (SetDomain (hierarchy δ))] [Nonempty (SetDomain (hierarchy ε))]
    [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    [(SetDomain (hierarchy ε))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hL : L ∈ hierarchy δ) (hM : M ∈ hierarchy δ) :
    IsStructureCode L M ↔ IsStructureCode (f ‘ L) (f ‘ M) := by
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  let v : Fin 2 → SetDomain (hierarchy δ) := ![⟨L, hL⟩, ⟨M, hM⟩]
  exact (TransitiveZF.structureCodeFormula_correct (hierarchy δ) v).symm.trans
    ((h.eval_semisentence isStructureCodeFormula v).trans
      (TransitiveZF.structureCodeFormula_correct (hierarchy ε) (h.toFunction ∘ v)))

theorem rankEmbedding_satisfies_iff_zf {δ ε f : V}
    [IsOrdinal δ] [IsOrdinal ε]
    [Nonempty (SetDomain (hierarchy δ))] [Nonempty (SetDomain (hierarchy ε))]
    [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    [(SetDomain (hierarchy ε))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (v : Fin 7 → V) (hv : ∀ i, v i ∈ hierarchy δ)
    (hL : IsLanguageCode (v 0)) (hL' : IsLanguageCode (f ‘ (v 0))) :
    Satisfies (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) ↔
      Satisfies (f ‘ (v 0)) (f ‘ (v 1)) (f ‘ (v 2)) (f ‘ (v 3))
        (f ‘ (v 4)) (f ‘ (v 5)) (f ‘ (v 6)) := by
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  let b : Fin 7 → SetDomain (hierarchy δ) := fun i ↦ ⟨v i, hv i⟩
  exact (TransitiveZF.satisfiesFormula_correct (hierarchy δ) b hL).symm.trans
    ((h.eval_semisentence satisfiesFormula b).trans
      (TransitiveZF.satisfiesFormula_correct (hierarchy ε) (h.toFunction ∘ b) hL'))

/-- A rank embedding restricts to an internally elementary map of every coded
structure whose language and syntax lie below the critical point. The source
and target ranks model ZF; no coarse dictionary-complexity bound is required. -/
theorem rankEmbedding_generic_restrict_zf {k : ℕ} {δ ε f κ L M : V}
    [Nonempty (SetDomain (hierarchy δ))] [Nonempty (SetDomain (hierarchy ε))]
    [(SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    [(SetDomain (hierarchy ε))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hδ : Cn (k + 1) δ) (hε : Cn (k + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hLκ : L ∈ hierarchy κ) (hsyntax : syntaxUniverse L ∅ ⊆ hierarchy κ)
    (hM : IsStructureCode L M) (hMδ : M ∈ hierarchy δ) :
    IsCodedElementaryEmbedding L M (f ‘ M) (f ↾ (structureDomain M)) := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  have hVκ := hδ.hierarchy_closed hκ.ordinal hκ.mem_domain
  have hinc : hierarchy κ ⊆ hierarchy δ := (hierarchy_transitive δ).transitive _ hVκ
  have hfix := rankEmbedding_fixed_below_criticalPoint hδ hε h hκ
  have hLδ := hinc L hLκ
  have hLfix := hfix L hLκ
  have htarget' : IsStructureCode (f ‘ L) (f ‘ M) :=
    (rankEmbedding_structureCode_iff_zf h hLδ hMδ).mp hM
  have htarget : IsStructureCode L (f ‘ M) := by simpa only [hLfix] using htarget'
  have hD := hM.domain_mem_transitive hMδ
  have hsub : structureDomain M ⊆ hierarchy δ := (hierarchy_transitive δ).transitive _ hD
  have hfun : f ↾ (structureDomain M) ∈ structureDomain (f ‘ M) ^ structureDomain M := by
    rw [← h.value_structureDomain hM hMδ]
    exact h.restriction_function hD
  refine ⟨hM, htarget, hfun, ?_⟩
  intro n hn φ hφ b hb
  have hφU : φ ∈ syntaxUniverse L ∅ := (kpair_components_mem_transitive
    (formulaFamily_subset_syntaxUniverse L ∅ _ ((mem_formulaSet_iff _ _ _ _).mp hφ))).2
  have hφκ := hsyntax φ hφU
  have hφδ := hinc φ hφκ
  have hbδ := function_mem_sequenceSupport hsub hn hb
  have h0 : (∅ : V) ∈ hierarchy δ := IsCodingSupport.empty_mem
  have hnδ : n ∈ hierarchy δ := IsCodingSupport.natural_mem hn
  have he := rankEmbedding_satisfies_iff_zf h ![L, ∅, M, ∅, n, φ, b]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hLδ, h0, hMδ, hnδ, hφδ, hbδ])
    hM.language htarget'.language
  change Satisfies L ∅ M ∅ n φ b ↔
    Satisfies (f ‘ L) (f ‘ ∅) (f ‘ M) (f ‘ ∅) (f ‘ n) (f ‘ φ) (f ‘ b) at he
  rw [hLfix, h.value_empty h0, h.value_natural hn, hfix φ hφκ,
    h.value_assignment hn hbδ (mem_function_of_mem_function_of_subset hb hsub),
    ← graph_compose_restrict hb f] at he
  exact he

end ZFVP
