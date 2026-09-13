import ZFVP.ModelTheory.InternalNamedConditions

/-! An actual countable family of all named existential-witness requirements. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def namedFormulaPayloads (L : V) : V := repl kpair.π₂ (by definability) (formulaFamily L ∅)

instance namedFormulaPayloads_definable : ℒₛₑₜ-function₁[V] namedFormulaPayloads := by
  unfold namedFormulaPayloads
  definability

noncomputable def namedWitnessQueries (L : V) : V :=
  {q ∈ (ω : V) ×ˢ (namedFormulaPayloads L ×ˢ finiteSequences (ω : V)) ;
    kpair.π₁ (kpair.π₂ q) ∈ formulaSet L ∅ (succ (kpair.π₁ q)) ∧
      kpair.π₂ (kpair.π₂ q) ∈ (ω : V) ^ (kpair.π₁ q)}

instance namedWitnessQueries_definable : ℒₛₑₜ-function₁[V] namedWitnessQueries := by
  have h : ℒₛₑₜ-relation[V] (fun Q L ↦ ∀ q, q ∈ Q ↔
      q ∈ (ω : V) ×ˢ (namedFormulaPayloads L ×ˢ finiteSequences (ω : V)) ∧
        kpair.π₁ (kpair.π₂ q) ∈ formulaSet L ∅ (succ (kpair.π₁ q)) ∧
          kpair.π₂ (kpair.π₂ q) ∈ (ω : V) ^ (kpair.π₁ q)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedWitnessQueries, mem_sep_iff]
  rfl

theorem pair_mem_namedWitnessQueries (L n φ b : V) : ⟨n, ⟨φ, b⟩ₖ⟩ₖ ∈ namedWitnessQueries L ↔
    n ∈ (ω : V) ∧ φ ∈ formulaSet L ∅ (succ n) ∧ b ∈ (ω : V) ^ n := by
  simp only [namedWitnessQueries, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨⟨hn, _⟩, hφ, hb⟩
    exact ⟨hn, hφ, hb⟩
  · rintro ⟨hn, hφ, hb⟩
    have hp : φ ∈ namedFormulaPayloads L :=
      (repl_spec _).mpr ⟨⟨succ n, φ⟩ₖ, (mem_formulaSet_iff _ _ _ _).mp hφ, by simp⟩
    exact ⟨⟨hn, hp, (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hb⟩⟩, hφ, hb⟩

theorem namedWitnessQueries_cases {L q : V} (hq : q ∈ namedWitnessQueries L) :
    ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet L ∅ (succ n), ∃ b ∈ (ω : V) ^ n, q = ⟨n, ⟨φ, b⟩ₖ⟩ₖ := by
  have hqb := (mem_sep_iff.mp hq).1
  obtain ⟨n, _, r, hr, rfl⟩ := mem_prod_iff.mp hqb
  obtain ⟨φ, _, b, _, rfl⟩ := mem_prod_iff.mp hr
  obtain ⟨hn, hφ, hb⟩ := (pair_mem_namedWitnessQueries L n φ b).mp hq
  exact ⟨n, hn, φ, hφ, b, hb, rfl⟩

theorem namedWitnessQueries_countable (hAC : InternalChoice V) {L : V}
    (hF : IsInternallyCountable (formulaFamily L (∅ : V))) :
    IsInternallyCountable (namedWitnessQueries L) := by
  apply internallyCountable_subset
    ((prod_cardLE_prod internallyCountable_omega
      ((prod_cardLE_prod (internallyCountable_repl kpair.π₂ (by definability) hF)
        (Schmerl.internallyCountable_finiteSequences hAC internallyCountable_omega)).trans omega_prod_cardLE_omega)).trans
      omega_prod_cardLE_omega)
  exact fun _ hp ↦ (mem_sep_iff.mp hp).1

noncomputable def namedWitnessDense (P L q : V) : V :=
  {A ∈ P ;
    namedNegation L ⟨⟨kpair.π₁ q, existsCode (kpair.π₁ (kpair.π₂ q))⟩ₖ, kpair.π₂ (kpair.π₂ q)⟩ₖ ∈ A ∨
      ∃ k ∈ (ω : V), ⟨⟨succ (kpair.π₁ q), kpair.π₁ (kpair.π₂ q)⟩ₖ,
        assignmentPrepend (kpair.π₁ q) (kpair.π₂ (kpair.π₂ q)) k⟩ₖ ∈ A}

instance namedWitnessDense_definable : ℒₛₑₜ-function₃[V] namedWitnessDense := by
  have h : ℒₛₑₜ-relation₄[V] (fun W P L q ↦ ∀ A, A ∈ W ↔ A ∈ P ∧
      (namedNegation L ⟨⟨kpair.π₁ q, existsCode (kpair.π₁ (kpair.π₂ q))⟩ₖ, kpair.π₂ (kpair.π₂ q)⟩ₖ ∈ A ∨
        ∃ k ∈ (ω : V), ⟨⟨succ (kpair.π₁ q), kpair.π₁ (kpair.π₂ q)⟩ₖ,
          assignmentPrepend (kpair.π₁ q) (kpair.π₂ (kpair.π₂ q)) k⟩ₖ ∈ A)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedWitnessDense, mem_sep_iff]
  rfl

theorem mem_namedWitnessDense_pair (P L A n φ b : V) : A ∈ namedWitnessDense P L ⟨n, ⟨φ, b⟩ₖ⟩ₖ ↔
    A ∈ P ∧ (namedNegation L ⟨⟨n, existsCode φ⟩ₖ, b⟩ₖ ∈ A ∨
      ∃ k ∈ (ω : V), ⟨⟨succ n, φ⟩ₖ, assignmentPrepend n b k⟩ₖ ∈ A) := by
  simp only [namedWitnessDense, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair]

theorem namedWitnessDense_dense {L M j B q : V} (hL : IsLanguageCode L)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hfr : HasFreshBackgroundNames j B)
    (hq : q ∈ namedWitnessQueries L) :
    ForcingDense (namedFiniteConditions L M j B) (reverseInclusionOrder (namedFiniteConditions L M j B))
      (namedWitnessDense (namedFiniteConditions L M j B) L q) := by
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := namedWitnessQueries_cases hq
  refine ⟨fun _ hA ↦ (mem_sep_iff.mp hA).1, fun A hA ↦ ?_⟩
  obtain ⟨k, hk, hkj, hkB, hkb⟩ := freshName_for_condition hL hA hn hb hfr
  have hAF := ((mem_namedFiniteConditions _ _ _ _ _).mp hA).2.2
  have hp := (pair_mem_namedFormulaSet_iff hL).mpr ⟨(formulaSet_quantifiers hL hn hφ).2, hb⟩
  rcases hAF.decide_or_fresh_witness hL hj hn hφ hb hk hkj hkB hkb with h | h
  · have hnew := namedFiniteCondition_extend hA (namedNegation_mem hL hp) h
    refine ⟨_, (mem_namedWitnessDense_pair _ _ _ _ _ _).mpr ⟨hnew, Or.inl (by simp)⟩, ?_⟩
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hnew, hA, fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)⟩
  · have hw := (pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, assignmentPrepend_mem_function hn hb hk⟩
    have hnew := namedFiniteCondition_extend hA hw h
    refine ⟨_, (mem_namedWitnessDense_pair _ _ _ _ _ _).mpr ⟨hnew, Or.inr ⟨k, hk, by simp⟩⟩, ?_⟩
    exact (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hnew, hA, fun _ hx ↦ mem_union_iff.mpr (Or.inl hx)⟩

noncomputable def namedHenkinDenseFamily (P L : V) : V :=
  repl (namedDecisionDense P L) (by definability) (namedFormulaSet L (ω : V)) ∪
    repl (namedWitnessDense P L) (by definability) (namedWitnessQueries L)

instance namedHenkinDenseFamily_definable : ℒₛₑₜ-function₂[V] namedHenkinDenseFamily := by
  have h : ℒₛₑₜ-relation₃[V] (fun F P L ↦ ∀ D, D ∈ F ↔
      (∃ p ∈ namedFormulaSet L (ω : V), D = namedDecisionDense P L p) ∨
        ∃ q ∈ namedWitnessQueries L, D = namedWitnessDense P L q) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = namedHenkinDenseFamily (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [namedHenkinDenseFamily, mem_union_iff, repl_spec]

theorem namedHenkinDenseFamily_countable (hAC : InternalChoice V) {P L : V}
    (hL : IsLanguageCode L) (hF : IsInternallyCountable (functionSymbols L))
    (hR : IsInternallyCountable (relationSymbols L)) : IsInternallyCountable (namedHenkinDenseFamily P L) :=
  internallyCountable_union
    (internallyCountable_repl _ _ (namedFormulaSet_countable hAC hL hF hR internallyCountable_omega))
    (internallyCountable_repl _ _ (namedWitnessQueries_countable hAC
      (Schmerl.formulaFamily_countable hAC hL hF hR internallyCountable_empty)))

theorem namedHenkinDenseFamily_dense {L M j B : V} (hL : IsLanguageCode L)
    (hj : j ∈ (ω : V) ^ structureDomain M) (hfr : HasFreshBackgroundNames j B) :
    ∀ D ∈ namedHenkinDenseFamily (namedFiniteConditions L M j B) L,
      ForcingDense (namedFiniteConditions L M j B) (reverseInclusionOrder (namedFiniteConditions L M j B)) D := by
  intro D hD
  rcases mem_union_iff.mp hD with hD | hD
  · obtain ⟨p, hp, rfl⟩ := (repl_spec _).mp hD
    exact namedDecisionDense_dense hL hp
  · obtain ⟨q, hq, rfl⟩ := (repl_spec _).mp hD
    exact namedWitnessDense_dense hL hj hfr hq

end ZFVP
