import ZFVP.ModelTheory.SchmerlCodedRubinSource
import ZFVP.ModelTheory.SchmerlInternalCodedSyntaxCountable

/-! Raw formula and parameter witnesses for unary and binary definitions.
The codes retain the parameter length, formula, and tuple as actual sets. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] codedSatisfies

noncomputable def definitionParameterCount (d : V) : V := kpair.π₁ (kpair.π₁ d)
noncomputable def definitionFormula (d : V) : V := kpair.π₂ (kpair.π₁ d)
noncomputable def definitionTuple (d : V) : V := kpair.π₂ d

instance definitionParameterCount_definable : ℒₛₑₜ-function₁[V] definitionParameterCount := by
  unfold definitionParameterCount; definability
instance definitionFormula_definable : ℒₛₑₜ-function₁[V] definitionFormula := by
  unfold definitionFormula; definability
instance definitionTuple_definable : ℒₛₑₜ-function₁[V] definitionTuple := by
  unfold definitionTuple; definability

@[simp] theorem definitionParameterCount_pair (n φ b : V) : definitionParameterCount ⟨⟨n, φ⟩ₖ, b⟩ₖ = n := by
  simp [definitionParameterCount]
@[simp] theorem definitionFormula_pair (n φ b : V) : definitionFormula ⟨⟨n, φ⟩ₖ, b⟩ₖ = φ := by
  simp [definitionFormula]
@[simp] theorem definitionTuple_pair (n φ b : V) : definitionTuple ⟨⟨n, φ⟩ₖ, b⟩ₖ = b := by
  simp [definitionTuple]

noncomputable def rawDefinitionParameters (M : V) : V :=
  ((ω : V) ×ˢ range (formulaFamily membershipLanguageCode ∅)) ×ˢ finiteSequences (structureDomain M)

instance rawDefinitionParameters_definable : ℒₛₑₜ-function₁[V] rawDefinitionParameters := by
  unfold rawDefinitionParameters; definability

noncomputable def unaryDefinitionParameters (M : V) : V :=
  {d ∈ rawDefinitionParameters M ;
    definitionFormula d ∈ formulaSet membershipLanguageCode ∅ (succ (definitionParameterCount d)) ∧
    definitionTuple d ∈ structureDomain M ^ definitionParameterCount d}

noncomputable def binaryDefinitionParameters (M : V) : V :=
  {d ∈ rawDefinitionParameters M ;
    definitionFormula d ∈ formulaSet membershipLanguageCode ∅ (succ (succ (definitionParameterCount d))) ∧
    definitionTuple d ∈ structureDomain M ^ definitionParameterCount d}

instance unaryDefinitionParameters_definable : ℒₛₑₜ-function₁[V] unaryDefinitionParameters := by
  have h : ℒₛₑₜ-relation[V] (fun U M ↦ ∀ d, d ∈ U ↔ d ∈ rawDefinitionParameters M ∧
    definitionFormula d ∈ formulaSet membershipLanguageCode ∅ (succ (definitionParameterCount d)) ∧
    definitionTuple d ∈ structureDomain M ^ definitionParameterCount d) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [unaryDefinitionParameters, mem_sep_iff]
  rfl

instance binaryDefinitionParameters_definable : ℒₛₑₜ-function₁[V] binaryDefinitionParameters := by
  have h : ℒₛₑₜ-relation[V] (fun U M ↦ ∀ d, d ∈ U ↔ d ∈ rawDefinitionParameters M ∧
    definitionFormula d ∈ formulaSet membershipLanguageCode ∅ (succ (succ (definitionParameterCount d))) ∧
    definitionTuple d ∈ structureDomain M ^ definitionParameterCount d) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [binaryDefinitionParameters, mem_sep_iff]
  rfl

theorem pair_mem_unaryDefinitionParameters {M n φ b : V} :
    ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ unaryDefinitionParameters M ↔
      n ∈ (ω : V) ∧ φ ∈ formulaSet membershipLanguageCode ∅ (succ n) ∧ b ∈ structureDomain M ^ n := by
  simp only [unaryDefinitionParameters, rawDefinitionParameters, mem_sep_iff, kpair_mem_iff,
    definitionParameterCount_pair, definitionFormula_pair, definitionTuple_pair]
  constructor
  · rintro ⟨⟨⟨hn, _⟩, _⟩, hφ, hb⟩
    exact ⟨hn, hφ, hb⟩
  · rintro ⟨hn, hφ, hb⟩
    exact ⟨⟨⟨hn, mem_range_of_kpair_mem ((mem_formulaSet_iff _ _ _ _).mp hφ)⟩,
      (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hb⟩⟩, hφ, hb⟩

theorem pair_mem_binaryDefinitionParameters {M n φ b : V} :
    ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ binaryDefinitionParameters M ↔
      n ∈ (ω : V) ∧ φ ∈ formulaSet membershipLanguageCode ∅ (succ (succ n)) ∧ b ∈ structureDomain M ^ n := by
  simp only [binaryDefinitionParameters, rawDefinitionParameters, mem_sep_iff, kpair_mem_iff,
    definitionParameterCount_pair, definitionFormula_pair, definitionTuple_pair]
  constructor
  · rintro ⟨⟨⟨hn, _⟩, _⟩, hφ, hb⟩
    exact ⟨hn, hφ, hb⟩
  · rintro ⟨hn, hφ, hb⟩
    exact ⟨⟨⟨hn, mem_range_of_kpair_mem ((mem_formulaSet_iff _ _ _ _).mp hφ)⟩,
      (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hb⟩⟩, hφ, hb⟩

theorem unaryDefinitionParameters_cases {M d : V} (hd : d ∈ unaryDefinitionParameters M) :
    ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet membershipLanguageCode ∅ (succ n),
      ∃ b ∈ structureDomain M ^ n, d = ⟨⟨n, φ⟩ₖ, b⟩ₖ := by
  obtain ⟨a, ha, b, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hd).1
  obtain ⟨n, _, φ, _, rfl⟩ := mem_prod_iff.mp ha
  obtain ⟨hn, hφ, hb⟩ := pair_mem_unaryDefinitionParameters.mp hd
  exact ⟨n, hn, φ, hφ, b, hb, rfl⟩

theorem binaryDefinitionParameters_cases {M d : V} (hd : d ∈ binaryDefinitionParameters M) :
    ∃ n ∈ (ω : V), ∃ φ ∈ formulaSet membershipLanguageCode ∅ (succ (succ n)),
      ∃ b ∈ structureDomain M ^ n, d = ⟨⟨n, φ⟩ₖ, b⟩ₖ := by
  obtain ⟨a, ha, b, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hd).1
  obtain ⟨n, _, φ, _, rfl⟩ := mem_prod_iff.mp ha
  obtain ⟨hn, hφ, hb⟩ := pair_mem_binaryDefinitionParameters.mp hd
  exact ⟨n, hn, φ, hφ, b, hb, rfl⟩

theorem unaryDefinitionParameters_spec {M d : V} (hd : d ∈ unaryDefinitionParameters M) :
    definitionParameterCount d ∈ (ω : V) ∧
      definitionFormula d ∈ formulaSet membershipLanguageCode ∅ (succ (definitionParameterCount d)) ∧
      definitionTuple d ∈ structureDomain M ^ definitionParameterCount d := by
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := unaryDefinitionParameters_cases hd
  simpa only [definitionParameterCount_pair, definitionFormula_pair, definitionTuple_pair] using And.intro hn ⟨hφ, hb⟩

theorem binaryDefinitionParameters_spec {M d : V} (hd : d ∈ binaryDefinitionParameters M) :
    definitionParameterCount d ∈ (ω : V) ∧
      definitionFormula d ∈ formulaSet membershipLanguageCode ∅ (succ (succ (definitionParameterCount d))) ∧
      definitionTuple d ∈ structureDomain M ^ definitionParameterCount d := by
  obtain ⟨n, hn, φ, hφ, b, hb, rfl⟩ := binaryDefinitionParameters_cases hd
  simpa only [definitionParameterCount_pair, definitionFormula_pair, definitionTuple_pair] using And.intro hn ⟨hφ, hb⟩

theorem rawDefinitionParameters_countable (hAC : InternalChoice V) {M : V}
    (hM : IsInternallyCountable (structureDomain M)) : IsInternallyCountable (rawDefinitionParameters M) := by
  have hs : IsInternallyCountable (formulaFamily (membershipLanguageCode : V) ∅) :=
    formulaFamily_countable hAC membershipLanguageCode_valid
      (by simpa only [membershipLanguageCode, functionSymbols_code] using internallyCountable_empty (V := V))
      (by simpa [membershipLanguageCode] using
        (internallyCountable_subset internallyCountable_omega
          (IsOrdinal.toIsTransitive.transitive (2 : V) (by simp))))
      internallyCountable_empty
  exact (prod_cardLE_prod
    ((prod_cardLE_prod internallyCountable_omega (internallyCountable_range hs)).trans omega_prod_cardLE_omega)
    (internallyCountable_finiteSequences hAC hM)).trans omega_prod_cardLE_omega

theorem unaryDefinitionParameters_countable (hAC : InternalChoice V) {M : V}
    (hM : IsInternallyCountable (structureDomain M)) : IsInternallyCountable (unaryDefinitionParameters M) :=
  internallyCountable_subset (rawDefinitionParameters_countable hAC hM) (fun _ hd ↦ (mem_sep_iff.mp hd).1)

theorem binaryDefinitionParameters_countable (hAC : InternalChoice V) {M : V}
    (hM : IsInternallyCountable (structureDomain M)) : IsInternallyCountable (binaryDefinitionParameters M) :=
  internallyCountable_subset (rawDefinitionParameters_countable hAC hM) (fun _ hd ↦ (mem_sep_iff.mp hd).1)

noncomputable def unaryDefinitionSet (M d : V) : V :=
  {x ∈ structureDomain M ; codedSatisfies M (succ (definitionParameterCount d)) (definitionFormula d)
    (assignmentPrepend (definitionParameterCount d) (definitionTuple d) x)}

noncomputable def binaryDefinitionRelation (M d : V) : V :=
  {p ∈ structureDomain M ×ˢ structureDomain M ;
    codedSatisfies M (succ (succ (definitionParameterCount d))) (definitionFormula d)
      (assignmentPrepend (succ (definitionParameterCount d))
        (assignmentPrepend (definitionParameterCount d) (definitionTuple d) (kpair.π₂ p)) (kpair.π₁ p))}

instance unaryDefinitionSet_definable : ℒₛₑₜ-function₂[V] unaryDefinitionSet := by
  have h : ℒₛₑₜ-relation₃[V] (fun P M d ↦ ∀ x, x ∈ P ↔ x ∈ structureDomain M ∧
    codedSatisfies M (succ (definitionParameterCount d)) (definitionFormula d)
      (assignmentPrepend (definitionParameterCount d) (definitionTuple d) x)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [unaryDefinitionSet, mem_sep_iff]
  rfl

instance binaryDefinitionRelation_definable : ℒₛₑₜ-function₂[V] binaryDefinitionRelation := by
  have h : ℒₛₑₜ-relation₃[V] (fun R M d ↦ ∀ p, p ∈ R ↔ p ∈ structureDomain M ×ˢ structureDomain M ∧
    codedSatisfies M (succ (succ (definitionParameterCount d))) (definitionFormula d)
      (assignmentPrepend (succ (definitionParameterCount d))
        (assignmentPrepend (definitionParameterCount d) (definitionTuple d) (kpair.π₂ p)) (kpair.π₁ p))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [binaryDefinitionRelation, mem_sep_iff]
  rfl

theorem mem_unaryDefinitionSet (M d x : V) : x ∈ unaryDefinitionSet M d ↔ x ∈ structureDomain M ∧
    codedSatisfies M (succ (definitionParameterCount d)) (definitionFormula d)
      (assignmentPrepend (definitionParameterCount d) (definitionTuple d) x) := mem_sep_iff

theorem pair_mem_binaryDefinitionRelation (M d x y : V) :
    ⟨x, y⟩ₖ ∈ binaryDefinitionRelation M d ↔ (x ∈ structureDomain M ∧ y ∈ structureDomain M) ∧
      codedSatisfies M (succ (succ (definitionParameterCount d))) (definitionFormula d)
        (assignmentPrepend (succ (definitionParameterCount d))
          (assignmentPrepend (definitionParameterCount d) (definitionTuple d) y) x) := by
  simp only [binaryDefinitionRelation, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]

theorem unaryDefinitionSet_subset (M d : V) : unaryDefinitionSet M d ⊆ structureDomain M :=
  fun _ hx ↦ (mem_sep_iff.mp hx).1

theorem binaryDefinitionRelation_subset (M d : V) :
    binaryDefinitionRelation M d ⊆ structureDomain M ×ˢ structureDomain M := fun _ hx ↦ (mem_sep_iff.mp hx).1

theorem unaryDefinitionSet_isCodedDefinable {M d : V} (hd : d ∈ unaryDefinitionParameters M) :
    IsCodedDefinableSet M (unaryDefinitionSet M d) := by
  obtain ⟨hn, hφ, hb⟩ := unaryDefinitionParameters_spec hd
  refine ⟨unaryDefinitionSet_subset M d, definitionParameterCount d, hn, definitionFormula d, hφ,
    definitionTuple d, hb, fun x hx ↦ ?_⟩
  exact ⟨fun h ↦ (mem_unaryDefinitionSet M d x).mp h |>.2,
    fun h ↦ (mem_unaryDefinitionSet M d x).mpr ⟨hx, h⟩⟩

theorem binaryDefinitionRelation_isCodedDefinable {M d : V} (hd : d ∈ binaryDefinitionParameters M) :
    IsCodedDefinableRelation M (binaryDefinitionRelation M d) := by
  obtain ⟨hn, hφ, hb⟩ := binaryDefinitionParameters_spec hd
  refine ⟨binaryDefinitionRelation_subset M d, definitionParameterCount d, hn, definitionFormula d, hφ,
    definitionTuple d, hb, fun x hx y hy ↦ ?_⟩
  exact ⟨fun h ↦ (pair_mem_binaryDefinitionRelation M d x y).mp h |>.2,
    fun h ↦ (pair_mem_binaryDefinitionRelation M d x y).mpr ⟨⟨hx, hy⟩, h⟩⟩

theorem IsCodedDefinableSet.exists_unaryDefinition {M P : V} (h : IsCodedDefinableSet M P) :
    ∃ d ∈ unaryDefinitionParameters M, unaryDefinitionSet M d = P := by
  obtain ⟨hP, n, hn, φ, hφ, b, hb, hdef⟩ := h
  refine ⟨⟨⟨n, φ⟩ₖ, b⟩ₖ, pair_mem_unaryDefinitionParameters.mpr ⟨hn, hφ, hb⟩, ?_⟩
  apply mem_ext
  intro x
  simp only [mem_unaryDefinitionSet, definitionParameterCount_pair, definitionFormula_pair, definitionTuple_pair]
  exact ⟨fun hx ↦ (hdef x hx.1).mpr hx.2, fun hx ↦ ⟨hP x hx, (hdef x (hP x hx)).mp hx⟩⟩

theorem IsCodedDefinableRelation.exists_binaryDefinition {M R : V} (h : IsCodedDefinableRelation M R) :
    ∃ d ∈ binaryDefinitionParameters M, binaryDefinitionRelation M d = R := by
  obtain ⟨hR, n, hn, φ, hφ, b, hb, hdef⟩ := h
  refine ⟨⟨⟨n, φ⟩ₖ, b⟩ₖ, pair_mem_binaryDefinitionParameters.mpr ⟨hn, hφ, hb⟩, ?_⟩
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (binaryDefinitionRelation_subset _ _ _ hp)
    exact (hdef x hx y hy).mpr (by
      simpa only [definitionParameterCount_pair, definitionFormula_pair, definitionTuple_pair] using
        ((pair_mem_binaryDefinitionRelation _ _ _ _).mp hp).2)
  · intro hp
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (hR p hp)
    apply (pair_mem_binaryDefinitionRelation _ _ _ _).mpr
    exact ⟨⟨hx, hy⟩, by simpa only [definitionParameterCount_pair, definitionFormula_pair, definitionTuple_pair]
      using (hdef x hx y hy).mp hp⟩

end ZFVP.Schmerl
