import ZFVP.ModelTheory.SchmerlInternalCodedSubstructure
import ZFVP.ModelTheory.SchmerlInternalCodedHullClosure

/-! Actual internal unions of ordinal chains in relational languages.
Carriers and relation interpretations are constructed by Replacement and Union. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsInternalRelationalChain (L θ C : V) : Prop where
  ordinal : IsOrdinal θ
  nonempty : IsNonempty θ
  function : IsFunction C
  domain : domain C = θ
  noFunctions : functionSymbols L = ∅
  valid : ∀ i ∈ θ, IsStructureCode L (C ‘ i)
  increasing : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → structureDomain (C ‘ i) ⊆ structureDomain (C ‘ j)
  coherent : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ r ∈ relationSymbols L,
    ∀ s ∈ structureDomain (C ‘ i) ^ ((relationArities L) ‘ r),
      (s ∈ (structureRelations (C ‘ i)) ‘ r ↔ s ∈ (structureRelations (C ‘ j)) ‘ r)
  elementary : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
    IsCodedElementaryEmbedding L (C ‘ i) (C ‘ j) (SetTheory.identity (structureDomain (C ‘ i)))

theorem isInternalRelationalChain_iff (L θ C : V) : IsInternalRelationalChain L θ C ↔
    IsOrdinal θ ∧ IsNonempty θ ∧ IsFunction C ∧ domain C = θ ∧ functionSymbols L = ∅ ∧
    (∀ i ∈ θ, IsStructureCode L (C ‘ i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → structureDomain (C ‘ i) ⊆ structureDomain (C ‘ j)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ r ∈ relationSymbols L,
      ∀ s ∈ structureDomain (C ‘ i) ^ ((relationArities L) ‘ r),
        (s ∈ (structureRelations (C ‘ i)) ‘ r ↔ s ∈ (structureRelations (C ‘ j)) ‘ r)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsCodedElementaryEmbedding L (C ‘ i) (C ‘ j) (SetTheory.identity (structureDomain (C ‘ i)))) := by
  constructor
  · intro h
    exact ⟨h.ordinal, h.nonempty, h.function, h.domain, h.noFunctions,
      h.valid, h.increasing, h.coherent, h.elementary⟩
  · rintro ⟨ho, hn, hf, hd, hF, hv, hi, hc, he⟩
    exact ⟨ho, hn, hf, hd, hF, hv, hi, hc, he⟩

instance isInternalRelationalChain_definable : ℒₛₑₜ-relation₃[V] IsInternalRelationalChain := by
  apply Language.Definable.of_iff (show ℒₛₑₜ-relation₃[V] (fun L θ C ↦
    IsOrdinal θ ∧ IsNonempty θ ∧ IsFunction C ∧ domain C = θ ∧ functionSymbols L = ∅ ∧
    (∀ i ∈ θ, IsStructureCode L (C ‘ i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → structureDomain (C ‘ i) ⊆ structureDomain (C ‘ j)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ r ∈ relationSymbols L,
      ∀ s ∈ structureDomain (C ‘ i) ^ ((relationArities L) ‘ r),
        (s ∈ (structureRelations (C ‘ i)) ‘ r ↔ s ∈ (structureRelations (C ‘ j)) ‘ r)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsCodedElementaryEmbedding L (C ‘ i) (C ‘ j) (SetTheory.identity (structureDomain (C ‘ i))))) from by
      definability)
  intro v
  exact isInternalRelationalChain_iff _ _ _

noncomputable def codedChainCarrier (θ C : V) : V :=
  ⋃ˢ repl (fun i ↦ structureDomain (C ‘ i)) (by definability) θ

theorem mem_codedChainCarrier (θ C x : V) :
    x ∈ codedChainCarrier θ C ↔ ∃ i ∈ θ, x ∈ structureDomain (C ‘ i) := by
  simp only [codedChainCarrier, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨D, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hx⟩

instance codedChainCarrier_definable : ℒₛₑₜ-function₂[V] codedChainCarrier := by
  have h : ℒₛₑₜ-relation₃[V] (fun D θ C ↦ ∀ x, x ∈ D ↔ ∃ i ∈ θ, x ∈ structureDomain (C ‘ i)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedChainCarrier]
  rfl

noncomputable def codedChainRelation (θ C r : V) : V :=
  ⋃ˢ repl (fun i ↦ (structureRelations (C ‘ i)) ‘ r) (by definability) θ

theorem mem_codedChainRelation (θ C r s : V) :
    s ∈ codedChainRelation θ C r ↔ ∃ i ∈ θ, s ∈ (structureRelations (C ‘ i)) ‘ r := by
  simp only [codedChainRelation, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨R, ⟨i, hi, rfl⟩, hs⟩
    exact ⟨i, hi, hs⟩
  · rintro ⟨i, hi, hs⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hs⟩

instance codedChainRelation_definable : ℒₛₑₜ-function₃[V] codedChainRelation := by
  have h : ℒₛₑₜ-relation₄[V] (fun R θ C r ↦ ∀ s,
      s ∈ R ↔ ∃ i ∈ θ, s ∈ (structureRelations (C ‘ i)) ‘ r) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedChainRelation]
  rfl

attribute [local irreducible] codedChainCarrier codedChainRelation

noncomputable def codedChainUnion (L θ C : V) : V :=
  structureCode (codedChainCarrier θ C) (constantGraph ∅ ∅)
    (definableGraph (relationSymbols L) (codedChainRelation θ C) (by definability))

instance codedChainUnion_definable : ℒₛₑₜ-function₃[V] codedChainUnion := by
  have h : ℒₛₑₜ-function₃[V] (fun L θ C ↦
      definableGraph (relationSymbols L) (codedChainRelation θ C) (by definability)) := by
    have hrel : ℒₛₑₜ-relation₄[V] (fun g L θ C ↦ ∀ p, p ∈ g ↔
        ∃ r ∈ relationSymbols L, p = ⟨r, codedChainRelation θ C r⟩ₖ) := by definability
    apply Language.Definable.of_iff hrel
    intro v
    rw [mem_ext_iff]
    simp only [mem_definableGraph_iff]
    rfl
  unfold codedChainUnion
  definability

@[simp] theorem structureDomain_codedChainUnion (L θ C : V) :
    structureDomain (codedChainUnion L θ C) = codedChainCarrier θ C := structureDomain_code _ _ _

theorem codedChainUnion_relation {L θ C r : V} (hr : r ∈ relationSymbols L) :
    (structureRelations (codedChainUnion L θ C)) ‘ r = codedChainRelation θ C r := by
  simp only [codedChainUnion, structureRelations_code]
  exact value_definableGraph _ _ _ hr

theorem codedChainCarrier_includes {θ C i : V} (hi : i ∈ θ) :
    structureDomain (C ‘ i) ⊆ codedChainCarrier θ C :=
  fun _ hx ↦ (mem_codedChainCarrier _ _ _).mpr ⟨i, hi, hx⟩

namespace IsInternalRelationalChain

variable {L θ C : V} (h : IsInternalRelationalChain L θ C)

include h

theorem sequence : C ∈ range C ^ θ := by
  let : IsFunction C := h.function
  simpa only [h.domain] using IsFunction.mem_function C

theorem common {i j : V} (hi : i ∈ θ) (hj : j ∈ θ) : ∃ k ∈ θ, i ⊆ k ∧ j ⊆ k := by
  let : IsOrdinal θ := h.ordinal
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.subset_or_supset i j with hij | hji
  · exact ⟨j, hj, hij, subset_refl _⟩
  · exact ⟨i, hi, subset_refl _, hji⟩

theorem carrier_nonempty : IsNonempty (codedChainCarrier θ C) := by
  obtain ⟨i, hi⟩ := h.nonempty.nonempty
  obtain ⟨x, hx⟩ := (h.valid i hi).domain_nonempty.nonempty
  exact ⟨x, codedChainCarrier_includes hi x hx⟩

theorem union_valid : IsStructureCode L (codedChainUnion L θ C) := by
  obtain ⟨i, hi⟩ := h.nonempty.nonempty
  simp only [IsStructureCode, codedChainUnion, structureDomain_code,
    structureFunctions_code, structureRelations_code, domain_constantGraph, domain_definableGraph]
  refine ⟨(h.valid i hi).language, True.intro, h.carrier_nonempty, inferInstance,
    h.noFunctions.symm, inferInstance, True.intro, ?_, ?_⟩
  · intro f hf
    exact False.elim (not_mem_empty (h.noFunctions ▸ hf))
  · intro r hr
    rw [value_definableGraph _ _ _ hr]
    intro s hs
    obtain ⟨j, hj, hs⟩ := (mem_codedChainRelation _ _ _ _).mp hs
    exact mem_function_of_mem_function_of_subset ((h.valid j hj).relation_tuple_mem hr hs)
      (codedChainCarrier_includes hj)

theorem relation_iff_stage {i r s : V} (hi : i ∈ θ) (hr : r ∈ relationSymbols L)
    (hs : s ∈ structureDomain (C ‘ i) ^ ((relationArities L) ‘ r)) :
    s ∈ codedChainRelation θ C r ↔ s ∈ (structureRelations (C ‘ i)) ‘ r := by
  constructor
  · intro hsu
    obtain ⟨j, hj, hsj⟩ := (mem_codedChainRelation _ _ _ _).mp hsu
    obtain ⟨k, hk, hik, hjk⟩ := h.common hi hj
    exact (h.coherent i hi k hk hik r hr s hs).mpr
      ((h.coherent j hj k hk hjk r hr s ((h.valid j hj).relation_tuple_mem hr hsj)).mp hsj)
  · intro hs
    exact (mem_codedChainRelation _ _ _ _).mpr ⟨i, hi, hs⟩

theorem stage_substructure {i : V} (hi : i ∈ θ) : IsCodedSubstructure L (C ‘ i) (codedChainUnion L θ C) := by
  refine ⟨h.valid i hi, h.union_valid,
    by simpa only [structureDomain_codedChainUnion] using codedChainCarrier_includes (C := C) hi, ?_, ?_⟩
  · intro f hf
    exact False.elim (not_mem_empty (h.noFunctions ▸ hf))
  · intro r hr s hs
    rw [codedChainUnion_relation hr]
    exact (h.relation_iff_stage hi hr hs).symm

/-- Every internal finite tuple is contained in one stage. This is an
internal finite-sequence induction, not an external finiteness argument. -/
theorem tuple_stage {s : V} (hs : s ∈ finiteSequences (codedChainCarrier θ C)) :
    ∃ i ∈ θ, s ∈ finiteSequences (structureDomain (C ‘ i)) := by
  have hrange (s : V) (hs : s ∈ finiteSequences (codedChainCarrier θ C)) :
      ∃ i ∈ θ, range s ⊆ structureDomain (C ‘ i) := by
    apply finiteSequence_induction _ (fun s ↦ ∃ i ∈ θ, range s ⊆ structureDomain (C ‘ i))
      (by definability) ?_ ?_ s hs
    · obtain ⟨i, hi⟩ := h.nonempty.nonempty
      exact ⟨i, hi, by simp only [range_empty]; exact empty_subset _⟩
    · intro n _ t _ x hx ih
      obtain ⟨i, hi, ht⟩ := ih
      obtain ⟨j, hj, hx⟩ := (mem_codedChainCarrier _ _ _).mp hx
      obtain ⟨k, hk, hik, hjk⟩ := h.common hi hj
      refine ⟨k, hk, ?_⟩
      rw [range_insert]
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact h.increasing j hj k hk hjk _ hx
      · exact h.increasing i hi k hk hik y (ht y hy)
  obtain ⟨i, hi, hr⟩ := hrange s hs
  obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff _ _).mp hs
  let : IsFunction s := IsFunction.of_mem hsn
  refine ⟨i, hi, (mem_finiteSequences_iff _ _).mpr ⟨n, hn, ?_⟩⟩
  have hf := mem_function_of_mem_function_of_subset (IsFunction.mem_function s) hr
  simpa only [domain_eq_of_mem_function hsn] using hf

theorem assignment_stage {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ codedChainCarrier θ C ^ n) :
    ∃ i ∈ θ, b ∈ structureDomain (C ‘ i) ^ n := by
  have hbf : b ∈ finiteSequences (codedChainCarrier θ C) :=
    (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hb⟩
  obtain ⟨i, hi, hbi⟩ := h.tuple_stage hbf
  obtain ⟨m, _, hbm⟩ := (mem_finiteSequences_iff _ _).mp hbi
  have he : m = n := (domain_eq_of_mem_function hbm).symm.trans (domain_eq_of_mem_function hb)
  exact ⟨i, hi, he ▸ hbm⟩

end IsInternalRelationalChain

theorem codedChainCarrier_countable (hAC : InternalChoice V) {θ C : V}
    (hθ : IsInternallyCountable θ) (hstage : ∀ i ∈ θ, IsInternallyCountable (structureDomain (C ‘ i))) :
    IsInternallyCountable (codedChainCarrier θ C) := by
  let D := definableGraph θ (fun i ↦ structureDomain (C ‘ i)) (by definability)
  have hc : ∀ i ∈ θ, D ‘ i ≤# (ω : V) := by
    intro i hi
    rw [show D ‘ i = structureDomain (C ‘ i) from value_definableGraph _ _ _ hi]
    exact hstage i hi
  have h := (sUnion_range_cardLE_prod hAC (domain_definableGraph _ _ _) hc).trans
    ((prod_cardLE_prod hθ (CardLE.refl (ω : V))).trans omega_prod_cardLE_omega)
  simpa only [D, range_definableGraph, codedChainCarrier, IsInternallyCountable] using h

end ZFVP.Schmerl
