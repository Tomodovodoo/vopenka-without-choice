import ZFVP.ModelTheory.InternalHenkinNameContexts
import ZFVP.Syntax.BoundedTruthTables
import ZFVP.SetTheory.FiniteNaturalSets

/-! The accepted diagram induces an actual truth table on finite tuples of
natural names. Its definition is independent of the finite context chosen to
represent those names. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem reverseNameAssignment_injective {n m r t : V} (hm : m ∈ (ω : V))
    (hr : r ∈ m ^ n) (ht : t ∈ m ^ n)
    (he : compose r (reverseIndices m) = compose t (reverseIndices m)) : r = t := by
  have h := congrArg (fun f ↦ compose f (reverseIndices m)) he
  simpa only [graph_compose_assoc, reverseIndices_compose_self hm,
    graph_compose_identity hr, graph_compose_identity ht] using h

theorem exists_reverseNameAssignment {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n) :
    ∃ m ∈ (ω : V), ∃ r ∈ m ^ n, b = compose r (reverseIndices m) := by
  have : IsFunction b := IsFunction.of_mem hb
  have hfin : IsInternallyFinite (domain b) := by
    rw [domain_eq_of_mem_function hb]
    exact ⟨n, hn, CardEQ.refl n⟩
  obtain ⟨m, hm, hbound⟩ := internallyFinite_naturals_bounded
    (internallyFinite_range (internallyFinite_function hfin)) (range_subset_of_mem_function hb)
  have hbm : b ∈ m ^ n := by
    simpa only [domain_eq_of_mem_function hb] using
      mem_function_of_mem_function_of_subset (IsFunction.mem_function b) hbound
  refine ⟨m, hm, compose b (reverseIndices m), compose_function hbm (reverseIndices_function hm), ?_⟩
  rw [graph_compose_assoc, reverseIndices_compose_self hm, graph_compose_identity hbm]

def HenkinNameHolds (T s n φ b : V) : Prop :=
  φ ∈ formulaSet membershipLanguageCode ∅ n ∧ b ∈ (ω : V) ^ n ∧
    ∃ m ∈ (ω : V), ∃ r ∈ m ^ n, b = compose r (reverseIndices m) ∧
      HenkinAccepted T s ⟨m, renameMembershipFormula n m r φ⟩ₖ

instance henkinNameHolds_definable : ℒₛₑₜ-relation₅[V] HenkinNameHolds := by
  change Language.Definable ℒₛₑₜ (fun v : Fin 5 → V ↦
    v 3 ∈ formulaSet membershipLanguageCode ∅ (v 2) ∧ v 4 ∈ (ω : V) ^ (v 2) ∧
      ∃ m ∈ (ω : V), ∃ r ∈ m ^ (v 2), v 4 = compose r (reverseIndices m) ∧
        HenkinAccepted (v 0) (v 1) ⟨m, renameMembershipFormula (v 2) m r (v 3)⟩ₖ)
  apply Language.Definable.and (by definability)
  apply Language.Definable.and (by definability)
  apply Language.Definable.exs
  apply Language.Definable.and (by definability)
  apply Language.Definable.exs
  apply Language.Definable.and (by definability)
  apply Language.Definable.and (by definability)
  apply Language.DefinableRel₃.comp (P := HenkinAccepted) (by definability) (by definability)
  apply Language.DefinableFunction₂.comp (F := kpair) (by definability)
  exact Language.DefinableFunction₄.comp (by definability) (by definability)
    (by definability) (by definability)

theorem henkinNamedRepresentations_agree (hω : Schmerl.HasStandardOmega V) {T s n φ m l r t : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hm : m ∈ (ω : V)) (hl : l ∈ (ω : V)) (hr : r ∈ m ^ n) (ht : t ∈ l ^ n)
    (he : compose r (reverseIndices m) = compose t (reverseIndices l)) :
    HenkinAccepted T s ⟨m, renameMembershipFormula n m r φ⟩ₖ ↔
      HenkinAccepted T s ⟨l, renameMembershipFormula n l t φ⟩ₖ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have hml := ordinalAdd_comm_natural hm hl
  have hr' := compose_function hr (tailShiftIndices_function hm hl)
  have ht' := compose_function ht (tailShiftIndices_function hl hm)
  rw [← hml] at ht'
  have hnames : compose (compose r (tailShiftIndices m l)) (reverseIndices (ordinalAdd m l)) =
      compose (compose t (tailShiftIndices l m)) (reverseIndices (ordinalAdd m l)) := by
    rw [reverseNameAssignment_extend hm hl, hml, reverseNameAssignment_extend hl hm, he]
  have hrt := reverseNameAssignment_injective (ordinalAdd_natural hm hl) hr' ht' hnames
  have ha := hs.named_rename_extend hω hn hm hr hφ hl
  have hb := hs.named_rename_extend hω hn hl ht hφ hm
  rw [hrt, hml] at ha
  exact ha.symm.trans hb

theorem henkinNameHolds_iff_of_rep (hω : Schmerl.HasStandardOmega V) {T s n φ b m r : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) (hb : b = compose r (reverseIndices m)) :
    HenkinNameHolds T s n φ b ↔ HenkinAccepted T s ⟨m, renameMembershipFormula n m r φ⟩ₖ := by
  constructor
  · rintro ⟨_, _, l, hl, t, ht, he, hacc⟩
    exact (henkinNamedRepresentations_agree hω hs hφ hl hm ht hr (he.symm.trans hb)).mp hacc
  · intro hacc
    refine ⟨hφ, ?_, m, hm, r, hr, hb, hacc⟩
    rw [hb]
    exact compose_function hr (reverseIndices_omega_function hm)

noncomputable def henkinNameTruthTable (T s : V) : V :=
  sep ((formulaFamily (membershipLanguageCode : V) ∅) ×ˢ finiteSequences (ω : V))
    (fun p ↦ HenkinNameHolds T s (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) (kpair.π₂ p))
    (Language.DefinableRel₅.comp (by definability) (by definability) (by definability)
      (by definability) (by definability))

instance henkinNameTruthTable_definable : ℒₛₑₜ-function₂[V] henkinNameTruthTable := by
  have he : ℒₛₑₜ-relation₃[V] (fun A T s ↦ ∀ p, p ∈ A ↔
      p ∈ (formulaFamily (membershipLanguageCode : V) ∅) ×ˢ finiteSequences (ω : V) ∧
      HenkinNameHolds T s (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) (kpair.π₂ p)) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional (by definability)
    apply Language.Definable.and (by definability)
    exact Language.DefinableRel₅.comp (by definability) (by definability) (by definability)
      (by definability) (by definability)
  apply Language.Definable.of_iff he
  intro v
  change v 0 = henkinNameTruthTable (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [henkinNameTruthTable, mem_sep_iff]

theorem henkinNameTruthTable_lookup {T s n φ b : V} :
    TableHolds (henkinNameTruthTable T s) n φ b ↔ HenkinNameHolds T s n φ b := by
  unfold TableHolds henkinNameTruthTable
  rw [mem_sep_iff]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · exact And.right
  · intro h
    refine ⟨mem_prod_iff.mpr ⟨⟨n, φ⟩ₖ, (mem_formulaSet_iff _ _ _ _).mp h.1,
      b, (mem_finiteSequences_iff _ _).mpr ⟨n, formulaSet_context membershipLanguageCode_valid h.1, h.2.1⟩,
      rfl⟩, h⟩

end ZFVP
