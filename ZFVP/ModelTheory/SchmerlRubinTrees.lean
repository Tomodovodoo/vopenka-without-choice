import ZFVP.ModelTheory.RatherClasslessOfRubin
import ZFVP.ModelTheory.RubinDefinableFilters
import ZFVP.ModelTheory.SchmerlInfinitaryClassConstruction
import ZFVP.ModelTheory.SchmerlSelectedDomains

/-! Bridges from the corrected Rubin model produced by Stage 1 to the actual
ranked trees and branch bounds used by the specialization construction. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory Set Order

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The raw cofinal-chain assertion supplies every field of a finite-domain tree. -/
theorem exists_finiteDomainChain_of_cofinal_chain {s : V}
    (h : HasCofinalOmegaOneChain (fun d ↦ d ∈ finiteSubsets s)) :
    Nonempty (FiniteDomainChain s (Ordinal.ToType (Ordinal.omega.{0} 1))) := by
  obtain ⟨d, hd, hmono, hcof⟩ := h
  have hm {i j} (hij : i ≤ j) : d i ⊆ d j := by
    rcases hij.eq_or_lt with rfl | hij
    · exact SetTheory.subset_refl _
    · exact (hmono i j hij).1
  have hinj : Function.Injective d := by
    intro i j he
    rcases lt_trichotomy i j with hij | hij | hji
    · exact ((hmono i j hij).2 he).elim
    · exact hij
    · exact ((hmono j i hji).2 he.symm).elim
  exact ⟨{
    domain := d
    finite := fun i ↦ ((mem_finiteSubsets_iff s (d i)).mp (hd i)).2
    subset := fun i ↦ ((mem_finiteSubsets_iff s (d i)).mp (hd i)).1
    monotone := fun {_ _} hij ↦ hm hij
    injective := hinj
    cofinal := fun a hsub hfin ↦ hcof a ((mem_finiteSubsets_iff s a).mpr ⟨hsub, hfin⟩) }⟩

theorem exists_finiteDomainChain_of_rubin (h : IsRubinDefinable V)
    {s : V} (hs : IsInternallyInfinite s) :
    Nonempty (FiniteDomainChain s (Ordinal.ToType (Ordinal.omega.{0} 1))) :=
  exists_finiteDomainChain_of_cofinal_chain (h.hasCofinalOmegaOneChain_finiteSubsets s hs)

/-- The Rubin cofinal-ordinal chain is an actual order embedding. -/
theorem exists_cofinal_ordinal_embedding_of_rubin (h : IsRubinDefinable V) :
    ∃ c : Ordinal.ToType (Ordinal.omega.{0} 1) ↪o SetTheory.Ordinal V, IsCofinal (Set.range c) := by
  obtain ⟨a, ha, hmono, hcof⟩ := h.1 (IsOrdinal (V := V)) (· ⊆ ·)
    inferInstance subset_definable (isPartialOrderOn_subset _) isDirectedNoMaxOn_isOrdinal
  let f : Ordinal.ToType (Ordinal.omega.{0} 1) → SetTheory.Ordinal V := fun i ↦ ⟨a i, ha i⟩
  have hf : StrictMono f := by
    intro i j hij
    apply lt_of_le_of_ne
    · exact (hmono i j hij).1
    · intro he
      exact (hmono i j hij).2 (congrArg SetTheory.Ordinal.val he)
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro b
  obtain ⟨i, hi⟩ := hcof b.val b.ordinal
  exact ⟨f i, Set.mem_range_self i, hi⟩

theorem ordinal_cofinality_of_rubin (h : IsRubinDefinable V) :
    Order.cof (SetTheory.Ordinal V) = Cardinal.aleph 1 := by
  obtain ⟨c, hc⟩ := exists_cofinal_ordinal_embedding_of_rubin h
  rw [← Order.cof_congr_of_strictMono c.strictMono hc,
    Ordinal.cof_toType, Cardinal.cof_omega_one]

theorem ratherClassless_of_rubin (h : IsRubinDefinable V) :
    ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X :=
  ratherClassless_of_rubin_clauses h.1 h.2

/-- Every branch of the actual function tree generates a filter to which the
Rubin coding theorem applies. The selected domain chain need not be definable. -/
theorem functionTree_filters_coded_of_rubin (h : IsRubinDefinable V) {s : V}
    (C : FiniteDomainChain s (Ordinal.ToType (Ordinal.omega.{0} 1)))
    {B : Set (FunctionTreeNode C)} (hB : (FunctionTreeNode.rankedTree (C := C)).IsBranch B) :
    ∃ m : V, ∀ p : V, p ∈ m ↔ filterOfBranch C B p := by
  let : Nonempty (Ordinal.ToType (Ordinal.omega.{0} 1)) :=
    Ordinal.nonempty_toType_iff.mpr (Ordinal.omega_pos 1).ne'
  have hfilter := filterOfBranch_isFilter C hB
  have hmax : IsMaximalInternalFilter (finitePartialFunctions s ((2 : ℕ) : V))
      (filterOfBranch C B) := by
    refine ⟨⟨hfilter.1, hfilter.2.2.1⟩, ?_⟩
    intro F hF hBF
    exact filterOfBranch_maximal C hB F hF.1 hF.2 hBF
  exact h.isCoded_maximalFilter s _ hmax (filterOfBranch_has_cofinal_chain C hB)

/-- The branch-cardinality premise of the corrected specializing forcing now
follows from the Rubin property and the size of the model. -/
theorem functionTree_branch_bound_of_rubin (h : IsRubinDefinable V)
    (hcard : Cardinal.mk V ≤ Cardinal.aleph 1) {s : V}
    (C : FiniteDomainChain s (Ordinal.ToType (Ordinal.omega.{0} 1))) :
    Cardinal.mk {B : Set (FunctionTreeNode C) //
      (FunctionTreeNode.rankedTree (C := C)).IsBranch B} ≤ Cardinal.aleph 1 :=
  functionTree_branch_bound C (fun B hB ↦
    (filterOfBranch_definable_iff_coded C B).mpr (functionTree_filters_coded_of_rubin h C hB)) hcard

theorem classTree_branch_bound_of_rubin (h : IsRubinDefinable V)
    (hcard : Cardinal.mk V ≤ Cardinal.aleph 1) :
    Cardinal.mk {B : Set (ClassTreeNode V) //
      (ClassTreeNode.rankedTree (V := V)).IsBranch B} ≤ Cardinal.aleph 1 :=
  classTree_branch_bound (ratherClassless_of_rubin h) hcard

end ZFVP.Schmerl

