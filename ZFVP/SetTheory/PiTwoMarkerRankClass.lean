import ZFVP.SetTheory.PiOneRankMarkerClass
import ZFVP.SetTheory.VopenkaLevyClasses
import ZFVP.ModelTheory.DeltaOneIndexedMarkerStructures
import ZFVP.SetTheory.CorrectDomainReflection
import ZFVP.Syntax.BoundedStandardTuples

/-! Rank structures carrying two marked elements, and the embedding a Pi fragment of Vopenka's
principle produces between two of them. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piTwoMarkerRankBodyFormula (ψ : SetTheorySemisentence 2) : SetTheorySemisentence 5 :=
  “A C M ρ B. !sequenceSupportFormula A ∧
    ∃ lam ∈ A, ∃ r ∈ A, ∃ t ∈ A, ∃ N ∈ A,
      !IsOrdinal.dfn lam ∧ !isSubsetOf ρ lam ∧ r ∈ lam ∧ !ψ lam r ∧
      !(boundedNumeralFormula 2) N ∧ !(boundedStandardTupleFormula 2) A t lam r ∧
      !piOneOrdinalOmegaHierarchyFormula A lam ∧
      !piOneIndexedMarkerStructureFormula M B N A t”

def piTwoMarkerRankClassFormula (ψ : SetTheorySemisentence 2) : SetTheorySemisentence 3 :=
  boundedPairBind (.bvar 0) (piTwoMarkerRankBodyFormula ψ)

theorem piTwoMarkerRankBodyFormula_pi {k : ℕ} (hk : 0 < k) {ψ : SetTheorySemisentence 2}
    (hψ : IsPiFormula k ψ) : IsPiFormula k (piTwoMarkerRankBodyFormula ψ) := by
  refine .and (.bounded (sequenceSupportFormula_bounded.subst _)) ?_
  refine .boundedExs (.bvar 0) (.boundedExs (.bvar 1) (.boundedExs (.bvar 2)
    (.boundedExs (.bvar 3) ?_)))
  refine .and (.bounded (isOrdinalFormula_bounded.subst _)) ?_
  refine .and (.bounded (isSubsetOf_bounded.subst _)) ?_
  refine .and (.bounded (.rel _ _)) ?_
  refine .and (hψ.subst _) ?_
  refine .and (.bounded ((boundedNumeralFormula_bounded 2).subst _)) ?_
  refine .and (.bounded ((boundedStandardTupleFormula_bounded 2).subst _)) ?_
  exact .and ((piOneOrdinalOmegaHierarchyFormula_piOne.mono hk).subst _)
    ((piOneIndexedMarkerStructureFormula_piOne.mono hk).subst _)

theorem piTwoMarkerRankClassFormula_pi {k : ℕ} (hk : 0 < k) {ψ : SetTheorySemisentence 2}
    (hψ : IsPiFormula k ψ) : IsPiFormula k (piTwoMarkerRankClassFormula ψ) :=
  boundedPairBind_levy _ (piTwoMarkerRankBodyFormula_pi hk hψ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The membership structure on `V_{lam+ω}` with names for `V_ρ` and for the two markers
`lam` and `r`. -/
noncomputable def twoMarkerRankStructure (ρ lam r : V) : V :=
  indexedMarkerStructure (hierarchy ρ) (2 : V) (hierarchy (ordinalAdd lam ω))
    (standardTuple ![lam, r])

def IsTwoMarkerRankStructure (ψ : SetTheorySemisentence 2) (ρ M : V) : Prop :=
  ∃ lam r, IsOrdinal lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r] ∧
    M = twoMarkerRankStructure ρ lam r

@[simp] theorem twoMarkerRankStructure_domain (ρ lam r : V) :
    structureDomain (twoMarkerRankStructure ρ lam r) = hierarchy (ordinalAdd lam ω) :=
  indexedMarkerStructure_domain _ _ _ _

theorem twoMarkerRankStructure_marker_mem (lam : V) [IsOrdinal lam] :
    lam ∈ hierarchy (ordinalAdd lam ω) :=
  ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt lam)

theorem twoMarkerRankStructure_second_mem {lam r : V} [IsOrdinal lam] (hr : r ∈ lam) :
    r ∈ hierarchy (ordinalAdd lam ω) :=
  (hierarchy_transitive (ordinalAdd lam ω)).mem_trans hr (twoMarkerRankStructure_marker_mem lam)

theorem twoMarkerRankStructure_base_subset {ρ lam : V} [IsOrdinal ρ] [IsOrdinal lam]
    (hρ : ρ ⊆ lam) : hierarchy ρ ⊆ hierarchy (ordinalAdd lam ω) :=
  hierarchy_mono (subset_trans hρ (subset_ordinalAdd lam ω))

theorem twoMarkerRankStructure_tuple_mem_function {lam r : V} [IsOrdinal lam] (hr : r ∈ lam) :
    standardTuple ![lam, r] ∈ (hierarchy (ordinalAdd lam ω)) ^ ((2 : ℕ) : V) := by
  refine standardTuple_mem_function _ ?_
  intro i
  match i with
  | 0 => exact twoMarkerRankStructure_marker_mem lam
  | 1 => exact twoMarkerRankStructure_second_mem hr

theorem twoMarkerRankStructure_expansion {ρ lam r : V} [IsOrdinal ρ] [IsOrdinal lam]
    (hρ : ρ ⊆ lam) (hr : r ∈ lam) :
    IsMembershipExpansion (namedMembershipLanguageCode (markerIndexSet (hierarchy ρ) (2 : V)))
      (twoMarkerRankStructure ρ lam r) :=
  indexedMarkerStructure_expansion ⟨lam, twoMarkerRankStructure_marker_mem lam⟩
    (twoMarkerRankStructure_base_subset hρ)
    (by simpa using twoMarkerRankStructure_tuple_mem_function hr)

theorem twoMarkerRankStructure_sequenceSupport {ρ lam : V} [IsOrdinal ρ] [IsOrdinal lam]
    (hω : (ω : V) ∈ ρ) (hρ : ρ ⊆ lam) : IsSequenceSupport (hierarchy (ordinalAdd lam ω)) :=
  hierarchy_isSequenceSupport
    (IsOrdinal.toIsTransitive.mem_trans (hρ _ hω) (ordinalAdd_omega_gt lam))
    (fun _ ↦ ordinalAdd_omega_succ_closed lam)

theorem piTwoMarkerRankBodyFormula_support {ψ : SetTheorySemisentence 2} {A C M ρ B : V}
    (h : (piTwoMarkerRankBodyFormula ψ).Evalb ![A, C, M, ρ, B]) : IsSequenceSupport A := by
  have hs : sequenceSupportFormula.Evalb ![A] := h.1
  exact (Defined.eval_iff ![A]).mp hs

theorem eval_piTwoMarkerRankBodyFormula (ψ : SetTheorySemisentence 2) (A C M ρ B : V)
    [IsSequenceSupport A] :
    (piTwoMarkerRankBodyFormula ψ).Evalb ![A, C, M, ρ, B] ↔
      ∃ lam ∈ A, ∃ r ∈ A, IsOrdinal lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r] ∧
        A = hierarchy (ordinalAdd lam ω) ∧ B ⊆ A ∧
        M = indexedMarkerStructure B (2 : V) A (standardTuple ![lam, r]) := by
  simp [piTwoMarkerRankBodyFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    eval_boundedStandardTupleFormula, eval_piOneOrdinalOmegaHierarchyFormula,
    eval_piOneIndexedMarkerStructureFormula, show IsSequenceSupport A from inferInstance]
  constructor
  · rintro ⟨lam, hlam, r, hr, -, -, hord, hρ, hrl, hψ, -, ⟨-, hA⟩, hBA, -, hM⟩
    exact ⟨lam, hlam, r, hr, hord, hρ, hrl, hψ, hA, hBA, hM⟩
  · rintro ⟨lam, hlam, r, hr, hord, hρ, hrl, hψ, hA, hBA, hM⟩
    have hmem : ∀ i, (![lam, r] i) ∈ A := by
      intro i
      match i with
      | 0 => exact hlam
      | 1 => exact hr
    exact ⟨lam, hlam, r, hr, standardTuple_mem_support _ hmem, IsCodingSupport.numeral_mem 2,
      hord, hρ, hrl, hψ, ⟨hlam, hr⟩, ⟨hord, hA⟩, hBA, standardTuple_mem_function _ hmem, hM⟩

theorem eval_piTwoMarkerRankClassFormula (ψ : SetTheorySemisentence 2) (M ρ : V) [IsOrdinal ρ]
    (hω : (ω : V) ∈ ρ) :
    (piTwoMarkerRankClassFormula ψ).Evalb ![M, ρ, hierarchy ρ] ↔ IsTwoMarkerRankStructure ψ ρ M := by
  rw [piTwoMarkerRankClassFormula, eval_boundedPairBind]
  simp only [Semiterm.val_bvar, Matrix.cons_val_zero]
  constructor
  · rintro ⟨A, C, -, hbody⟩
    let := piTwoMarkerRankBodyFormula_support hbody
    obtain ⟨lam, -, r, -, hord, hρ, hrl, hψ, rfl, -, hM⟩ :=
      (eval_piTwoMarkerRankBodyFormula ψ A C M ρ (hierarchy ρ)).mp hbody
    exact ⟨lam, r, hord, hρ, hrl, hψ, hM⟩
  · rintro ⟨lam, r, hord, hρ, hrl, hψ, rfl⟩
    let := hord
    let := twoMarkerRankStructure_sequenceSupport hω hρ
    refine ⟨hierarchy (ordinalAdd lam ω), _, rfl, ?_⟩
    exact (eval_piTwoMarkerRankBodyFormula ψ _ _ _ ρ (hierarchy ρ)).mpr
      ⟨lam, twoMarkerRankStructure_marker_mem lam, r, twoMarkerRankStructure_second_mem hrl,
        hord, hρ, hrl, hψ, rfl, twoMarkerRankStructure_base_subset hρ, rfl⟩

theorem twoMarkerRankStructure_proper (ψ : SetTheorySemisentence 2) (ρ : V) [IsOrdinal ρ]
    (hub : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧
      ψ.Evalb ![lam, r]) :
    IsProperClass (IsTwoMarkerRankStructure ψ ρ) := by
  intro C
  obtain ⟨lam, r, hlam, hCl, hρ, hrl, hψ⟩ := hub (succ (rank C)) inferInstance
  let := hlam
  refine ⟨twoMarkerRankStructure ρ lam r, ⟨lam, r, hlam, hρ, hrl, hψ, rfl⟩, ?_⟩
  intro hm
  have hM := subset_hierarchy_rank C _ hm
  let := hierarchy_transitive (rank C)
  have hA : hierarchy (ordinalAdd lam ω) ∈ hierarchy (rank C) :=
    (kpair_components_mem_transitive hM).1
  have hlC : ordinalAdd lam ω ∈ rank C := by
    simpa only [rank_hierarchy] using (mem_hierarchy_iff_rank_mem _ _).mp hA
  have hCl' : rank C ∈ lam := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self _) hCl
  exact mem_asymm hlC (IsOrdinal.toIsTransitive.mem_trans hCl' (ordinalAdd_omega_gt lam))

theorem pi_vopenka_twoMarkerRank_embedding {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (ψ : SetTheorySemisentence 2) (hψ : IsPiFormula k ψ) (ρ : V) [IsOrdinal ρ]
    (hub : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧
      ψ.Evalb ![lam, r]) :
    ∃ lam lam' r r' f κ : V, IsOrdinal lam ∧ IsOrdinal lam' ∧ (lam ≠ lam' ∨ r ≠ r') ∧
      ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r] ∧ ρ ⊆ lam' ∧ r' ∈ lam' ∧ ψ.Evalb ![lam', r'] ∧
      IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam ω)) (hierarchy (ordinalAdd lam' ω)) f ∧
      f ‘ lam = lam' ∧ f ‘ r = r' ∧ (∀ x ∈ hierarchy ρ, f ‘ x = x) ∧
      IsCriticalPoint (hierarchy (ordinalAdd lam ω)) f κ ∧ ρ ⊆ κ ∧ κ ⊆ lam := by
  let b := ρ ∪ (ω : V)
  let : IsOrdinal b := ordinal_union_ordinal _ _
  let ρ₀ := succ b
  have hρρ₀ : ρ ⊆ ρ₀ := fun x hx ↦ mem_succ_iff.mpr (Or.inr (mem_union_iff.mpr (Or.inl hx)))
  have hωρ₀ : (ω : V) ∈ ρ₀ := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp
    (show (ω : V) ⊆ b from fun x hx ↦ mem_union_iff.mpr (Or.inr hx)))
  have hub₀ : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ₀ ⊆ lam ∧ r ∈ lam ∧
      ψ.Evalb ![lam, r] := by
    intro γ hγ
    let := hγ
    let s := γ ∪ ρ₀
    let : IsOrdinal s := ordinal_union_ordinal _ _
    obtain ⟨lam, r, hlam, hs, -, hrl, hψ'⟩ := hub (succ s) inferInstance
    let := hlam
    have hsl : s ∈ lam := IsOrdinal.toIsTransitive.mem_trans (mem_succ_self _) hs
    refine ⟨lam, r, hlam, ?_, ?_, hrl, hψ'⟩
    · exact IsOrdinal.toIsTransitive.mem_trans (mem_succ_iff.mpr (IsOrdinal.subset_iff.mp
        (show γ ⊆ s from fun x hx ↦ mem_union_iff.mpr (Or.inl hx)))) hs
    · exact subset_trans (show ρ₀ ⊆ s from fun x hx ↦ mem_union_iff.mpr (Or.inr hx))
        (IsOrdinal.toIsTransitive.transitive _ hsl)
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_levy_definable_class hk hVP
    (namedMembershipLanguageCode (markerIndexSet (hierarchy ρ₀) (2 : V)))
    (IsTwoMarkerRankStructure ψ ρ₀) (piTwoMarkerRankClassFormula ψ)
    (piTwoMarkerRankClassFormula_pi hk hψ) ![ρ₀, hierarchy ρ₀]
    (fun M ↦ eval_piTwoMarkerRankClassFormula ψ M ρ₀ hωρ₀)
    (twoMarkerRankStructure_proper ψ ρ₀ hub₀) (by
      rintro M ⟨lam, r, hlam, hρ, hrl, -, rfl⟩
      let := hlam
      exact (twoMarkerRankStructure_expansion hρ hrl).2.1)
  obtain ⟨lam, r, hlam, hρl, hrl, hψl, rfl⟩ := hM
  obtain ⟨lam', r', hlam', hρl', hrl', hψl', rfl⟩ := hN
  let := hlam
  let := hlam'
  let := hierarchy_transitive ρ₀
  let := hierarchy_transitive (ordinalAdd lam ω)
  have hv := hf.indexedMarker_values (twoMarkerRankStructure_base_subset hρl)
    (by simpa using twoMarkerRankStructure_tuple_mem_function hrl)
  have hmarks (i : Fin 2) : f ‘ (![lam, r] i) = ![lam', r'] i := by
    simpa only [value_standardTuple] using hv.1 (i.val : V) (natCast_mem_of_lt i.isLt)
  have hm0 : f ‘ lam = lam' := hmarks 0
  have hm1 : f ‘ r = r' := hmarks 1
  have hfix : ∀ x ∈ hierarchy ρ₀, f ‘ x = x := hv.2
  have hemb : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam ω))
      (hierarchy (ordinalAdd lam' ω)) f := by
    simpa only [twoMarkerRankStructure, indexedMarkerStructure_domain] using
      hf.membership_reduct (twoMarkerRankStructure_expansion hρl hrl)
        (twoMarkerRankStructure_expansion hρl' hrl')
  have hdiff : lam ≠ lam' ∨ r ≠ r' := by
    by_cases h : lam = lam'
    · exact Or.inr (fun he ↦ hne (by rw [h, he]))
    · exact Or.inl h
  obtain ⟨α, hαord, hαmem, hαmove, hαlam⟩ :
      ∃ α : V, IsOrdinal α ∧ α ∈ hierarchy (ordinalAdd lam ω) ∧ f ‘ α ≠ α ∧ α ⊆ lam := by
    rcases hdiff with h | h
    · exact ⟨lam, hlam, twoMarkerRankStructure_marker_mem lam,
        fun he ↦ h (he.symm.trans hm0), subset_refl lam⟩
    · exact ⟨r, IsOrdinal.of_mem hrl, twoMarkerRankStructure_second_mem hrl,
        fun he ↦ h (he.symm.trans hm1), IsOrdinal.toIsTransitive.transitive _ hrl⟩
  obtain ⟨κ, hκ, -⟩ := criticalPoint_exists_of_moved_ordinal hαord hαmem hαmove
  have hκlam : κ ⊆ lam := subset_trans (hκ.2.2 α hαord ⟨hαmem, hαmove⟩) hαlam
  have hρκ : ρ ⊆ κ := subset_trans hρρ₀ (hκ.fixed_rank_bound hfix)
  refine ⟨lam, lam', r, r', f, κ, hlam, hlam', hdiff, subset_trans hρρ₀ hρl, hrl, hψl,
    subset_trans hρρ₀ hρl', hrl', hψl', hemb, hm0, hm1, ?_, hκ, hρκ, hκlam⟩
  exact fun x hx ↦ hfix x (hierarchy_mono hρρ₀ x hx)

end ZFVP
