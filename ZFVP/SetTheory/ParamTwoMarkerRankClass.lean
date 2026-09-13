import ZFVP.SetTheory.PiTwoMarkerRankClass

/-! The two-marker rank class of `ZFVP.SetTheory.PiTwoMarkerRankClass`, with the base parameter
`ρ` made visible to the side condition.

The structures are the same `twoMarkerRankStructure ρ lam r` on `V_{lam+ω}`, so everything about
them is reused from that module. The only change is the side condition: `ψ` now takes three
arguments and is evaluated at `![lam, r, ρ]`. Because `ψ` sees `ρ`, the base cannot be enlarged
inside the proof the way `pi_vopenka_twoMarkerRank_embedding` enlarges it, so the hypothesis
`(ω : V) ∈ ρ` is assumed instead and the class is built at the given `ρ`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Body of the class formula. Free variables: `A` (the domain), `C` (the second component of the
structure code, unused), `M`, `ρ`, `B`. -/
def paramTwoMarkerRankBodyFormula (ψ : SetTheorySemisentence 3) : SetTheorySemisentence 5 :=
  “A C M ρ B. !sequenceSupportFormula A ∧
    ∃ lam ∈ A, ∃ r ∈ A, ∃ t ∈ A, ∃ N ∈ A,
      !IsOrdinal.dfn lam ∧ !isSubsetOf ρ lam ∧ r ∈ lam ∧ !ψ lam r ρ ∧
      !(boundedNumeralFormula 2) N ∧ !(boundedStandardTupleFormula 2) A t lam r ∧
      !piOneOrdinalOmegaHierarchyFormula A lam ∧
      !piOneIndexedMarkerStructureFormula M B N A t”

/-- The class formula. Free variables: `M`, `ρ`, `B`; it is used at `B = V_ρ`. -/
def paramTwoMarkerRankClassFormula (ψ : SetTheorySemisentence 3) : SetTheorySemisentence 3 :=
  boundedPairBind (.bvar 0) (paramTwoMarkerRankBodyFormula ψ)

theorem paramTwoMarkerRankBodyFormula_pi {k : ℕ} (hk : 0 < k) {ψ : SetTheorySemisentence 3}
    (hψ : IsPiFormula k ψ) : IsPiFormula k (paramTwoMarkerRankBodyFormula ψ) := by
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

theorem paramTwoMarkerRankClassFormula_pi {k : ℕ} (hk : 0 < k) {ψ : SetTheorySemisentence 3}
    (hψ : IsPiFormula k ψ) : IsPiFormula k (paramTwoMarkerRankClassFormula ψ) :=
  boundedPairBind_levy _ (paramTwoMarkerRankBodyFormula_pi hk hψ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The structures picked out by the class: two-marker rank structures over the base `ρ` whose
markers satisfy the parameterized side condition `ψ lam r ρ`. -/
def IsParamTwoMarkerRankStructure (ψ : SetTheorySemisentence 3) (ρ M : V) : Prop :=
  ∃ lam r, IsOrdinal lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r, ρ] ∧
    M = twoMarkerRankStructure ρ lam r

theorem paramTwoMarkerRankBodyFormula_support {ψ : SetTheorySemisentence 3} {A C M ρ B : V}
    (h : (paramTwoMarkerRankBodyFormula ψ).Evalb ![A, C, M, ρ, B]) : IsSequenceSupport A := by
  have hs : sequenceSupportFormula.Evalb ![A] := h.1
  exact (Defined.eval_iff ![A]).mp hs

theorem eval_paramTwoMarkerRankBodyFormula (ψ : SetTheorySemisentence 3) (A C M ρ B : V)
    [IsSequenceSupport A] :
    (paramTwoMarkerRankBodyFormula ψ).Evalb ![A, C, M, ρ, B] ↔
      ∃ lam ∈ A, ∃ r ∈ A, IsOrdinal lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r, ρ] ∧
        A = hierarchy (ordinalAdd lam ω) ∧ B ⊆ A ∧
        M = indexedMarkerStructure B (2 : V) A (standardTuple ![lam, r]) := by
  simp [paramTwoMarkerRankBodyFormula, Semiformula.eval_substs,
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

theorem eval_paramTwoMarkerRankClassFormula (ψ : SetTheorySemisentence 3) (M ρ : V) [IsOrdinal ρ]
    (hω : (ω : V) ∈ ρ) :
    (paramTwoMarkerRankClassFormula ψ).Evalb ![M, ρ, hierarchy ρ] ↔
      IsParamTwoMarkerRankStructure ψ ρ M := by
  rw [paramTwoMarkerRankClassFormula, eval_boundedPairBind]
  simp only [Semiterm.val_bvar, Matrix.cons_val_zero]
  constructor
  · rintro ⟨A, C, -, hbody⟩
    let := paramTwoMarkerRankBodyFormula_support hbody
    obtain ⟨lam, -, r, -, hord, hρ, hrl, hψ, rfl, -, hM⟩ :=
      (eval_paramTwoMarkerRankBodyFormula ψ A C M ρ (hierarchy ρ)).mp hbody
    exact ⟨lam, r, hord, hρ, hrl, hψ, hM⟩
  · rintro ⟨lam, r, hord, hρ, hrl, hψ, rfl⟩
    let := hord
    let := twoMarkerRankStructure_sequenceSupport hω hρ
    refine ⟨hierarchy (ordinalAdd lam ω), _, rfl, ?_⟩
    exact (eval_paramTwoMarkerRankBodyFormula ψ _ _ _ ρ (hierarchy ρ)).mpr
      ⟨lam, twoMarkerRankStructure_marker_mem lam, r, twoMarkerRankStructure_second_mem hrl,
        hord, hρ, hrl, hψ, rfl, twoMarkerRankStructure_base_subset hρ, rfl⟩

theorem paramTwoMarkerRankStructure_proper (ψ : SetTheorySemisentence 3) (ρ : V) [IsOrdinal ρ]
    (hub : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧
      ψ.Evalb ![lam, r, ρ]) :
    IsProperClass (IsParamTwoMarkerRankStructure ψ ρ) := by
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

theorem pi_vopenka_paramTwoMarkerRank_embedding {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (ψ : SetTheorySemisentence 3) (hψ : IsPiFormula k ψ) (ρ : V) [IsOrdinal ρ]
    (hω : (ω : V) ∈ ρ)
    (hub : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧
      ψ.Evalb ![lam, r, ρ]) :
    ∃ lam lam' r r' f κ : V, IsOrdinal lam ∧ IsOrdinal lam' ∧ (lam ≠ lam' ∨ r ≠ r') ∧
      ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r, ρ] ∧
      ρ ⊆ lam' ∧ r' ∈ lam' ∧ ψ.Evalb ![lam', r', ρ] ∧
      IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam ω)) (hierarchy (ordinalAdd lam' ω)) f ∧
      f ‘ lam = lam' ∧ f ‘ r = r' ∧ (∀ x ∈ hierarchy ρ, f ‘ x = x) ∧
      IsCriticalPoint (hierarchy (ordinalAdd lam ω)) f κ ∧ ρ ⊆ κ ∧ κ ⊆ lam := by
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_levy_definable_class hk hVP
    (namedMembershipLanguageCode (markerIndexSet (hierarchy ρ) (2 : V)))
    (IsParamTwoMarkerRankStructure ψ ρ) (paramTwoMarkerRankClassFormula ψ)
    (paramTwoMarkerRankClassFormula_pi hk hψ) ![ρ, hierarchy ρ]
    (fun M ↦ eval_paramTwoMarkerRankClassFormula ψ M ρ hω)
    (paramTwoMarkerRankStructure_proper ψ ρ hub) (by
      rintro M ⟨lam, r, hlam, hρ, hrl, -, rfl⟩
      let := hlam
      exact (twoMarkerRankStructure_expansion hρ hrl).2.1)
  obtain ⟨lam, r, hlam, hρl, hrl, hψl, rfl⟩ := hM
  obtain ⟨lam', r', hlam', hρl', hrl', hψl', rfl⟩ := hN
  let := hlam
  let := hlam'
  let := hierarchy_transitive ρ
  let := hierarchy_transitive (ordinalAdd lam ω)
  have hv := hf.indexedMarker_values (twoMarkerRankStructure_base_subset hρl)
    (by simpa using twoMarkerRankStructure_tuple_mem_function hrl)
  have hmarks (i : Fin 2) : f ‘ (![lam, r] i) = ![lam', r'] i := by
    simpa only [value_standardTuple] using hv.1 (i.val : V) (natCast_mem_of_lt i.isLt)
  have hm0 : f ‘ lam = lam' := hmarks 0
  have hm1 : f ‘ r = r' := hmarks 1
  have hfix : ∀ x ∈ hierarchy ρ, f ‘ x = x := hv.2
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
  have hρκ : ρ ⊆ κ := hκ.fixed_rank_bound hfix
  exact ⟨lam, lam', r, r', f, κ, hlam, hlam', hdiff, hρl, hrl, hψl, hρl', hrl', hψl', hemb,
    hm0, hm1, hfix, hκ, hρκ, hκlam⟩

end ZFVP
