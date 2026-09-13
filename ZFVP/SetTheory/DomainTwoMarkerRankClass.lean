import ZFVP.SetTheory.PiTwoMarkerRankClass

/-! The two-marker rank class of `ZFVP.SetTheory.ParamTwoMarkerRankClass`, with the domain
`V_{lam+ω}` also handed to the side condition.

The structures are the same `twoMarkerRankStructure ρ lam r`, so everything about them is reused
from `ZFVP.SetTheory.PiTwoMarkerRankClass`. The only change against the parameterized version is
that `ψ` takes a fourth argument and is evaluated at `![lam, r, ρ, V_{lam+ω}]`. This is what the
Pi_1 case of Bagaria's Theorem 4.3 needs: there the side condition is a bounded statement about
the domain itself.

A functionality hypothesis on `ψ` (the marker `r` determines `lam`) turns the distinctness
supplied by Vopenka's principle into `r ≠ r'`, which bounds the critical point by `r`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Body of the class formula. Free variables: `A` (the domain), `C` (the second component of the
structure code, unused), `M`, `ρ`, `B`. The side condition `ψ` is evaluated at the two markers,
the base and the domain `A`. -/
def domainTwoMarkerRankBodyFormula (ψ : SetTheorySemisentence 4) : SetTheorySemisentence 5 :=
  “A C M ρ B. !sequenceSupportFormula A ∧
    ∃ lam ∈ A, ∃ r ∈ A, ∃ t ∈ A, ∃ N ∈ A,
      !IsOrdinal.dfn lam ∧ !isSubsetOf ρ lam ∧ r ∈ lam ∧ !ψ lam r ρ A ∧
      !(boundedNumeralFormula 2) N ∧ !(boundedStandardTupleFormula 2) A t lam r ∧
      !piOneOrdinalOmegaHierarchyFormula A lam ∧
      !piOneIndexedMarkerStructureFormula M B N A t”

/-- The class formula. Free variables: `M`, `ρ`, `B`; it is used at `B = V_ρ`. -/
def domainTwoMarkerRankClassFormula (ψ : SetTheorySemisentence 4) : SetTheorySemisentence 3 :=
  boundedPairBind (.bvar 0) (domainTwoMarkerRankBodyFormula ψ)

theorem domainTwoMarkerRankBodyFormula_pi {k : ℕ} (hk : 0 < k) {ψ : SetTheorySemisentence 4}
    (hψ : IsPiFormula k ψ) : IsPiFormula k (domainTwoMarkerRankBodyFormula ψ) := by
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

theorem domainTwoMarkerRankClassFormula_pi {k : ℕ} (hk : 0 < k) {ψ : SetTheorySemisentence 4}
    (hψ : IsPiFormula k ψ) : IsPiFormula k (domainTwoMarkerRankClassFormula ψ) :=
  boundedPairBind_levy _ (domainTwoMarkerRankBodyFormula_pi hk hψ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The structures picked out by the class: two-marker rank structures over the base `ρ` whose
markers satisfy the side condition `ψ lam r ρ V_{lam+ω}`. -/
def IsDomainTwoMarkerRankStructure (ψ : SetTheorySemisentence 4) (ρ M : V) : Prop :=
  ∃ lam r, IsOrdinal lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧
    ψ.Evalb ![lam, r, ρ, hierarchy (ordinalAdd lam ω)] ∧ M = twoMarkerRankStructure ρ lam r

theorem domainTwoMarkerRankBodyFormula_support {ψ : SetTheorySemisentence 4} {A C M ρ B : V}
    (h : (domainTwoMarkerRankBodyFormula ψ).Evalb ![A, C, M, ρ, B]) : IsSequenceSupport A := by
  have hs : sequenceSupportFormula.Evalb ![A] := h.1
  exact (Defined.eval_iff ![A]).mp hs

theorem eval_domainTwoMarkerRankBodyFormula (ψ : SetTheorySemisentence 4) (A C M ρ B : V)
    [IsSequenceSupport A] :
    (domainTwoMarkerRankBodyFormula ψ).Evalb ![A, C, M, ρ, B] ↔
      ∃ lam ∈ A, ∃ r ∈ A, IsOrdinal lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r, ρ, A] ∧
        A = hierarchy (ordinalAdd lam ω) ∧ B ⊆ A ∧
        M = indexedMarkerStructure B (2 : V) A (standardTuple ![lam, r]) := by
  simp [domainTwoMarkerRankBodyFormula, Semiformula.eval_substs,
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

theorem eval_domainTwoMarkerRankClassFormula (ψ : SetTheorySemisentence 4) (M ρ : V) [IsOrdinal ρ]
    (hω : (ω : V) ∈ ρ) :
    (domainTwoMarkerRankClassFormula ψ).Evalb ![M, ρ, hierarchy ρ] ↔
      IsDomainTwoMarkerRankStructure ψ ρ M := by
  rw [domainTwoMarkerRankClassFormula, eval_boundedPairBind]
  simp only [Semiterm.val_bvar, Matrix.cons_val_zero]
  constructor
  · rintro ⟨A, C, -, hbody⟩
    let := domainTwoMarkerRankBodyFormula_support hbody
    obtain ⟨lam, -, r, -, hord, hρ, hrl, hψ, rfl, -, hM⟩ :=
      (eval_domainTwoMarkerRankBodyFormula ψ A C M ρ (hierarchy ρ)).mp hbody
    exact ⟨lam, r, hord, hρ, hrl, hψ, hM⟩
  · rintro ⟨lam, r, hord, hρ, hrl, hψ, rfl⟩
    let := hord
    let := twoMarkerRankStructure_sequenceSupport hω hρ
    refine ⟨hierarchy (ordinalAdd lam ω), _, rfl, ?_⟩
    exact (eval_domainTwoMarkerRankBodyFormula ψ _ _ _ ρ (hierarchy ρ)).mpr
      ⟨lam, twoMarkerRankStructure_marker_mem lam, r, twoMarkerRankStructure_second_mem hrl,
        hord, hρ, hrl, hψ, rfl, twoMarkerRankStructure_base_subset hρ, rfl⟩

theorem domainTwoMarkerRankStructure_proper (ψ : SetTheorySemisentence 4) (ρ : V) [IsOrdinal ρ]
    (hub : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧
      ψ.Evalb ![lam, r, ρ, hierarchy (ordinalAdd lam ω)]) :
    IsProperClass (IsDomainTwoMarkerRankStructure ψ ρ) := by
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

theorem pi_vopenka_domainTwoMarkerRank_embedding {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (ψ : SetTheorySemisentence 4) (hψ : IsPiFormula k ψ) (ρ : V) [IsOrdinal ρ]
    (hω : (ω : V) ∈ ρ)
    (hfun : ∀ lam₁ lam₂ r₀ : V, ψ.Evalb ![lam₁, r₀, ρ, hierarchy (ordinalAdd lam₁ ω)] →
      ψ.Evalb ![lam₂, r₀, ρ, hierarchy (ordinalAdd lam₂ ω)] → lam₁ = lam₂)
    (hub : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧ r ∈ lam ∧
      ψ.Evalb ![lam, r, ρ, hierarchy (ordinalAdd lam ω)]) :
    ∃ lam lam' r r' f κ : V, IsOrdinal lam ∧ IsOrdinal lam' ∧ r ≠ r' ∧
      ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r, ρ, hierarchy (ordinalAdd lam ω)] ∧
      ρ ⊆ lam' ∧ r' ∈ lam' ∧ ψ.Evalb ![lam', r', ρ, hierarchy (ordinalAdd lam' ω)] ∧
      IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam ω)) (hierarchy (ordinalAdd lam' ω)) f ∧
      f ‘ lam = lam' ∧ f ‘ r = r' ∧ (∀ x ∈ hierarchy ρ, f ‘ x = x) ∧
      IsCriticalPoint (hierarchy (ordinalAdd lam ω)) f κ ∧ ρ ⊆ κ ∧ κ ⊆ r := by
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_levy_definable_class hk hVP
    (namedMembershipLanguageCode (markerIndexSet (hierarchy ρ) (2 : V)))
    (IsDomainTwoMarkerRankStructure ψ ρ) (domainTwoMarkerRankClassFormula ψ)
    (domainTwoMarkerRankClassFormula_pi hk hψ) ![ρ, hierarchy ρ]
    (fun M ↦ eval_domainTwoMarkerRankClassFormula ψ M ρ hω)
    (domainTwoMarkerRankStructure_proper ψ ρ hub) (by
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
  have hrr : r ≠ r' := by
    intro he
    subst he
    exact hne (by rw [hfun lam lam' r hψl hψl'])
  have hmove : f ‘ r ≠ r := fun he ↦ hrr (he.symm.trans hm1)
  obtain ⟨κ, hκ, -⟩ := criticalPoint_exists_of_moved_ordinal (IsOrdinal.of_mem hrl)
    (twoMarkerRankStructure_second_mem hrl) hmove
  refine ⟨lam, lam', r, r', f, κ, hlam, hlam', hrr, hρl, hrl, hψl, hρl', hrl', hψl',
    hemb, hm0, hm1, hfix, hκ, hκ.fixed_rank_bound hfix, ?_⟩
  exact hκ.2.2 r (IsOrdinal.of_mem hrl) ⟨twoMarkerRankStructure_second_mem hrl, hmove⟩

end ZFVP
