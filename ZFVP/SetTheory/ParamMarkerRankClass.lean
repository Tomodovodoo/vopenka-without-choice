import ZFVP.SetTheory.PiOneRankMarkerClass
import ZFVP.SetTheory.VopenkaLevyClasses

/-! Marker structures whose domain is a correct rank stage `V_lam`, with one marked ordinal
`r ∈ lam` and one set parameter `ρ`.

The two earlier marker classes put the structure on `V_{lam+ω}` so that `lam` itself is an element
of the domain and can be used as a marker. For the converse direction of Bagaria's Theorem 4.12 the
domain has to be the stage `V_lam` itself, so `lam` is not available as a marker; it is recovered
from the domain as its rank. The marker is then an ordinal `r ∈ lam`, and the side condition
`ψ lam r ρ` may mention the base ordinal `ρ`.

Saying "the domain is a correct stage" is done by a universal quantifier over the rank of the
domain and the negation of a Sigma-one graph, which keeps the whole class formula Pi at level `k`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Body of the class formula. Free variables: `A` (the domain), `C` (the second component of the
structure code, unused), `M`, `ρ`, `B`. -/
def paramMarkerRankBody (ψ : SetTheorySemisentence 3) : SetTheorySemisentence 5 :=
  “A C M ρ B. ∃ r ∈ A, !piOneMarkerStructureFormula M B A r ∧
    ∀ lam, !sigmaOneRankFormula lam A →
      (!piOneHierarchyFormula A lam ∧ !isSubsetOf ρ lam ∧
        (∀ ξ ∈ lam, ∃ s ∈ lam, !boundedSuccFormula s ξ) ∧ r ∈ lam ∧ !ψ lam r ρ)”

/-- The class formula. Free variables: `M`, `ρ`, `B`; it is used at `B = V_ρ`. -/
def paramMarkerRankClassFormula (ψ : SetTheorySemisentence 3) : SetTheorySemisentence 3 :=
  boundedPairBind (.bvar 0) (paramMarkerRankBody ψ)

theorem paramMarkerRankBody_pi {k : ℕ} (hk : 2 ≤ k) {ψ : SetTheorySemisentence 3}
    (hψ : IsPiFormula k ψ) : IsPiFormula k (paramMarkerRankBody ψ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine .boundedExs (.bvar 0)
    (.and ((piOneMarkerStructureFormula_piOne.subst _).mono (by omega)) ?_)
  refine .all (.or ((sigmaOneRankFormula_sigmaOne.subst _).neg.mono (by omega)) ?_)
  refine .and ((piOneHierarchyFormula_piOne.subst _).mono (by omega)) ?_
  refine .and (.bounded (isSubsetOf_bounded.subst _)) ?_
  refine .and (.boundedAll (.bvar 0) (.boundedExs (.bvar 1)
    (.bounded (boundedSuccFormula_bounded.subst _)))) ?_
  exact .and (.bounded (.rel _ _)) (hψ.subst _)

theorem paramMarkerRankClassFormula_pi {k : ℕ} (hk : 2 ≤ k) {ψ : SetTheorySemisentence 3}
    (hψ : IsPiFormula k ψ) : IsPiFormula k (paramMarkerRankClassFormula ψ) :=
  boundedPairBind_levy _ (paramMarkerRankBody_pi hk hψ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The membership structure on the stage `V_lam` with a name for `V_ρ` and a name for the
marker `r`. -/
noncomputable def paramMarkerRankStructure (ρ lam r : V) : V :=
  markerStructure (hierarchy ρ) (hierarchy lam) r

def IsParamMarkerRankStructure (ψ : SetTheorySemisentence 3) (ρ M : V) : Prop :=
  ∃ lam r, IsOrdinal lam ∧ ρ ⊆ lam ∧ (∀ ξ ∈ lam, succ ξ ∈ lam) ∧ r ∈ lam ∧
    ψ.Evalb ![lam, r, ρ] ∧ M = paramMarkerRankStructure ρ lam r

@[simp] theorem paramMarkerRankStructure_domain (ρ lam r : V) :
    structureDomain (paramMarkerRankStructure ρ lam r) = hierarchy lam :=
  markerStructure_domain _ _ _

theorem paramMarkerRankStructure_marker_mem {lam r : V} [IsOrdinal lam] (hr : r ∈ lam) :
    r ∈ hierarchy lam := ordinal_subset_hierarchy lam r hr

theorem paramMarkerRankStructure_base_subset {ρ lam : V} [IsOrdinal ρ] [IsOrdinal lam]
    (hρ : ρ ⊆ lam) : hierarchy ρ ⊆ hierarchy lam := hierarchy_mono hρ

theorem paramMarkerRankStructure_expansion {ρ lam r : V} [IsOrdinal ρ] [IsOrdinal lam]
    (hρ : ρ ⊆ lam) (hr : r ∈ lam) :
    IsMembershipExpansion (namedMembershipLanguageCode (succ (hierarchy ρ)))
      (paramMarkerRankStructure ρ lam r) :=
  markerStructure_expansion ⟨r, paramMarkerRankStructure_marker_mem hr⟩
    (paramMarkerRankStructure_base_subset hρ) (paramMarkerRankStructure_marker_mem hr)

theorem eval_paramMarkerRankBody (ψ : SetTheorySemisentence 3) (A C M ρ B : V) :
    (paramMarkerRankBody ψ).Evalb ![A, C, M, ρ, B] ↔
      ∃ r ∈ A, M = markerStructure B A r ∧
        ((IsOrdinal (rank A) ∧ A = hierarchy (rank A)) ∧ ρ ⊆ rank A ∧
          (∀ ξ ∈ rank A, succ ξ ∈ rank A) ∧ r ∈ rank A ∧ ψ.Evalb ![rank A, r, ρ]) := by
  simp [paramMarkerRankBody, eval_piOneMarkerStructureFormula, IsHierarchySegment]

theorem eval_paramMarkerRankClassFormula (ψ : SetTheorySemisentence 3) (M ρ : V) [IsOrdinal ρ] :
    (paramMarkerRankClassFormula ψ).Evalb ![M, ρ, hierarchy ρ] ↔
      IsParamMarkerRankStructure ψ ρ M := by
  rw [paramMarkerRankClassFormula, eval_boundedPairBind]
  simp only [Semiterm.val_bvar, Matrix.cons_val_zero, eval_paramMarkerRankBody]
  constructor
  · rintro ⟨A, C, -, r, hrA, hM, ⟨hord, hA⟩, hρ, hsucc, hrl, hψ⟩
    exact ⟨rank A, r, hord, hρ, hsucc, hrl, hψ, by rw [hM, paramMarkerRankStructure, ← hA]⟩
  · rintro ⟨lam, r, hord, hρ, hsucc, hrl, hψ, rfl⟩
    let := hord
    have hrk : rank (hierarchy lam) = lam := rank_hierarchy lam
    refine ⟨hierarchy lam, _, rfl, r, paramMarkerRankStructure_marker_mem hrl, rfl, ?_⟩
    rw [hrk]
    exact ⟨⟨hord, rfl⟩, hρ, hsucc, hrl, hψ⟩

theorem paramMarkerRankStructure_proper (ψ : SetTheorySemisentence 3) (ρ : V) [IsOrdinal ρ]
    (hub : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧
      (∀ ξ ∈ lam, succ ξ ∈ lam) ∧ r ∈ lam ∧ ψ.Evalb ![lam, r, ρ]) :
    IsProperClass (IsParamMarkerRankStructure ψ ρ) := by
  intro C
  obtain ⟨lam, r, hlam, hCl, hρ, hsucc, hrl, hψ⟩ := hub (rank C) inferInstance
  let := hlam
  refine ⟨paramMarkerRankStructure ρ lam r, ⟨lam, r, hlam, hρ, hsucc, hrl, hψ, rfl⟩, ?_⟩
  intro hm
  have hM := subset_hierarchy_rank C _ hm
  let := hierarchy_transitive (rank C)
  have hA : hierarchy lam ∈ hierarchy (rank C) := (kpair_components_mem_transitive hM).1
  have hlC : lam ∈ rank C := by
    simpa only [rank_hierarchy] using (mem_hierarchy_iff_rank_mem _ _).mp hA
  exact mem_asymm hlC hCl

theorem pi_vopenka_paramMarkerRank_embedding {k : ℕ} (hk : 2 ≤ k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (ψ : SetTheorySemisentence 3) (hψ : IsPiFormula k ψ) (ρ : V) [IsOrdinal ρ]
    (hfun : ∀ lam₁ lam₂ r₀ : V, ψ.Evalb ![lam₁, r₀, ρ] → ψ.Evalb ![lam₂, r₀, ρ] → lam₁ = lam₂)
    (hub : ∀ γ : V, IsOrdinal γ → ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ ρ ⊆ lam ∧
      (∀ ξ ∈ lam, succ ξ ∈ lam) ∧ r ∈ lam ∧ ψ.Evalb ![lam, r, ρ]) :
    ∃ lam lam' r r' f κ : V,
      IsOrdinal lam ∧ IsOrdinal lam' ∧ r ≠ r' ∧
      ρ ⊆ lam ∧ r ∈ lam ∧ ψ.Evalb ![lam, r, ρ] ∧
      ρ ⊆ lam' ∧ r' ∈ lam' ∧ ψ.Evalb ![lam', r', ρ] ∧
      IsCodedMembershipEmbedding (hierarchy lam) (hierarchy lam') f ∧
      f ‘ r = r' ∧ (∀ x ∈ hierarchy ρ, f ‘ x = x) ∧
      IsCriticalPoint (hierarchy lam) f κ ∧ ρ ⊆ κ ∧ κ ⊆ r := by
  have hk' : 0 < k := by omega
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_levy_definable_class hk' hVP
    (namedMembershipLanguageCode (succ (hierarchy ρ)))
    (IsParamMarkerRankStructure ψ ρ) (paramMarkerRankClassFormula ψ)
    (paramMarkerRankClassFormula_pi hk hψ) ![ρ, hierarchy ρ]
    (fun M ↦ eval_paramMarkerRankClassFormula ψ M ρ)
    (paramMarkerRankStructure_proper ψ ρ hub) (by
      rintro M ⟨lam, r, hlam, hρ, -, hrl, -, rfl⟩
      let := hlam
      exact (paramMarkerRankStructure_expansion hρ hrl).2.1)
  obtain ⟨lam, r, hlam, hρl, hsucc, hrl, hψl, rfl⟩ := hM
  obtain ⟨lam', r', hlam', hρl', hsucc', hrl', hψl', rfl⟩ := hN
  let := hlam
  let := hlam'
  let := hierarchy_transitive lam
  have hv := hf.marker_values (paramMarkerRankStructure_base_subset hρl)
    (paramMarkerRankStructure_marker_mem hrl)
  have hemb : IsCodedMembershipEmbedding (hierarchy lam) (hierarchy lam') f := by
    simpa only [paramMarkerRankStructure, markerStructure_domain] using
      hf.membership_reduct (paramMarkerRankStructure_expansion hρl hrl)
        (paramMarkerRankStructure_expansion hρl' hrl')
  have hrr : r ≠ r' := by
    intro he
    subst he
    exact hne (by rw [hfun lam lam' r hψl hψl'])
  have hmove : f ‘ r ≠ r := fun he ↦ hrr (he.symm.trans hv.1)
  obtain ⟨κ, hκ, -⟩ := criticalPoint_exists_of_moved_ordinal (IsOrdinal.of_mem hrl)
    (paramMarkerRankStructure_marker_mem hrl) hmove
  refine ⟨lam, lam', r, r', f, κ, hlam, hlam', hrr, hρl, hrl, hψl, hρl', hrl', hψl',
    hemb, hv.1, hv.2, hκ, hκ.fixed_rank_bound hv.2, ?_⟩
  exact hκ.2.2 r (IsOrdinal.of_mem hrl)
    ⟨paramMarkerRankStructure_marker_mem hrl, hmove⟩

end ZFVP
