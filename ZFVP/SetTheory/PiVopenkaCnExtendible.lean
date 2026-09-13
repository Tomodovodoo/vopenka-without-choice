import ZFVP.SetTheory.LeastGoodLimitPointClass
import ZFVP.SetTheory.ParamMarkerRankClass
import ZFVP.SetTheory.CriticalPointGoodClosure
import ZFVP.SetTheory.CnExtendibleSmallEmbedding
import ZFVP.ModelTheory.CriticalPointCardinal

/-! The converse of Bagaria's Theorem 4.12: the `Pi_{k+2}` fragment of Vopenka's principle gives
unboundedly many `C(k+1)`-extendible cardinals.

Fix an ordinal `α` and suppose no ordinal above `α` is `C(k+1)`-extendible. Then the good limit
points for `α` form an unbounded class of `C(k+2)` ordinals, and "`lam` is the least good limit
point for `α` above `r`" is a `Pi_{k+2}` condition that picks out one `lam` for each `r`. Feeding
the resulting proper class of rank-stage structures to the `Pi_{k+2}` fragment of Vopenka's
principle produces an elementary `f : V_lam → V_lam'` between two such stages with a critical
point `κ` above `α`.

That `κ` is then a good closure point, so it has a least failure stage `μ`, which lies below both
`lam` and `f ‘ κ`. Restricting `f` to `V_μ` witnesses `C(k+1)`-extendibility of `κ` at `μ`, which
is what the failure stage denies. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `leastGoodLimitPointFormula` with the conjunct saying that the predecessor of the base
ordinal `ρ` is an element of `lam`. Free variables: `lam`, `r`, `ρ`; it is used at `ρ = succ α`. -/
def leastGoodLimitAboveBaseFormula (k : ℕ) : SetTheorySemisentence 3 :=
  “lam r ρ. (∃ a ∈ ρ, !boundedSuccFormula ρ a ∧ a ∈ lam) ∧
    !(leastGoodLimitPointFormula k) lam r ρ”

theorem leastGoodLimitAboveBaseFormula_pi (k : ℕ) :
    IsPiFormula (k + 2) (leastGoodLimitAboveBaseFormula k) := by
  refine .and (.bounded (.exs (.bvar 2) ?_)) ((leastGoodLimitPointFormula_pi k).subst _)
  exact .and (boundedSuccFormula_bounded.subst _) (.rel _ _)

theorem eval_leastGoodLimitAboveBaseFormula_components {W : Type*} [SetStructure W]
    (k : ℕ) (lam r ρ : W) :
    (leastGoodLimitAboveBaseFormula k).Evalb ![lam, r, ρ] ↔
      (∃ a ∈ ρ, boundedSuccFormula.Evalb ![ρ, a] ∧ a ∈ lam) ∧
        (leastGoodLimitPointFormula k).Evalb ![lam, r, ρ] := by
  simp [leastGoodLimitAboveBaseFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_leastGoodLimitAboveBaseFormula {k : ℕ} {α lam r : V} [IsOrdinal α] :
    (leastGoodLimitAboveBaseFormula k).Evalb ![lam, r, succ α] ↔
      α ∈ lam ∧ (leastGoodLimitPointFormula k).Evalb ![lam, r, succ α] := by
  rw [eval_leastGoodLimitAboveBaseFormula_components]
  refine and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨a, ha, hsucc, halam⟩
    have : IsOrdinal a := IsOrdinal.of_mem ha
    have hs : succ α = succ a := by
      simpa using
        (Defined.eval_iff (R := fun v : Fin 2 → V ↦ v 0 = succ (v 1)) ![succ α, a]).mp hsucc
    rwa [succ_inj_ordinal hs]
  · intro hαlam
    refine ⟨α, mem_succ_self α, ?_, hαlam⟩
    show boundedSuccFormula.Evalb ![succ α, α]
    simp

/-! ### The least good limit point above an ordinal -/

/-- Under the failure hypothesis every ordinal `r` has a least good limit point above it. -/
theorem exists_least_goodLimitPoint_above {k : ℕ} {α : V} [IsOrdinal α]
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (r : V) [IsOrdinal r] :
    ∃ lam : V, IsOrdinal lam ∧ r ∈ lam ∧ IsGoodLimitPoint k α lam ∧
      ∀ ξ ∈ lam, r ∈ ξ → ¬ IsGoodLimitPoint k α ξ := by
  obtain ⟨lam₀, hr₀, hlam₀⟩ := exists_goodLimitPoint_above hno r
  have hdef : ℒₛₑₜ-predicate[V] (fun x ↦ r ∈ x ∧ IsGoodLimitPoint k α x) := by
    unfold IsGoodLimitPoint IsGoodClosurePoint IsFailureStage IsExtendibilityCandidate
    definability
  obtain ⟨lam, hlam, -⟩ :=
    leastOrdinal_existsUnique _ hdef ⟨lam₀, hlam₀.cn.ordinal, hr₀, hlam₀⟩
  obtain ⟨hord, ⟨hr, hg⟩, hmin⟩ := isLeastOrdinal_iff.mp hlam
  exact ⟨lam, hord, hr, hg, fun ξ hξ hrξ hgξ ↦ hmin ξ hξ ⟨hrξ, hgξ⟩⟩

/-- The class function fed to Vopenka's principle is total: for every ordinal `γ` there is a
`C(k+2)` stage `lam` above `γ` containing `succ α` and a marker `r`, with `lam` the least good
limit point above `r`. -/
theorem leastGoodLimitAboveBase_unbounded {k : ℕ} {α : V} [IsOrdinal α]
    (hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ) (γ : V) (hγ : IsOrdinal γ) :
    ∃ lam r : V, IsOrdinal lam ∧ γ ∈ lam ∧ succ α ⊆ lam ∧ (∀ ξ ∈ lam, succ ξ ∈ lam) ∧
      r ∈ lam ∧ (leastGoodLimitAboveBaseFormula k).Evalb ![lam, r, succ α] := by
  have : IsOrdinal γ := hγ
  have hrord : IsOrdinal (γ ∪ α) := ordinal_union_isOrdinal γ α
  set r : V := γ ∪ α with hrdef
  obtain ⟨lam, hlamord, hrlam, hglp, hleast⟩ := exists_least_goodLimitPoint_above hno r
  have : IsOrdinal lam := hlamord
  have hsub : ∀ x : V, IsOrdinal x → x ⊆ r → x ∈ lam := by
    intro x hx hxr
    have : IsOrdinal x := hx
    rcases IsOrdinal.subset_iff.mp hxr with he | hlt
    · exact he ▸ hrlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hrlam
  have hγlam : γ ∈ lam := hsub γ hγ (fun x hx ↦ mem_union_iff.mpr (Or.inl hx))
  have hαlam : α ∈ lam := hsub α inferInstance (fun x hx ↦ mem_union_iff.mpr (Or.inr hx))
  refine ⟨lam, r, hlamord, hγlam, ?_, hglp.cn.successor_closed, hrlam, ?_⟩
  · intro x hx
    rcases mem_succ_iff.mp hx with he | hlt
    · exact he ▸ hαlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hαlam
  · exact eval_leastGoodLimitAboveBaseFormula.mpr
      ⟨hαlam, leastGoodLimitPointFormula_complete hαlam hglp hrlam hleast⟩

/-! ### The main theorem -/

/-- The `Pi_{k+2}` fragment of Vopenka's principle gives unboundedly many `C(k+1)`-extendible
cardinals. Together with `cnExtendible_unbounded_implies_pi_vopenka` this is Bagaria's
Theorem 4.12 for `C(n)`-cardinals. -/
theorem pi_vopenka_implies_cnExtendible_unbounded (hAC : InternalChoice V) {k : ℕ}
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula (k + 2) φ → VopenkaInstance (V := V) φ) :
    ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible (k + 1) κ := by
  intro α₀ hα₀
  by_contra hcon
  have hno₀ : ∀ κ : V, α₀ ∈ κ → ¬ IsCnExtendible (k + 1) κ := by
    intro κ hκ hE
    exact hcon ⟨κ, hκ, hE⟩
  have : IsOrdinal α₀ := hα₀
  set α : V := α₀ ∪ (ω : V) with hαdef
  have hαord : IsOrdinal α := ordinal_union_isOrdinal α₀ (ω : V)
  have : IsOrdinal α := hαord
  have hα₀α : α₀ ⊆ α := fun x hx ↦ mem_union_iff.mpr (Or.inl hx)
  have hno : ∀ κ : V, α ∈ κ → ¬ IsCnExtendible (k + 1) κ := by
    intro κ hκ hE
    have : IsOrdinal κ := hE.1.1
    refine hno₀ κ ?_ hE
    rcases IsOrdinal.subset_iff.mp hα₀α with he | hlt
    · exact he ▸ hκ
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hκ
  -- run the embedding theorem on the least-good-limit-point class
  obtain ⟨lam, lam', r, r', f, κ, hlamord, hlam'ord, hrr', hρlam, hrlam, hψ,
      hρlam', hr'lam', hψ', hf, hfr, hfix, hκ, hρκ, hκr⟩ :=
    pi_vopenka_paramMarkerRank_embedding (V := V) (by omega) hVP
      (leastGoodLimitAboveBaseFormula k) (leastGoodLimitAboveBaseFormula_pi k) (succ α)
      (by
        intro lam₁ lam₂ r₀ h₁ h₂
        obtain ⟨hα₁, h₁'⟩ := eval_leastGoodLimitAboveBaseFormula.mp h₁
        obtain ⟨hα₂, h₂'⟩ := eval_leastGoodLimitAboveBaseFormula.mp h₂
        exact leastGoodLimitPointFormula_functional hα₁ hα₂ h₁' h₂')
      (fun γ hγ ↦ by
        obtain ⟨lam, r, h1, h2, h3, h4, h5, h6⟩ := leastGoodLimitAboveBase_unbounded hno γ hγ
        exact ⟨lam, r, h1, h2, h3, h4, h5, h6⟩)
  obtain ⟨hαlam, hψ0⟩ := eval_leastGoodLimitAboveBaseFormula.mp hψ
  obtain ⟨hαlam', hψ0'⟩ := eval_leastGoodLimitAboveBaseFormula.mp hψ'
  obtain ⟨hglp, -, -⟩ := leastGoodLimitPointFormula_sound hαlam hψ0
  obtain ⟨hglp', -, -⟩ := leastGoodLimitPointFormula_sound hαlam' hψ0'
  have : IsOrdinal lam := hlamord
  have : IsOrdinal lam' := hlam'ord
  have : IsTransitive (hierarchy lam) := hierarchy_transitive lam
  have hκord : IsOrdinal κ := hκ.ordinal
  have : IsOrdinal κ := hκord
  -- `α` and `κ`
  have hακ : α ∈ κ := hρκ α (mem_succ_self α)
  have hαH : α ∈ hierarchy lam := ordinal_subset_hierarchy lam α hαlam
  have hfα : f ‘ α = α :=
    hfix α (ordinal_subset_hierarchy (succ α) α (mem_succ_self α))
  have hrord : IsOrdinal r := IsOrdinal.of_mem hrlam
  have hκlam : κ ∈ lam := by
    rcases IsOrdinal.subset_iff.mp hκr with he | hlt
    · exact he ▸ hrlam
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hrlam
  have hκH : κ ∈ hierarchy lam := hκ.mem_domain
  -- `κ` is a good closure point and an extendibility candidate
  have hgood : IsGoodClosurePoint k α κ :=
    criticalPoint_isGoodClosurePoint hAC hno hglp hglp'.cn hf hκ hαlam hfα hακ hκlam
  have hinit : IsInitialOrdinal κ :=
    rankEmbedding_criticalPoint_initial hglp.cn hglp'.cn hf hκ
  have hcand : IsExtendibilityCandidate α κ := ⟨hinit, hακ⟩
  -- `f ‘ κ` is a good closure point above `κ`
  have hgood' : IsGoodClosurePoint k α (f ‘ κ) :=
    (goodClosurePoint_transfer hglp.cn hglp'.cn hf hαH hκH hfα).mp hgood
  have hfκord : IsOrdinal (f ‘ κ) :=
    rankEmbedding_value_ordinal hglp.cn hglp'.cn hf hκord hκH
  have hκfκ : κ ∈ f ‘ κ := by
    have hsub : κ ⊆ f ‘ κ := by
      intro x hx
      have hxH : x ∈ hierarchy lam := (hierarchy_transitive lam).mem_trans hx hκH
      have := (hf.value_mem_iff hxH hκH).mpr hx
      rwa [hκ.fixed_below hx] at this
    rcases IsOrdinal.subset_iff.mp hsub with he | hlt
    · exact absurd he.symm hκ.moved
    · exact hlt
  -- the least failure stage of `κ`
  set μ : V := minFailureStage k α κ with hμdef
  have hfail : IsFailureStage k α κ μ := minFailureStage_isFailureStage hno κ
  have hμcn : Cn (k + 1) μ := hfail.1
  have hκμ : κ ∈ μ := hfail.2.1
  have hnw : ¬ CnExtendibleWitness (k + 1) κ μ := by
    rcases hfail.2.2 with hbad | hgoodw
    · exact absurd hcand hbad
    · exact hgoodw
  have hμlam : μ ∈ lam := minFailureStage_mem_of_good hno hglp.good hκlam
  have hμfκ : μ ∈ f ‘ κ := minFailureStage_mem_of_good hno hgood' hκfκ
  -- restrict `f` to `V_μ` to build the witness the failure stage denies
  have hμord : IsOrdinal μ := hμcn.ordinal
  have : IsOrdinal μ := hμord
  have hμH : μ ∈ hierarchy lam := ordinal_subset_hierarchy lam μ hμlam
  have hVμ : hierarchy μ ∈ hierarchy lam := hglp.cn.hierarchy_closed hμord hμH
  have hVμne : IsNonempty (hierarchy μ) := ⟨ω, ordinal_subset_hierarchy μ _ hμcn.omega_lt⟩
  have hres := rankEmbedding_restrict hglp.cn hglp'.cn hf hVμ hVμne
  rw [(rankEmbedding_value_hierarchy hglp.cn hglp'.cn hf hμord hμH).2] at hres
  have hcnfμ : Cn (k + 1) (f ‘ μ) :=
    (rankEmbedding_cn_iff hglp.cn hglp'.cn hf hμH).mp hμcn
  have hκVμ : κ ∈ hierarchy μ := ordinal_subset_hierarchy μ κ hκμ
  have : IsTransitive (hierarchy μ) := hierarchy_transitive μ
  have hcr : IsCriticalPoint (hierarchy μ) (f ↾ (hierarchy μ)) κ :=
    hκ.restrict hf.function ((hierarchy_transitive lam).transitive _ hVμ) hκVμ
  have hval : (f ↾ (hierarchy μ)) ‘ κ = f ‘ κ := by
    have : IsFunction f := IsFunction.of_mem hf.function
    exact value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hκH) hκVμ
  have hμfμ : μ ∈ f ‘ μ := by
    have h1 : f ‘ κ ∈ f ‘ μ := (hf.value_mem_iff hκH hμH).mpr hκμ
    have : IsOrdinal (f ‘ μ) := rankEmbedding_value_ordinal hglp.cn hglp'.cn hf hμord hμH
    exact IsOrdinal.toIsTransitive.mem_trans hμfκ h1
  exact hnw ⟨hμord, f ‘ μ, f ↾ (hierarchy μ), hμfμ, hcnfμ, hres, hcr, by rw [hval]; exact hμfκ⟩

end ZFVP
