import ZFVP.SetTheory.RankBerkeleyFailure
import ZFVP.ModelTheory.CriticalPoint

/-! The least failing rank lies in a C(2) source and is fixed when
the proposed rank-Berkeley cardinal is fixed. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankBerkeleyFailureExistsFormula : SetTheorySemisentence 1 :=
  “δ. ∃ θ, !rankBerkeleyFailureFormula δ θ”

theorem rankBerkeleyFailureExistsFormula_sigmaTwo : IsSigmaFormula 2 rankBerkeleyFailureExistsFormula :=
  .exs (rankBerkeleyFailureFormula_sigmaTwo.subst _)

def leastRankBerkeleyFailureFormula : SetTheorySemisentence 2 :=
  “δ σ. !rankBerkeleyFailureFormula δ σ ∧ ∀ τ ∈ σ, ¬!rankBerkeleyFailureFormula δ τ”

theorem eval_rankBerkeleyFailureExists_components {W : Type*} [SetStructure W] (δ : W) :
    rankBerkeleyFailureExistsFormula.Evalb ![δ] ↔ ∃ θ : W, rankBerkeleyFailureFormula.Evalb ![δ, θ] := by
  simp [rankBerkeleyFailureExistsFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

theorem eval_leastRankBerkeleyFailure_components {W : Type*} [SetStructure W] (δ σ : W) :
    leastRankBerkeleyFailureFormula.Evalb ![δ, σ] ↔
      rankBerkeleyFailureFormula.Evalb ![δ, σ] ∧
        ∀ τ ∈ σ, ¬rankBerkeleyFailureFormula.Evalb ![δ, τ] := by
  simp [leastRankBerkeleyFailureFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance rankBerkeleyFailureExistsFormula_defined :
    Defined (fun v : Fin 1 → V ↦ ∃ θ, RankBerkeleyFailure (v 0) θ) rankBerkeleyFailureExistsFormula :=
  ⟨fun v ↦ by simp [rankBerkeleyFailureExistsFormula]⟩

theorem Cn.rankBerkeleyFailure_absolute {n : ℕ} {θ : V} (hθ : Cn (n + 2) θ)
    (δ σ : SetDomain (hierarchy θ)) : rankBerkeleyFailureFormula.Evalb ![δ, σ] ↔
      RankBerkeleyFailure δ.val σ.val :=
  hθ.defined_correct (rankBerkeleyFailureFormula_sigmaTwo.mono (by omega))
    (fun v ↦ RankBerkeleyFailure (v 0) (v 1)) ![δ, σ]

theorem Cn.leastRankBerkeleyFailure_absolute {n : ℕ} {θ : V} (hθ : Cn (n + 2) θ)
    (δ σ : SetDomain (hierarchy θ)) : leastRankBerkeleyFailureFormula.Evalb ![δ, σ] ↔
      IsLeastOrdinal (RankBerkeleyFailure δ.val) σ.val := by
  let := hθ.ordinal
  let := hierarchy_transitive θ
  rw [eval_leastRankBerkeleyFailure_components, hθ.rankBerkeleyFailure_absolute δ σ]
  constructor
  · rintro ⟨hbad, hmin⟩
    let := hbad.1
    refine ⟨hbad.1, hbad, ?_⟩
    intro τ hτ hτbad
    let := hτ
    rcases IsOrdinal.mem_trichotomy σ.val τ with hl | he | hg
    · exact IsOrdinal.toIsTransitive.transitive _ hl
    · exact subset_of_eq he
    · let t : SetDomain (hierarchy θ) := ⟨τ, (hierarchy_transitive θ).mem_trans hg σ.property⟩
      exact False.elim (hmin t hg ((hθ.rankBerkeleyFailure_absolute δ t).mpr hτbad))
  · intro hmin
    refine ⟨hmin.2.1, ?_⟩
    intro τ hτσ hτ
    have hbad := (hθ.rankBerkeleyFailure_absolute δ τ).mp hτ
    have hle := hmin.2.2 τ.val hbad.1 hbad
    exact mem_irrefl τ.val (hle τ.val hτσ)

theorem Cn.leastRankBerkeleyFailure_exists {n : ℕ} {θ δ : V} (hθ : Cn (n + 2) θ)
    (hδ : δ ∈ hierarchy θ) (hex : ∃ σ, RankBerkeleyFailure δ σ) :
    ∃ σ, σ ∈ θ ∧ IsLeastOrdinal (RankBerkeleyFailure δ) σ := by
  let := hθ.ordinal
  let d : SetDomain (hierarchy θ) := ⟨δ, hδ⟩
  have hs := (hθ.defined_correct (rankBerkeleyFailureExistsFormula_sigmaTwo.mono (by omega))
    (fun v ↦ ∃ σ, RankBerkeleyFailure (v 0) σ) ![d]).mpr hex
  obtain ⟨s, hsbad⟩ := (eval_rankBerkeleyFailureExists_components d).mp hs
  have hs' := (hθ.rankBerkeleyFailure_absolute d s).mp hsbad
  let := hs'.1
  have hsθ := ordinal_mem_hierarchy_iff.mp s.property
  obtain ⟨σ, hmin, _⟩ := leastOrdinal_existsUnique (RankBerkeleyFailure δ)
    (by definability) ⟨s.val, hs'.1, hs'⟩
  let := hmin.1
  exact ⟨σ, ordinal_mem_of_subset_mem (hmin.2.2 s.val hs'.1 hs') hsθ, hmin⟩

theorem rankEmbedding_leastRankBerkeleyFailure_fixed {n : ℕ} {θ f δ σ : V}
    (hθ : Cn (n + 2) θ) (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f)
    (hmin : IsLeastOrdinal (RankBerkeleyFailure δ) σ) (hσθ : σ ∈ θ)
    (hfixδ : f ‘ δ = δ) : f ‘ σ = σ := by
  let := hθ.ordinal
  let := hmin.1
  let := hierarchy_transitive θ
  have hσV := ordinal_subset_hierarchy θ σ hσθ
  have hδV := (hierarchy_transitive θ).mem_trans hmin.2.1.2.1 hσV
  let d : SetDomain (hierarchy θ) := ⟨δ, hδV⟩
  let s : SetDomain (hierarchy θ) := ⟨σ, hσV⟩
  have hs := (hθ.leastRankBerkeleyFailure_absolute d s).mpr hmin
  have ht := (hf.eval_semisentence leastRankBerkeleyFailureFormula ![d, s]).mp hs
  have hv : hf.toFunction ∘ ![d, s] = ![d, hf.toFunction s] := by
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    exact Subtype.ext hfixδ
  rw [hv] at ht
  have hm := (hθ.leastRankBerkeleyFailure_absolute d (hf.toFunction s)).mp ht
  exact subset_antisymm (hm.2.2 σ hmin.1 hmin.2.1) (hmin.2.2 _ hm.1 hm.2.1)

end ZFVP
