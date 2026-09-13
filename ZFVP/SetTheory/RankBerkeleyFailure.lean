import ZFVP.SetTheory.PiTwoRankBerkeley

/-! A Sigma-two formula for a rank at which the rank-Berkeley property fails. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedRankBerkeleyWitnessFormula : SetTheorySemisentence 4 :=
  “ζ δ A F. ∃ f ∈ F, ∃ κ ∈ δ, !piOneMembershipEmbeddingFormula A A f ∧
    !boundedCriticalPointFormula A f κ ∧ ζ ∈ κ ∧ !boundedPairMemberFormula f δ δ”

theorem boundedRankBerkeleyWitnessFormula_piOne : IsPiFormula 1 boundedRankBerkeleyWitnessFormula :=
  .boundedExs (.bvar 3) (.boundedExs (.bvar 2)
    (.and (piOneMembershipEmbeddingFormula_piOne.subst _)
      (.and (.bounded (boundedCriticalPointFormula_bounded.subst _))
        (.and (.bounded (.rel _ _)) (.bounded (boundedPairMemberFormula_bounded.subst _))))))

def rankBerkeleyFailureFormula : SetTheorySemisentence 2 :=
  “δ θ. !IsOrdinal.dfn θ ∧ δ ∈ θ ∧ ∃ A F,
    !piOneHierarchyFormula A θ ∧ !piOneSelfFunctionSpaceFormula F A ∧
      ∃ ζ ∈ δ, ¬!boundedRankBerkeleyWitnessFormula ζ δ A F”

theorem rankBerkeleyFailureFormula_sigmaTwo : IsSigmaFormula 2 rankBerkeleyFailureFormula := by
  unfold rankBerkeleyFailureFormula
  refine .and (.bounded (isOrdinalFormula_bounded.subst _)) (.and (.bounded (.rel _ _)) ?_)
  exact .exs (.exs (.and (piOneHierarchyFormula_piOne.subst _).raise
    (.and (piOneSelfFunctionSpaceFormula_piOne.subst _).raise
      (.boundedExs (.bvar 2) (boundedRankBerkeleyWitnessFormula_piOne.subst _).neg.raise))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def RankBerkeleyAt (δ θ : V) : Prop := ∀ ζ ∈ δ, ∃ f κ,
  IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f ∧
  IsCriticalPoint (hierarchy θ) f κ ∧ ζ ∈ κ ∧ κ ∈ δ ∧ f ‘ δ = δ

def RankBerkeleyFailure (δ θ : V) : Prop := IsOrdinal θ ∧ δ ∈ θ ∧ ¬RankBerkeleyAt δ θ

instance rankBerkeleyAt_definable : ℒₛₑₜ-relation[V] RankBerkeleyAt := by
  unfold RankBerkeleyAt
  definability

instance rankBerkeleyFailure_definable : ℒₛₑₜ-relation[V] RankBerkeleyFailure := by
  unfold RankBerkeleyFailure
  definability

theorem eval_boundedRankBerkeleyWitness {ζ δ θ : V} [IsOrdinal θ] (hδθ : δ ∈ θ) :
    boundedRankBerkeleyWitnessFormula.Evalb ![ζ, δ, hierarchy θ, hierarchy θ ^ hierarchy θ] ↔
      ∃ f κ, IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f ∧
        IsCriticalPoint (hierarchy θ) f κ ∧ ζ ∈ κ ∧ κ ∈ δ ∧ f ‘ δ = δ := by
  let := hierarchy_transitive θ
  simp [boundedRankBerkeleyWitnessFormula]
  constructor
  · rintro ⟨f, hf, κ, hκδ, he, hc, hζκ, hp⟩
    let := IsFunction.of_mem hf
    exact ⟨f, he, κ, (criticalPoint_iff_graphSpec hf).mpr hc, hζκ, hκδ, value_eq_of_kpair_mem hp⟩
  · rintro ⟨f, he, κ, hc, hζκ, hκδ, hfix⟩
    let := IsFunction.of_mem he.function
    refine ⟨f, he.function, κ, hκδ, he, (criticalPoint_iff_graphSpec he.function).mp hc, hζκ, ?_⟩
    apply kpair_mem_iff_value.mpr
    exact ⟨by
      rw [domain_eq_of_mem_function he.function]
      exact ordinal_subset_hierarchy θ δ hδθ, hfix⟩

theorem eval_rankBerkeleyFailureFormula (δ θ : V) :
    rankBerkeleyFailureFormula.Evalb ![δ, θ] ↔ RankBerkeleyFailure δ θ := by
  classical
  have he : rankBerkeleyFailureFormula.Evalb ![δ, θ] ↔
      IsOrdinal θ ∧ δ ∈ θ ∧ ∃ A F : V, (IsOrdinal θ ∧ A = hierarchy θ) ∧ F = A ^ A ∧
        ∃ ζ ∈ δ, ¬boundedRankBerkeleyWitnessFormula.Evalb ![ζ, δ, A, F] := by
    simp [rankBerkeleyFailureFormula, IsHierarchySegment, Semiformula.eval_substs,
      Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [he]
  constructor
  · rintro ⟨hθ, hδθ, A, F, ⟨_, rfl⟩, rfl, ζ, hζ, hn⟩
    let := hθ
    refine ⟨hθ, hδθ, ?_⟩
    intro hall
    exact hn (eval_boundedRankBerkeleyWitness hδθ |>.mpr (hall ζ hζ))
  · rintro ⟨hθ, hδθ, hn⟩
    let := hθ
    have hex : ∃ ζ ∈ δ, ¬∃ f κ, IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f ∧
        IsCriticalPoint (hierarchy θ) f κ ∧ ζ ∈ κ ∧ κ ∈ δ ∧ f ‘ δ = δ := by
      simpa only [RankBerkeleyAt, not_forall, not_imp, exists_prop] using hn
    obtain ⟨ζ, hζ, hno⟩ := hex
    exact ⟨hθ, hδθ, hierarchy θ, hierarchy θ ^ hierarchy θ, ⟨hθ, rfl⟩, rfl,
      ζ, hζ, fun h ↦ hno ((eval_boundedRankBerkeleyWitness hδθ).mp h)⟩

instance rankBerkeleyFailureFormula_defined :
    ℒₛₑₜ-relation[V] RankBerkeleyFailure via rankBerkeleyFailureFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change rankBerkeleyFailureFormula.Evalb v ↔ RankBerkeleyFailure (v 0) (v 1)
    rw [← hv]
    exact eval_rankBerkeleyFailureFormula _ _⟩

theorem rankBerkeleyClause_iff_no_failure (δ : V) :
    RankBerkeleyClause δ ↔ IsInitialOrdinal δ ∧ ∀ θ, ¬RankBerkeleyFailure δ θ := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rintro θ ⟨hθ, hδθ, hn⟩
    apply hn
    intro ζ hζ
    obtain ⟨f, κ, he, hc, hζκ, hκδ, hfix⟩ := (h.2 ζ hζ).2.2 θ hθ hδθ
    exact ⟨f, κ, he, hc, hζκ, hκδ, hfix⟩
  · rintro ⟨hinit, hn⟩
    refine ⟨hinit, ?_⟩
    intro ζ hζ
    refine ⟨hinit, hζ, ?_⟩
    intro θ hθ hδθ
    have hall : RankBerkeleyAt δ θ := by
      classical
      exact Classical.byContradiction (fun h ↦ hn θ ⟨hθ, hδθ, h⟩)
    exact hall ζ hζ

end ZFVP
