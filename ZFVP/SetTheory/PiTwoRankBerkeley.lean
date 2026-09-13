import ZFVP.SetTheory.PiOneInitialOrdinal
import ZFVP.SetTheory.RankBerkeley

/-! Pi-two dictionaries for the rank-Berkeley clause and its nonzero form.
Embedding witnesses are bounded by an explicitly named function space. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneSelfFunctionSpaceFormula : SetTheorySemisentence 2 :=
  “F A. ∀ f, f ∈ F ↔ !boundedFunctionFormula f A A”

theorem piOneSelfFunctionSpaceFormula_piOne : IsPiFormula 1 piOneSelfFunctionSpaceFormula :=
  .all (.and (.or (.bounded (.nrel _ _)) (.bounded (boundedFunctionFormula_bounded.subst _)))
    (.or (.bounded (boundedFunctionFormula_bounded.subst _).neg) (.bounded (.rel _ _))))

def piTwoProtoRankBerkeleyFormula : SetTheorySemisentence 2 :=
  “ζ δ. !piOneInitialOrdinalFormula δ ∧ ζ ∈ δ ∧ ∀ θ A F,
    !IsOrdinal.dfn θ → δ ∈ θ → !piOneHierarchyFormula A θ →
    !piOneSelfFunctionSpaceFormula F A → ∃ f ∈ F, ∃ κ ∈ δ,
      !piOneMembershipEmbeddingFormula A A f ∧ !boundedCriticalPointFormula A f κ ∧
      ζ ∈ κ ∧ !boundedPairMemberFormula f δ δ”

theorem piTwoProtoRankBerkeleyFormula_piTwo : IsPiFormula 2 piTwoProtoRankBerkeleyFormula := by
  unfold piTwoProtoRankBerkeleyFormula
  refine .and (piOneInitialOrdinalFormula_piOne.subst _).raise (.and (.bounded (.rel _ _)) ?_)
  repeat' apply IsLevyFormula.all
  refine .or (.bounded (isOrdinalFormula_bounded.subst _).neg) (.or (.bounded (.nrel _ _))
    (.or (piOneHierarchyFormula_piOne.subst _).neg.raise
      (.or (piOneSelfFunctionSpaceFormula_piOne.subst _).neg.raise ?_)))
  exact .boundedExs (.bvar 0) (.boundedExs (.bvar 5)
    (.and (piOneMembershipEmbeddingFormula_piOne.subst _).raise
      (.and (.bounded (boundedCriticalPointFormula_bounded.subst _))
        (.and (.bounded (.rel _ _)) (.bounded (boundedPairMemberFormula_bounded.subst _))))))

def piTwoRankBerkeleyClauseFormula : SetTheorySemisentence 1 :=
  “δ. !piOneInitialOrdinalFormula δ ∧ ∀ ζ ∈ δ, !piTwoProtoRankBerkeleyFormula ζ δ”

theorem piTwoRankBerkeleyClauseFormula_piTwo : IsPiFormula 2 piTwoRankBerkeleyClauseFormula :=
  .and (piOneInitialOrdinalFormula_piOne.subst _).raise
    (.boundedAll (.bvar 0) (piTwoProtoRankBerkeleyFormula_piTwo.subst _))

def piTwoNonzeroRankBerkeleyFormula : SetTheorySemisentence 1 :=
  “δ. (∃ x ∈ δ, ⊤) ∧ !piTwoRankBerkeleyClauseFormula δ”

theorem piTwoNonzeroRankBerkeleyFormula_piTwo : IsPiFormula 2 piTwoNonzeroRankBerkeleyFormula :=
  .and (.bounded (.exs (.bvar 0) .verum)) (piTwoRankBerkeleyClauseFormula_piTwo.subst _)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance piOneSelfFunctionSpaceFormula_defined :
    Defined (fun v : Fin 2 → V ↦ v 0 = v 1 ^ v 1) piOneSelfFunctionSpaceFormula :=
  ⟨fun v ↦ by simp [piOneSelfFunctionSpaceFormula, mem_ext_iff]⟩

theorem eval_piTwoProtoRankBerkeleyFormula (ζ δ : V) :
    piTwoProtoRankBerkeleyFormula.Evalb ![ζ, δ] ↔ IsProtoRankBerkeley ζ δ := by
  simp [piTwoProtoRankBerkeleyFormula, IsProtoRankBerkeley]
  intro hinit hζ
  constructor
  · intro h θ hθ hδθ
    let := hθ
    let := hierarchy_transitive θ
    obtain ⟨f, hf, κ, hκδ, he, hc, hζκ, hp⟩ :=
      h θ (hierarchy θ) (hierarchy θ ^ hierarchy θ) hθ hδθ ⟨hθ, rfl⟩ rfl
    let := IsFunction.of_mem hf
    exact ⟨f, he, κ, (criticalPoint_iff_graphSpec hf).mpr hc, hζκ, hκδ,
      value_eq_of_kpair_mem hp⟩
  · intro h θ A F hθ hδθ hA hF
    let := hθ
    let := hierarchy_transitive θ
    rcases hA with ⟨_, rfl⟩
    subst F
    obtain ⟨f, he, κ, hc, hζκ, hκδ, hfix⟩ := h θ hθ hδθ
    let := IsFunction.of_mem he.function
    refine ⟨f, he.function, κ, hκδ, he, (criticalPoint_iff_graphSpec he.function).mp hc, hζκ, ?_⟩
    apply kpair_mem_iff_value.mpr
    exact ⟨by
      rw [domain_eq_of_mem_function he.function]
      exact ordinal_subset_hierarchy θ δ hδθ, hfix⟩

instance piTwoProtoRankBerkeleyFormula_defined :
    ℒₛₑₜ-relation[V] IsProtoRankBerkeley via piTwoProtoRankBerkeleyFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    change piTwoProtoRankBerkeleyFormula.Evalb v ↔ IsProtoRankBerkeley (v 0) (v 1)
    rw [← hv]
    exact eval_piTwoProtoRankBerkeleyFormula _ _⟩

instance piTwoRankBerkeleyClauseFormula_defined :
    ℒₛₑₜ-predicate[V] RankBerkeleyClause via piTwoRankBerkeleyClauseFormula :=
  ⟨fun v ↦ by simp [piTwoRankBerkeleyClauseFormula, RankBerkeleyClause]⟩

instance piTwoNonzeroRankBerkeleyFormula_defined :
    ℒₛₑₜ-predicate[V] IsNonzeroRankBerkeley via piTwoNonzeroRankBerkeleyFormula :=
  ⟨fun v ↦ by
    simp [piTwoNonzeroRankBerkeleyFormula, IsNonzeroRankBerkeley]
    intro _
    exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.nonempty⟩⟩

theorem Cn.rankBerkeleyClause_absolute {n : ℕ} {θ : V} (hθ : Cn (n + 2) θ)
    (δ : SetDomain (hierarchy θ)) : piTwoRankBerkeleyClauseFormula.Evalb ![δ] ↔
      RankBerkeleyClause δ.val :=
  hθ.defined_correct (piTwoRankBerkeleyClauseFormula_piTwo.mono (by omega))
    (fun v ↦ RankBerkeleyClause (v 0)) ![δ]

theorem Cn.nonzeroRankBerkeley_absolute {n : ℕ} {θ : V} (hθ : Cn (n + 2) θ)
    (δ : SetDomain (hierarchy θ)) : piTwoNonzeroRankBerkeleyFormula.Evalb ![δ] ↔
      IsNonzeroRankBerkeley δ.val :=
  hθ.defined_correct (piTwoNonzeroRankBerkeleyFormula_piTwo.mono (by omega))
    (fun v ↦ IsNonzeroRankBerkeley (v 0)) ![δ]

end ZFVP
