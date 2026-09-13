import ZFVP.SetTheory.MagidorSupercompact
import ZFVP.SetTheory.BoundedHierarchyGraph
import ZFVP.ModelTheory.BoundedMembershipEmbedding
import ZFVP.ModelTheory.KunenSupportSelfEmbedding

/-! A bounded formula for Magidor's small-embedding predicate, and its transfer along a coded
embedding between rank stages.

`IsMagidorSupercompactAt κ γ` quantifies over the rank stages `V_lb` and `V_γ` and over an
embedding between them. Read literally the predicate is Sigma-one at best, and the Pi-one case of
Bagaria's Theorem 4.3 needs it under a negation, so a Sigma-one reading is of no use there.

Handing a rank stage `W` to the formula as a third argument makes every quantifier bounded. The
two stages are named by `boundedHierarchyGraphFormula`, the embedding by
`boundedMembershipEmbeddingFormula`, the critical point by `boundedCriticalPointFormula` and the
value `e ‘ ab = κ` by `boundedPairMemberFormula`. At `W = hierarchy ν` for a successor-closed `ν`
above `ω` that holds the membership formula family and has `γ` below it, the bounded reading says
exactly what the predicate says: the witnessing stages and the embedding all sit inside
`hierarchy ν`, because `lb ∈ κ ∈ γ ∈ ν` and the embedding is a set of Kuratowski pairs of members
of `hierarchy γ`, hence a member of `hierarchy (succ (succ (succ γ)))`.

A bounded formula transfers along any coded embedding between transitive sets, so the predicate
moves across a coded embedding of rank stages with the stage parameter `hierarchy ν` for any
`ν ∈ θ`, and the stages here are `V_{lam+omega}`, never in `C(1)`. No correctness hypothesis
appears anywhere below.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Magidor's small-embedding predicate with every quantifier bounded by a third argument `W`,
meant to be a rank stage holding the two witnessing stages and the embedding. -/
def boundedMagidorSupercompactAtFormula : SetTheorySemisentence 3 :=
  “k c W. ∃ lb ∈ k, ∃ ab ∈ lb, ∃ A ∈ W, ∃ B ∈ W, ∃ e ∈ W,
    !boundedHierarchyGraphFormula A lb W ∧ !boundedHierarchyGraphFormula B c W ∧
      !boundedMembershipEmbeddingFormula A B e W ∧
        !boundedCriticalPointFormula A e ab ∧ !boundedPairMemberFormula e ab k”

theorem boundedMagidorSupercompactAtFormula_bounded :
    IsBoundedSetFormula boundedMagidorSupercompactAtFormula :=
  .exs (.bvar 0) (.exs (.bvar 0) (.exs (.bvar 4) (.exs (.bvar 5) (.exs (.bvar 6)
    (.and (boundedHierarchyGraphFormula_bounded.subst _)
      (.and (boundedHierarchyGraphFormula_bounded.subst _)
        (.and (boundedMembershipEmbeddingFormula_bounded.subst _)
          (.and (boundedCriticalPointFormula_bounded.subst _)
            (boundedPairMemberFormula_bounded.subst _)))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The literal reading of `boundedMagidorSupercompactAtFormula`. -/
def BoundedMagidorSupercompactAt (κ γ W : V) : Prop :=
  ∃ lb ∈ κ, ∃ ab ∈ lb, ∃ A ∈ W, ∃ B ∈ W, ∃ e ∈ W,
    BoundedHierarchyGraph A lb W ∧ BoundedHierarchyGraph B γ W ∧
      BoundedMembershipEmbedding A B e W ∧ CriticalPointGraphSpec A e ab ∧ ⟨ab, κ⟩ₖ ∈ e

instance boundedMagidorSupercompactAtFormula_defined :
    ℒₛₑₜ-relation₃[V] BoundedMagidorSupercompactAt via boundedMagidorSupercompactAtFormula :=
  ⟨fun v ↦ by
    simp [boundedMagidorSupercompactAtFormula, BoundedMagidorSupercompactAt,
      (boundedHierarchyGraphFormula_defined (V := V)).iff,
      (boundedMembershipEmbeddingFormula_defined (V := V)).iff,
      (boundedCriticalPointFormula_defined (V := V)).iff,
      (boundedPairMemberFormula_defined (V := V)).iff]⟩

/-- An internal function from one rank stage to a higher one is a set of Kuratowski pairs of
members of the higher stage, so it lies three stages above it. -/
private theorem embedding_mem_hierarchy_three {γ lb e : V} [IsOrdinal γ] [IsOrdinal lb]
    (hlbγ : lb ∈ γ) (he : e ∈ (hierarchy γ) ^ (hierarchy lb)) :
    e ∈ hierarchy (succ (succ (succ γ))) := by
  rw [hierarchy_succ, mem_power_iff]
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function he p hp)
  exact kpair_mem_hierarchy_succ_succ
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hlbγ) x hx) hy

/-- At a successor-closed rank stage above `ω` that holds the membership formula family and has
`γ` below it, the bounded reading is exactly Magidor's predicate. -/
theorem boundedMagidorSupercompactAt_iff {ν κ γ : V} [IsOrdinal ν]
    (hω : (ω : V) ∈ ν) (hsucc : ∀ ξ ∈ ν, succ ξ ∈ ν)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν)
    (hκγ : κ ∈ γ) (hγν : γ ∈ ν) :
    BoundedMagidorSupercompactAt κ γ (hierarchy ν) ↔ IsMagidorSupercompactAt κ γ := by
  have hγord : IsOrdinal γ := IsOrdinal.of_mem hγν
  let := hγord
  have hκν : κ ∈ ν := IsOrdinal.toIsTransitive.mem_trans hκγ hγν
  have hBν : hierarchy γ ∈ hierarchy ν := hierarchy_mem hγν
  constructor
  · rintro ⟨lb, hlbκ, ab, hablb, A, hA, B, hB, e, he, hGA, hGB, hemb, hcrit, hpair⟩
    have hlbν : lb ∈ ν := IsOrdinal.toIsTransitive.mem_trans hlbκ hκν
    have hlbord : IsOrdinal lb := IsOrdinal.of_mem hlbν
    let := hlbord
    obtain ⟨-, rfl⟩ := (boundedHierarchyGraph_iff hsucc hlbν hA).mp hGA
    obtain ⟨-, rfl⟩ := (boundedHierarchyGraph_iff hsucc hγν hB).mp hGB
    have hemb' : IsCodedMembershipEmbedding (hierarchy lb) (hierarchy γ) e :=
      (boundedMembershipEmbedding_iff hω hsucc hF hA hB he).mp hemb
    let := hierarchy_transitive lb
    let := IsFunction.of_mem hemb'.function
    exact ⟨lb, hlbκ, ab, hablb, e, hemb',
      (criticalPoint_iff_graphSpec hemb'.function).mpr hcrit, value_eq_of_kpair_mem hpair⟩
  · rintro ⟨lb, hlbκ, ab, hablb, e, hemb, hcrit, hval⟩
    have hlbν : lb ∈ ν := IsOrdinal.toIsTransitive.mem_trans hlbκ hκν
    have hlbord : IsOrdinal lb := IsOrdinal.of_mem hlbν
    let := hlbord
    have hlbγ : lb ∈ γ := IsOrdinal.toIsTransitive.mem_trans hlbκ hκγ
    have hAν : hierarchy lb ∈ hierarchy ν := hierarchy_mem hlbν
    have h3 : succ (succ (succ γ)) ∈ ν := hsucc _ (hsucc _ (hsucc _ hγν))
    have heν : e ∈ hierarchy ν :=
      mem_hierarchy_of_mem_stage h3 (embedding_mem_hierarchy_three hlbγ hemb.function)
    let := hierarchy_transitive lb
    let := IsFunction.of_mem hemb.function
    refine ⟨lb, hlbκ, ab, hablb, hierarchy lb, hAν, hierarchy γ, hBν, e, heν,
      (boundedHierarchyGraph_iff hsucc hlbν hAν).mpr ⟨hlbord, rfl⟩,
      (boundedHierarchyGraph_iff hsucc hγν hBν).mpr ⟨hγord, rfl⟩,
      (boundedMembershipEmbedding_iff hω hsucc hF hAν hBν heν).mpr hemb,
      (criticalPoint_iff_graphSpec hemb.function).mp hcrit, ?_⟩
    have hdom : ab ∈ domain e := by
      rw [domain_eq_of_mem_function hemb.function]
      exact hcrit.mem_domain
    exact hval ▸ kpair_value_mem hdom

/-- The bounded formula, evaluated with a rank stage in the third slot, says exactly that `κ` is
Magidor supercompact at `γ`. -/
theorem eval_boundedMagidorSupercompactAtFormula {ν κ γ : V} [IsOrdinal ν]
    (hω : (ω : V) ∈ ν) (hsucc : ∀ ξ ∈ ν, succ ξ ∈ ν)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν)
    (hκγ : κ ∈ γ) (hγν : γ ∈ ν) :
    boundedMagidorSupercompactAtFormula.Evalb ![κ, γ, hierarchy ν] ↔
      IsMagidorSupercompactAt κ γ :=
  ((boundedMagidorSupercompactAtFormula_defined (V := V)).iff ![κ, γ, hierarchy ν]).trans
    (boundedMagidorSupercompactAt_iff hω hsucc hF hκγ hγν)

/-- Magidor's predicate transfers along a coded embedding between successor-closed rank stages.
The stage parameter is `hierarchy ν` for an auxiliary `ν ∈ θ`, so that all three arguments of the
bounded formula are members of the source stage. No correctness hypothesis is used. -/
theorem supportEmbedding_magidorSupercompactAt_iff {θ θ' ν f κ γ : V}
    [IsOrdinal θ] [IsOrdinal θ'] [IsOrdinal ν]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hω' : (ω : V) ∈ θ') (hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ')
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hων : (ω : V) ∈ ν) (hsuccν : ∀ ξ ∈ ν, succ ξ ∈ ν) (hνθ : ν ∈ θ)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν)
    (hκγ : κ ∈ γ) (hγν : γ ∈ ν) :
    IsMagidorSupercompactAt κ γ ↔ IsMagidorSupercompactAt (f ‘ κ) (f ‘ γ) := by
  have hγord : IsOrdinal γ := IsOrdinal.of_mem hγν
  let := hγord
  have hκν : κ ∈ ν := IsOrdinal.toIsTransitive.mem_trans hκγ hγν
  have hκord : IsOrdinal κ := IsOrdinal.of_mem hκν
  let := hκord
  let := hierarchy_transitive θ
  let := hierarchy_transitive θ'
  let := (hierarchy_isSequenceSupport hω hsucc).toIsCodingSupport
  let := (hierarchy_isSequenceSupport hων hsuccν).toIsCodingSupport
  -- the three arguments sit inside the source stage
  have hγθ : γ ∈ θ := IsOrdinal.toIsTransitive.mem_trans hγν hνθ
  have hκθ : κ ∈ θ := IsOrdinal.toIsTransitive.mem_trans hκν hνθ
  have hνH : ν ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hνθ
  have hγH : γ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hγθ
  have hκH : κ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hκθ
  have hWH : hierarchy ν ∈ hierarchy θ := hierarchy_mem hνθ
  have hωH : (ω : V) ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hω
  -- the image of the auxiliary stage
  have hvpair := supportEmbedding_value_hierarchy hω hsucc hω' hsucc' h inferInstance hνH
  have hvord : IsOrdinal (f ‘ ν) := hvpair.1
  let := hvord
  have hvW : f ‘ (hierarchy ν) = hierarchy (f ‘ ν) := hvpair.2
  -- the side conditions at the image stage
  have hων' : (ω : V) ∈ f ‘ ν := by
    have := (h.value_mem_iff hωH hνH).mpr hων
    rwa [h.value_omega hωH] at this
  have hsuccν' : ∀ ξ ∈ f ‘ ν, succ ξ ∈ f ‘ ν := by
    have h0 := (eval_boundedSuccessorClosedFormula ν).mpr hsuccν
    have he := (h.bounded_formula_iff boundedSuccessorClosedFormula_bounded ![ν]
      (by simp [hνH])).mp h0
    have hvec : (fun i ↦ f ‘ ((![ν] : Fin 1 → V) i)) = ![f ‘ ν] := by
      funext i
      exact Fin.cases rfl (fun t ↦ Fin.elim0 t) i
    rw [hvec] at he
    exact (eval_boundedSuccessorClosedFormula (f ‘ ν)).mp he
  have hFθ : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy θ :=
    (hierarchy_transitive θ).mem_trans hF hWH
  have hF' : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy (f ‘ ν) := by
    have hfix : f ‘ (formulaFamily membershipLanguageCode ∅ : V) =
        formulaFamily membershipLanguageCode ∅ :=
      h.value_membershipFamily_of_support hWH hF (identity_mem_hierarchy_limit hsuccν hF)
    have hm := (h.value_mem_iff hFθ hWH).mpr hF
    rwa [hfix, hvW] at hm
  have hκγ' : f ‘ κ ∈ f ‘ γ := (h.value_mem_iff hκH hγH).mpr hκγ
  have hγν' : f ‘ γ ∈ f ‘ ν := (h.value_mem_iff hγH hνH).mpr hγν
  -- the bounded formula crosses the embedding
  have hv : ∀ i, (![κ, γ, hierarchy ν] : Fin 3 → V) i ∈ hierarchy θ := by
    intro i
    refine Fin.cases hκH (fun j ↦ Fin.cases hγH (fun t ↦ Fin.cases ?_ (fun s ↦ Fin.elim0 s) t) j) i
    exact hWH
  have hiff := h.bounded_defined_iff boundedMagidorSupercompactAtFormula_bounded
    (fun v ↦ BoundedMagidorSupercompactAt (v 0) (v 1) (v 2)) ![κ, γ, hierarchy ν] hv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hiff
  rw [show (![κ, γ, hierarchy ν] : Fin 3 → V) 2 = hierarchy ν from rfl, hvW] at hiff
  exact (boundedMagidorSupercompactAt_iff hων hsuccν hF hκγ hγν).symm.trans
    (hiff.trans (boundedMagidorSupercompactAt_iff hων' hsuccν' hF' hκγ' hγν'))

/-- Members of an ordinal below the union with `ω` sit inside `α ∪ ω` plus `ω`. -/
private theorem mem_ordinalAdd_omega_of_subset {a b : V} [IsOrdinal a] [IsOrdinal b]
    (hab : a ⊆ b) : a ∈ ordinalAdd b (ω : V) := by
  rcases IsOrdinal.subset_iff.mp hab with rfl | hlt
  · exact ordinalAdd_omega_gt a
  · exact IsOrdinal.toIsTransitive.mem_trans hlt (ordinalAdd_omega_gt b)

/-- Magidor's predicate transfers along a coded embedding between the stages `V_{lam+omega}` and
`V_{lam'+omega}` that Bagaria's Theorem 4.3 hands to Vopenka's principle in the Pi-one case. The
auxiliary stage is `V_{(γ ∪ ω)+omega}`, which sits inside `V_{lam+omega}` because `lam` is a
successor-closed limit above `ω`. -/
theorem magidorSupercompactAt_value_iff {lam lam' f κ γ : V} [IsOrdinal lam] [IsOrdinal lam']
    (hωlam : (ω : V) ∈ lam) (hsucclam : ∀ ξ ∈ lam, succ ξ ∈ lam)
    (hωlam' : (ω : V) ∈ lam') (hsucclam' : ∀ ξ ∈ lam', succ ξ ∈ lam')
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈
      hierarchy (ordinalAdd (ω : V) (ω : V)))
    (h : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam (ω : V)))
      (hierarchy (ordinalAdd lam' (ω : V))) f)
    (hκγ : κ ∈ γ) (hγ : γ ∈ lam) :
    IsMagidorSupercompactAt κ γ ↔ IsMagidorSupercompactAt (f ‘ κ) (f ‘ γ) := by
  have hγord : IsOrdinal γ := IsOrdinal.of_mem hγ
  let := hγord
  -- the auxiliary stage `(γ ∪ ω) + ω`
  set δ : V := γ ∪ (ω : V) with hδdef
  have hδord : IsOrdinal δ := ordinal_union_ordinal γ (ω : V)
  let := hδord
  have hδlam : δ ∈ lam := union_mem_of_ordinals hγ hωlam
  set ν : V := ordinalAdd δ (ω : V) with hνdef
  have hδν : δ ∈ ν := ordinalAdd_omega_gt δ
  have hγδ : γ ⊆ δ := fun x hx ↦ mem_union_iff.mpr (Or.inl hx)
  have hωδ : (ω : V) ⊆ δ := fun x hx ↦ mem_union_iff.mpr (Or.inr hx)
  have hγν : γ ∈ ν := mem_ordinalAdd_omega_of_subset hγδ
  have hων : (ω : V) ∈ ν := mem_ordinalAdd_omega_of_subset hωδ
  have hsuccν : ∀ ξ ∈ ν, succ ξ ∈ ν := fun _ hξ ↦ ordinalAdd_omega_succ_closed δ hξ
  have hνlam : ν ⊆ lam := ordinalAdd_omega_subset_of_successor_closed hδlam hsucclam
  have hlamθ : lam ∈ ordinalAdd lam (ω : V) := ordinalAdd_omega_gt lam
  have hνθ : ν ∈ ordinalAdd lam (ω : V) := by
    rcases IsOrdinal.subset_iff.mp hνlam with he | hlt
    · exact he ▸ hlamθ
    · exact IsOrdinal.toIsTransitive.mem_trans hlt hlamθ
  -- the formula family sits inside the auxiliary stage
  have hFν : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy ν :=
    hierarchy_mono (ordinalAdd_omega_subset_of_successor_closed hων hsuccν) _ hF
  -- the two big stages are successor-closed and hold `ω`
  have hω : (ω : V) ∈ ordinalAdd lam (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam hlamθ
  have hsucc : ∀ ξ ∈ ordinalAdd lam (ω : V), succ ξ ∈ ordinalAdd lam (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam hξ
  have hω' : (ω : V) ∈ ordinalAdd lam' (ω : V) :=
    IsOrdinal.toIsTransitive.mem_trans hωlam' (ordinalAdd_omega_gt lam')
  have hsucc' : ∀ ξ ∈ ordinalAdd lam' (ω : V), succ ξ ∈ ordinalAdd lam' (ω : V) :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam' hξ
  exact supportEmbedding_magidorSupercompactAt_iff hω hsucc hω' hsucc' h hων hsuccν hνθ hFν
    hκγ hγν

end ZFVP
