import ZFVP.ModelTheory.LimitRankRestriction
import ZFVP.ModelTheory.EmbeddingAssignments

/-! Rank stages closed under successor act like correct stages for the hierarchy formula,
and coded embeddings between them restrict to smaller stages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem hierarchy_mem_hierarchy_of_support {θ α : V} [IsOrdinal θ] [IsOrdinal α]
    (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ) (hαθ : α ∈ hierarchy θ) : hierarchy α ∈ hierarchy θ :=
  hierarchy_mem (by simpa only [mem_hierarchy_iff_rank_mem, rank_of_ordinal] using hαθ)

theorem hierarchy_formula_correct_of_support {θ : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ) (A α : SetDomain (hierarchy θ)) :
    piOneHierarchyFormula.Evalb ![A, α] ↔ IsOrdinal α.val ∧ A.val = hierarchy α.val :=
  piOneHierarchyFormula_absolute_limit hsucc A α

theorem supportEmbedding_value_hierarchy {θ θ' f α : V} [IsOrdinal θ] [IsOrdinal θ']
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hω' : (ω : V) ∈ θ') (hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ')
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hα : IsOrdinal α) (hαθ : α ∈ hierarchy θ) :
    IsOrdinal (f ‘ α) ∧ f ‘ (hierarchy α) = hierarchy (f ‘ α) :=
  limitRankEmbedding_value_hierarchy hsucc hsucc' h hα hαθ

theorem supportEmbedding_value_ordinal {θ θ' f α : V} [IsOrdinal θ] [IsOrdinal θ']
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hω' : (ω : V) ∈ θ') (hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ')
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hα : IsOrdinal α) (hαθ : α ∈ hierarchy θ) : IsOrdinal (f ‘ α) :=
  (supportEmbedding_value_hierarchy hω hsucc hω' hsucc' h hα hαθ).1

theorem identity_mem_hierarchy_limit {κ X : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hX : X ∈ hierarchy κ) :
    SetTheory.identity X ∈ hierarchy κ := by
  apply subset_mem_hierarchy_limit hκ (prod_mem_hierarchy_limit hκ hX hX)
  intro p hp
  exact (mem_sep_iff.mp hp).1

/-- Satisfaction over a set inside a successor closed stage is preserved by a coded embedding,
provided the stage contains a sequence support that holds the set and the membership formula
family. The support bounds every quantifier of the truth table equations. -/
theorem supportEmbedding_setSatisfaction {θ B f a U n φ b : V} [IsOrdinal θ] [IsTransitive B]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (h : IsCodedMembershipEmbedding (hierarchy θ) B f)
    (hUs : IsSequenceSupport U) (hU : U ∈ hierarchy θ) (haU : a ∈ U)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ U)
    (hiF : SetTheory.identity (formulaFamily membershipLanguageCode ∅ : V) ∈ U)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ a ^ n) :
    MembershipSatisfies a n φ b ↔ MembershipSatisfies (f ‘ a) n φ (compose b f) := by
  let := hierarchy_isSequenceSupport hω hsucc
  let := hUs
  have hωA : (ω : V) ∈ hierarchy θ := ordinal_subset_hierarchy θ _ hω
  have hasub : a ⊆ U := hUs.transitive a haU
  have ha : a ∈ hierarchy θ := (hierarchy_transitive θ).mem_trans haU hU
  have hFA : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy θ :=
    (hierarchy_transitive θ).mem_trans hF hU
  set T := membershipModelTruthTable a with hTdef
  have ht : IsMembershipTruthTable a T := membershipModelTruthTable_correct a
  have hTA : T ∈ hierarchy θ :=
    membershipModelTruthTable_mem_hierarchy_limit hsucc hωA ha hFA
  let := h.value_sequenceSupport hU hUs
  have hfa : f ‘ a ∈ f ‘ U := (h.value_mem_iff ha hU).mpr haU
  have hfasub : f ‘ a ⊆ f ‘ U := IsTransitive.transitive _ hfa
  have hFfix : f ‘ (formulaFamily membershipLanguageCode ∅ : V) =
      formulaFamily membershipLanguageCode ∅ :=
    h.value_membershipFamily_of_support hU hF hiF
  -- the image of the truth table is a truth table for the image of `a`
  have hs := (eval_membershipTruthTableFormula hasub T).mpr ht
  have he := (h.bounded_formula_iff membershipTruthTableFormula_bounded
    ![U, ω, formulaFamily membershipLanguageCode ∅, a, T]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hU, hωA, hFA, ha, hTA])).mp hs
  have hv : (fun i ↦ f ‘ (![U, ω, formulaFamily membershipLanguageCode ∅, a, T] i)) =
      ![f ‘ U, f ‘ (ω : V), f ‘ (formulaFamily membershipLanguageCode ∅ : V), f ‘ a, f ‘ T] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) m) l) k) j) i
  rw [hv, h.value_omega hωA, hFfix] at he
  have ht' := (eval_membershipTruthTableFormula hfasub (f ‘ T)).mp he
  -- transfer the table lookup
  have hnA : n ∈ hierarchy θ := IsCodingSupport.natural_mem hφ.context
  have hφA : φ ∈ hierarchy θ := membershipFormulaCode_formula_mem_support hφ
  have hbU : b ∈ U := function_mem_sequenceSupport hasub hφ.context hb
  have hbA : b ∈ hierarchy θ := (hierarchy_transitive θ).mem_trans hbU hU
  have hbt : b ∈ hierarchy θ ^ n :=
    mem_function_of_mem_function_of_subset hb (IsTransitive.transitive a ha)
  have hfb : f ‘ b ∈ (f ‘ a) ^ n := by
    simpa only [h.value_natural hφ.context] using h.value_function hbA hnA ha hb
  have he2 := h.bounded_formula_iff (boundedTableAnswerFormula_bounded true) ![U, T, n, φ, b]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hU, hTA, hnA, hφA, hbA])
  have hv2 : (fun i ↦ f ‘ (![U, T, n, φ, b] i)) = ![f ‘ U, f ‘ T, f ‘ n, f ‘ φ, f ‘ b] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) m) l) k) j) i
  rw [hv2, h.value_natural hφ.context, h.value_formulaCode hφ] at he2
  rw [eval_truthTableAnswer ht hφ hb, eval_truthTableAnswer ht' hφ hfb,
    h.value_assignment hφ.context hbA hbt] at he2
  exact he2

/-- Restriction of a coded embedding to a set inside the source stage. The stage must contain a
sequence support holding the set and the membership formula family. -/
theorem supportEmbedding_restrict {θ θ' f a U : V} [IsOrdinal θ] [IsOrdinal θ']
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hω' : (ω : V) ∈ θ') (hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ')
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hUs : IsSequenceSupport U) (hU : U ∈ hierarchy θ) (haU : a ∈ U)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ U)
    (hiF : SetTheory.identity (formulaFamily membershipLanguageCode ∅ : V) ∈ U)
    (hne : IsNonempty a) :
    IsCodedMembershipEmbedding a (f ‘ a) (f ↾ a) := by
  let := hierarchy_isSequenceSupport hω hsucc
  let := hierarchy_transitive θ'
  have ha : a ∈ hierarchy θ := (hierarchy_transitive θ).mem_trans haU hU
  have himage : IsNonempty (f ‘ a) := by
    obtain ⟨x, hx⟩ := hne.nonempty
    exact ⟨⟨f ‘ x, (h.value_mem_iff
      ((hierarchy_transitive θ).mem_trans hx ha) ha).mpr hx⟩⟩
  refine ⟨membershipStructureCode_valid hne, membershipStructureCode_valid himage,
    by simpa using h.restriction_function ha, ?_⟩
  intro n hn φ hφ b hb
  have hb' : b ∈ a ^ n := by simpa using hb
  have he := supportEmbedding_setSatisfaction hω hsucc h hUs hU haU hF hiF
    ((mem_formulaSet_iff _ _ _ _).mp hφ) hb'
  rw [← graph_compose_restrict hb' f] at he
  exact he

/-- Restriction to a rank stage `hierarchy α` below the source stage. The sequence support is
taken to be a smaller stage `hierarchy γ` that already holds the membership formula family. -/
theorem supportEmbedding_restrict_hierarchy {θ θ' f α γ : V} [IsOrdinal θ] [IsOrdinal θ']
    [IsOrdinal γ] (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hω' : (ω : V) ∈ θ') (hsucc' : ∀ ξ ∈ θ', succ ξ ∈ θ')
    (h : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ') f)
    (hωγ : (ω : V) ∈ γ) (hsuccγ : ∀ ξ ∈ γ, succ ξ ∈ γ) (hγθ : γ ∈ θ)
    (hFγ : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy γ)
    (hα : IsOrdinal α) (hαne : IsNonempty α) (hαγ : α ∈ γ) :
    IsCodedMembershipEmbedding (hierarchy α) (hierarchy (f ‘ α)) (f ↾ (hierarchy α)) := by
  let := hα
  have hne : IsNonempty (hierarchy α) :=
    ⟨∅, ordinal_subset_hierarchy α _ (IsOrdinal.empty_mem_iff_nonempty.mpr hαne)⟩
  have hr := supportEmbedding_restrict hω hsucc hω' hsucc' h
    (hierarchy_isSequenceSupport hωγ hsuccγ)
    (hierarchy_mem_hierarchy_of_support hsucc (ordinal_subset_hierarchy θ _ hγθ))
    (hierarchy_mem hαγ) hFγ (identity_mem_hierarchy_limit hsuccγ hFγ) hne
  rwa [(supportEmbedding_value_hierarchy hω hsucc hω' hsucc' h hα
    (ordinal_subset_hierarchy θ _ (IsOrdinal.toIsTransitive.mem_trans hαγ hγθ))).2] at hr

end ZFVP
