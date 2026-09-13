import ZFVP.ModelTheory.WoodinBoundTailName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

noncomputable def woodinBoundCoordinateName (θ i f j : V) : V :=
  let s := kpair.π₁ (woodinIterationRec i)
  forcingCompositionName ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i) f
    (checkName ((forcingCodet s) ‘ i)
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) j))

instance woodinBoundCoordinateName_definable (θ i f : V) :
    ℒₛₑₜ-function₁[V] (woodinBoundCoordinateName θ i f) := by
  unfold woodinBoundCoordinateName
  dsimp only
  apply Language.DefinableFunction₄.comp (F := forcingCompositionName) <;> definability

noncomputable def woodinBoundSuccessorTail (θ i p f k : V) : V :=
  let s := woodinIterationPrefix (succ k)
  let K := woodinIterationCardinalPrefix (succ k)
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := K ‘ k
  let δ := woodinPrefixCutoff P R o κ
  let E := (forcingCodeE s) ‘ ⟨i, k⟩ₖ
  woodinBoundTailName (woodinStageCode P R o δ) (E ‘ p)
    (saturatedWoodinPrefixPosetName P R o κ δ) E (woodinBoundCoordinateName θ i f (succ k))

instance woodinBoundSuccessorTail_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (woodinBoundSuccessorTail θ i p f) := by
  unfold woodinBoundSuccessorTail
  dsimp only
  apply Language.DefinableFunction₅.comp (F := woodinBoundTailName) <;> definability

noncomputable def woodinBoundInverseTail (θ i p f j : V) : V :=
  let s := woodinIterationPrefix j
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix j)
  let δ := forcingInverseSourceCutoff j s γ
  let E := forcingThreadSection j (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) i
  woodinBoundTailName
    (woodinStageCode (forcingInverseCodePoset j s) (forcingInverseCodeOrder j s) (forcingInverseCodeTop j s) δ)
    (E ‘ p) (forcingInverseCollapseName j s δ (forcingInverseHartogsName j s γ)
      (forcingInverseRestorationName j s γ)) E (woodinBoundCoordinateName θ i f j)

instance woodinBoundInverseTail_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (woodinBoundInverseTail θ i p f) := by
  unfold woodinBoundInverseTail
  dsimp only
  apply Language.DefinableFunction₅.comp (F := woodinBoundTailName) <;> definability

/-- The history H contains the already constructed coordinates. The base condition
is fixed, and every later tail uses the same original descending-sequence name. -/
noncomputable def woodinQuotientBoundRule (θ i p f j H : V) : V := by
  classical
  exact if j = i then p else if j ∈ i then
    ((forcingCodeπ (kpair.π₁ (woodinIterationRec i))) ‘ ⟨j, i⟩ₖ) ‘ p else
    if j = succ (⋃ˢ j) then ⟨H ‘ (⋃ˢ j), woodinBoundSuccessorTail θ i p f (⋃ˢ j)⟩ₖ else
    if IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) then H else
      ⟨H, woodinBoundInverseTail θ i p f j⟩ₖ

instance woodinQuotientBoundRule_definable (θ i p f : V) :
    ℒₛₑₜ-function₂[V] (woodinQuotientBoundRule θ i p f) := by
  classical
  have h : ℒₛₑₜ-relation₃ (fun z j H : V ↦
      (j = i ∧ z = p) ∨
      (j ≠ i ∧ j ∈ i ∧ z = ((forcingCodeπ (kpair.π₁ (woodinIterationRec i))) ‘ ⟨j, i⟩ₖ) ‘ p) ∨
      (j ≠ i ∧ j ∉ i ∧ j = succ (⋃ˢ j) ∧
        z = ⟨H ‘ (⋃ˢ j), woodinBoundSuccessorTail θ i p f (⋃ˢ j)⟩ₖ) ∨
      (j ≠ i ∧ j ∉ i ∧ j ≠ succ (⋃ˢ j) ∧
        IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) ∧ z = H) ∨
      (j ≠ i ∧ j ∉ i ∧ j ≠ succ (⋃ˢ j) ∧
        ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) ∧
        z = ⟨H, woodinBoundInverseTail θ i p f j⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinQuotientBoundRule θ i p f (v 1) (v 2) ↔ _
  unfold woodinQuotientBoundRule
  split_ifs <;> tauto

noncomputable def woodinQuotientBoundStep (θ i p f H : V) : V :=
  woodinQuotientBoundRule θ i p f (domain H) H

instance woodinQuotientBoundStep_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (woodinQuotientBoundStep θ i p f) := by
  unfold woodinQuotientBoundStep
  apply Language.DefinableFunction₂.comp <;> definability

noncomputable def woodinQuotientBoundRec (θ i p f j : V) : V :=
  Replacement.transfiniteRec (woodinQuotientBoundStep θ i p f)
    (woodinQuotientBoundStep_definable θ i p f) j

instance woodinQuotientBoundRec_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (woodinQuotientBoundRec θ i p f) :=
  Replacement.transfiniteRec_definable (woodinQuotientBoundStep_definable θ i p f)

noncomputable def woodinQuotientBoundHistory (θ i p f j : V) : V :=
  definableGraph j (woodinQuotientBoundRec θ i p f) (woodinQuotientBoundRec_definable θ i p f)

theorem woodinQuotientBoundRec_rule (θ i p f j : V) [IsOrdinal j] :
    woodinQuotientBoundRec θ i p f j =
      woodinQuotientBoundRule θ i p f j (woodinQuotientBoundHistory θ i p f j) := by
  have he := Replacement.transfiniteRec_spec (woodinQuotientBoundStep θ i p f)
    (woodinQuotientBoundStep_definable θ i p f) (IsOrdinal.toOrdinal j)
  change woodinQuotientBoundRec θ i p f j = woodinQuotientBoundStep θ i p f
    (woodinQuotientBoundHistory θ i p f j) at he
  simpa only [woodinQuotientBoundStep, woodinQuotientBoundHistory, domain_definableGraph] using he

theorem woodinQuotientBoundRec_base (θ i p f : V) [IsOrdinal i] :
    woodinQuotientBoundRec θ i p f i = p := by
  rw [woodinQuotientBoundRec_rule]
  simp only [woodinQuotientBoundRule, ite_true]

theorem woodinQuotientBoundRec_before {θ i p f j : V} [IsOrdinal i] (hj : j ∈ i) :
    woodinQuotientBoundRec θ i p f j =
      ((forcingCodeπ (kpair.π₁ (woodinIterationRec i))) ‘ ⟨j, i⟩ₖ) ‘ p := by
  let := IsOrdinal.of_mem hj
  have hn : j ≠ i := by rintro rfl; exact mem_irrefl _ hj
  rw [woodinQuotientBoundRec_rule]
  simp only [woodinQuotientBoundRule, ite_eq_right hn, ite_eq_left hj]

end ZFVP
