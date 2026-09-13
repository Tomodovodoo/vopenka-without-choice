import ZFVP.ModelTheory.UsubaIterationStages
import ZFVP.ModelTheory.UsubaTransportedLocalUnion
import ZFVP.ModelTheory.ForcingCompositionName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

attribute [local instance] DefinableForcingTower.P_definable DefinableForcingTower.R_definable
  DefinableForcingTower.top_definable DefinableForcingTower.projection_definable
  DefinableForcingTower.section_definable

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

private theorem selectedUnion_comp {n : ℕ}
    {a b c d e f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ
      (fun v ↦ forcingSelectedUnion (a v) (b v) (c v) (d v) (e v) (f v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f]) forcingSelectedUnion_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf])

instance usubaSelectedUnionName_definable :
    ℒₛₑₜ-function₄[V] usubaSelectedUnionName := by
  unfold usubaSelectedUnionName
  apply selectedUnion_comp <;> definability

instance usubaLocalUnionName_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (usubaLocalUnionName (V := V)) := by
  unfold usubaLocalUnionName
  apply Language.DefinableFunction₅.comp (F := forcingCarrierLocalNormalize) <;> definability

noncomputable def usubaBoundCoordinateName (θ i f j : V) : V :=
  forcingCompositionName ((T).P i) ((T).R i) f
    (checkName ((T).top i) ((T).projection j θ))

instance usubaBoundCoordinateName_definable (θ i f : V) :
    ℒₛₑₜ-function₁[V] (usubaBoundCoordinateName θ i f) := by
  unfold usubaBoundCoordinateName
  apply Language.DefinableFunction₄.comp (F := forcingCompositionName) <;> definability

theorem usubaBoundCoordinateName_isName (θ i f j : V) :
    IsForcingName ((T).P i) (usubaBoundCoordinateName θ i f j) :=
  forcingCompositionName_isName _ _ _ _

noncomputable def usubaBoundSuccessorRawTail (θ i f k : V) : V :=
  usubaSelectedUnionName ((T).P k) ((T).R k) ((T).top k)
    (nameAction ((T).sectionMap i k) (usubaBoundCoordinateName θ i f (succ k)))

instance usubaBoundSuccessorRawTail_definable (θ i f : V) :
    ℒₛₑₜ-function₁[V] (usubaBoundSuccessorRawTail θ i f) := by
  unfold usubaBoundSuccessorRawTail
  apply Language.DefinableFunction₄.comp (F := usubaSelectedUnionName) <;> definability

noncomputable def usubaBoundSuccessorTail (θ i p f k : V) : V :=
  usubaLocalUnionName ((T).P k) ((T).R k) ((T).top k)
    (((T).sectionMap i k) ‘ p)
    (nameAction ((T).sectionMap i k) (usubaBoundCoordinateName θ i f (succ k)))

instance usubaBoundSuccessorTail_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (usubaBoundSuccessorTail θ i p f) := by
  unfold usubaBoundSuccessorTail
  apply Language.DefinableFunction₅.comp (F := usubaLocalUnionName) <;> definability

noncomputable def usubaQuotientBoundRule (θ i p f j H : V) : V := by
  classical
  exact if j = i then p else if j ∈ i then ((T).projection j i) ‘ p else
    if j = succ (⋃ˢ j) then ⟨H ‘ (⋃ˢ j), usubaBoundSuccessorTail θ i p f (⋃ˢ j)⟩ₖ else H

instance usubaQuotientBoundRule_definable (θ i p f : V) :
    ℒₛₑₜ-function₂[V] (usubaQuotientBoundRule θ i p f) := by
  classical
  have h : ℒₛₑₜ-relation₃ (fun z j H : V ↦
      (j = i ∧ z = p) ∨
      (j ≠ i ∧ j ∈ i ∧ z = ((T).projection j i) ‘ p) ∨
      (j ≠ i ∧ j ∉ i ∧ j = succ (⋃ˢ j) ∧
        z = ⟨H ‘ (⋃ˢ j), usubaBoundSuccessorTail θ i p f (⋃ˢ j)⟩ₖ) ∨
      (j ≠ i ∧ j ∉ i ∧ j ≠ succ (⋃ˢ j) ∧ z = H)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = usubaQuotientBoundRule θ i p f (v 1) (v 2) ↔ _
  unfold usubaQuotientBoundRule
  split_ifs <;> tauto

noncomputable def usubaQuotientBoundStep (θ i p f H : V) : V :=
  usubaQuotientBoundRule θ i p f (domain H) H

instance usubaQuotientBoundStep_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (usubaQuotientBoundStep θ i p f) := by
  unfold usubaQuotientBoundStep
  apply Language.DefinableFunction₂.comp <;> definability

noncomputable def usubaQuotientBoundRec (θ i p f j : V) : V :=
  Replacement.transfiniteRec (usubaQuotientBoundStep θ i p f)
    (usubaQuotientBoundStep_definable θ i p f) j

instance usubaQuotientBoundRec_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (usubaQuotientBoundRec θ i p f) :=
  Replacement.transfiniteRec_definable (usubaQuotientBoundStep_definable θ i p f)

noncomputable def usubaQuotientBoundHistory (θ i p f j : V) : V :=
  definableGraph j (usubaQuotientBoundRec θ i p f) (usubaQuotientBoundRec_definable θ i p f)

instance usubaQuotientBoundHistory_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (usubaQuotientBoundHistory θ i p f) := by
  unfold usubaQuotientBoundHistory definableGraph
  definability

theorem usubaQuotientBoundRec_rule (θ i p f j : V) [IsOrdinal j] :
    usubaQuotientBoundRec θ i p f j =
      usubaQuotientBoundRule θ i p f j (usubaQuotientBoundHistory θ i p f j) := by
  have he := Replacement.transfiniteRec_spec (usubaQuotientBoundStep θ i p f)
    (usubaQuotientBoundStep_definable θ i p f) (IsOrdinal.toOrdinal j)
  change usubaQuotientBoundRec θ i p f j = usubaQuotientBoundStep θ i p f
    (usubaQuotientBoundHistory θ i p f j) at he
  simpa only [usubaQuotientBoundStep, usubaQuotientBoundHistory, domain_definableGraph] using he

theorem usubaQuotientBoundRec_base (θ i p f : V) [IsOrdinal i] :
    usubaQuotientBoundRec θ i p f i = p := by
  rw [usubaQuotientBoundRec_rule]
  simp only [usubaQuotientBoundRule, ite_true]

theorem usubaQuotientBoundRec_before {θ i p f j : V} [IsOrdinal i] (hj : j ∈ i) :
    usubaQuotientBoundRec θ i p f j = ((T).projection j i) ‘ p := by
  let := IsOrdinal.of_mem hj
  have hn : j ≠ i := by rintro rfl; exact mem_irrefl _ hj
  rw [usubaQuotientBoundRec_rule]
  simp only [usubaQuotientBoundRule, ite_eq_right hn, ite_eq_left hj]

theorem usubaQuotientBoundHistory_table (θ i p f j : V) :
    IsIterationTable j (usubaQuotientBoundHistory θ i p f j) := by
  unfold usubaQuotientBoundHistory
  exact ⟨inferInstance, domain_definableGraph _ _ _⟩

theorem usubaQuotientBoundHistory_value {θ i p f j k : V} (hk : k ∈ j) :
    (usubaQuotientBoundHistory θ i p f j) ‘ k = usubaQuotientBoundRec θ i p f k :=
  value_definableGraph _ _ _ hk

theorem usubaQuotientBoundRec_successor {θ i p f k : V} [IsOrdinal k] (hi : i ∈ succ k) :
    usubaQuotientBoundRec θ i p f (succ k) =
      ⟨usubaQuotientBoundRec θ i p f k, usubaBoundSuccessorTail θ i p f k⟩ₖ := by
  have hne : succ k ≠ i := by rintro rfl; exact mem_irrefl _ hi
  have hn : succ k ∉ i := by
    intro h
    exact mem_irrefl _ (IsOrdinal.toIsTransitive.mem_trans h hi)
  rw [usubaQuotientBoundRec_rule]
  simp only [usubaQuotientBoundRule, ite_eq_right hne, ite_eq_right hn,
    sUnion_succ_of_transitive, ite_true, usubaQuotientBoundHistory_value (mem_succ_self k)]

theorem usubaQuotientBoundRec_limit {θ i p f j : V} [IsOrdinal j]
    (hi : i ∈ j) (hs : j ≠ succ (⋃ˢ j)) :
    usubaQuotientBoundRec θ i p f j = usubaQuotientBoundHistory θ i p f j := by
  have hne : j ≠ i := by rintro rfl; exact mem_irrefl _ hi
  have hn : j ∉ i := by
    intro h
    exact mem_irrefl _ (IsOrdinal.toIsTransitive.mem_trans h hi)
  rw [usubaQuotientBoundRec_rule]
  simp only [usubaQuotientBoundRule, ite_eq_right hne, ite_eq_right hn, ite_eq_right hs]

end ZFVP
