import ZFVP.SetTheory.ForcingIterationHistory

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private def forcingCodeClause0_0 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP s) ‘ j,
    ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ p ∈ (forcingCodeP s) ‘ i)

private instance forcingCodeClause0_0_definable : ℒₛₑₜ-relation[V] forcingCodeClause0_0 := by
  unfold forcingCodeClause0_0
  definability

private def forcingCodeClause0_1 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP s) ‘ i,
    ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ p ∈ (forcingCodeP s) ‘ j)

private instance forcingCodeClause0_1_definable : ℒₛₑₜ-relation[V] forcingCodeClause0_1 := by
  unfold forcingCodeClause0_1
  definability

private def forcingCodeClause0_2 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ p ∈ (forcingCodeP s) ‘ i, ((forcingCodeE s) ‘ ⟨i, i⟩ₖ) ‘ p = p)

private instance forcingCodeClause0_2_definable : ℒₛₑₜ-relation[V] forcingCodeClause0_2 := by
  unfold forcingCodeClause0_2
  definability

private def forcingCodeClause0_3 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ p ∈ (forcingCodeP s) ‘ k,
      ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ (((forcingCodeπ s) ‘ ⟨j, k⟩ₖ) ‘ p) = ((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) ‘ p)

private instance forcingCodeClause0_3_definable : ℒₛₑₜ-relation[V] forcingCodeClause0_3 := by
  unfold forcingCodeClause0_3
  definability

private def forcingCodeClause0_4 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ p ∈ (forcingCodeP s) ‘ i,
      ((forcingCodeE s) ‘ ⟨j, k⟩ₖ) ‘ (((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ p) = ((forcingCodeE s) ‘ ⟨i, k⟩ₖ) ‘ p)

private instance forcingCodeClause0_4_definable : ℒₛₑₜ-relation[V] forcingCodeClause0_4 := by
  unfold forcingCodeClause0_4
  definability

private def forcingCodeClause0_5 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP s) ‘ i,
    ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ (((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ p) = p)

private instance forcingCodeClause0_5_definable : ℒₛₑₜ-relation[V] forcingCodeClause0_5 := by
  unfold forcingCodeClause0_5
  definability

private def forcingCodeLaws0 (θ s : V) : Prop :=
  forcingCodeClause0_0 θ s ∧
  forcingCodeClause0_1 θ s ∧
  forcingCodeClause0_2 θ s ∧
  forcingCodeClause0_3 θ s ∧
  forcingCodeClause0_4 θ s ∧
  forcingCodeClause0_5 θ s

private instance forcingCodeLaws0_definable : ℒₛₑₜ-relation[V] forcingCodeLaws0 := by
  unfold forcingCodeLaws0
  definability

private def forcingCodeClause1_0 (θ s : V) : Prop :=
  (∀ i ∈ θ, IsForcingPreorder ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i))

private instance forcingCodeClause1_0_definable : ℒₛₑₜ-relation[V] forcingCodeClause1_0 := by
  unfold forcingCodeClause1_0
  definability

private def forcingCodeClause1_1 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ (forcingCodeP s) ‘ j, ∀ b ∈ (forcingCodeP s) ‘ j,
    ⟨a, b⟩ₖ ∈ (forcingCodeR s) ‘ j → ⟨((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ a, ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ b⟩ₖ ∈ (forcingCodeR s) ‘ i)

private instance forcingCodeClause1_1_definable : ℒₛₑₜ-relation[V] forcingCodeClause1_1 := by
  unfold forcingCodeClause1_1
  definability

private def forcingCodeClause1_2 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ (forcingCodeP s) ‘ j, ∀ b ∈ (forcingCodeP s) ‘ i,
    ⟨a, ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ b⟩ₖ ∈ (forcingCodeR s) ‘ j ↔ ⟨((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ a, b⟩ₖ ∈ (forcingCodeR s) ‘ i)

private instance forcingCodeClause1_2_definable : ℒₛₑₜ-relation[V] forcingCodeClause1_2 := by
  unfold forcingCodeClause1_2
  definability

private def forcingCodeLaws1 (θ s : V) : Prop :=
  forcingCodeClause1_0 θ s ∧
  forcingCodeClause1_1 θ s ∧
  forcingCodeClause1_2 θ s

private instance forcingCodeLaws1_definable : ℒₛₑₜ-relation[V] forcingCodeLaws1 := by
  unfold forcingCodeLaws1
  definability

private def forcingCodeClause2_0 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ∈ ((forcingCodeP s) ‘ i) ^ ((forcingCodeP s) ‘ j))

private instance forcingCodeClause2_0_definable : ℒₛₑₜ-relation[V] forcingCodeClause2_0 := by
  unfold forcingCodeClause2_0
  definability

private def forcingCodeClause2_1 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ∈ ((forcingCodeP s) ‘ j) ^ ((forcingCodeP s) ‘ i))

private instance forcingCodeClause2_1_definable : ℒₛₑₜ-relation[V] forcingCodeClause2_1 := by
  unfold forcingCodeClause2_1
  definability

private def forcingCodeLaws2 (θ s : V) : Prop :=
  forcingCodeClause2_0 θ s ∧
  forcingCodeClause2_1 θ s

private instance forcingCodeLaws2_definable : ℒₛₑₜ-relation[V] forcingCodeLaws2 := by
  unfold forcingCodeLaws2
  definability

private def forcingCodeClause3_0 (θ s : V) : Prop :=
  (∀ i ∈ θ, IsForcingTop ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i) ((forcingCodet s) ‘ i))

private instance forcingCodeClause3_0_definable : ℒₛₑₜ-relation[V] forcingCodeClause3_0 := by
  unfold forcingCodeClause3_0
  definability

private def forcingCodeClause3_1 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ ((forcingCodet s) ‘ j) = (forcingCodet s) ‘ i)

private instance forcingCodeClause3_1_definable : ℒₛₑₜ-relation[V] forcingCodeClause3_1 := by
  unfold forcingCodeClause3_1
  definability

private def forcingCodeClause3_2 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ((forcingCodeE s) ‘ ⟨i, j⟩ₖ) ‘ ((forcingCodet s) ‘ i) = (forcingCodet s) ‘ j)

private instance forcingCodeClause3_2_definable : ℒₛₑₜ-relation[V] forcingCodeClause3_2 := by
  unfold forcingCodeClause3_2
  definability

private def forcingCodeLaws3 (θ s : V) : Prop :=
  forcingCodeClause3_0 θ s ∧
  forcingCodeClause3_1 θ s ∧
  forcingCodeClause3_2 θ s

private instance forcingCodeLaws3_definable : ℒₛₑₜ-relation[V] forcingCodeLaws3 := by
  unfold forcingCodeLaws3
  definability

private def forcingCodeClause4_0 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ a ∈ (forcingCodeP s) ‘ j, ∀ b ∈ (forcingCodeP s) ‘ i,
    ⟨b, ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ a⟩ₖ ∈ (forcingCodeR s) ‘ i →
    ((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ ∈ (forcingCodeP s) ‘ j ∧
    ⟨((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ, a⟩ₖ ∈ (forcingCodeR s) ‘ j ∧
    ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) ‘ (((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨a, b⟩ₖ) = b)

private instance forcingCodeClause4_0_definable : ℒₛₑₜ-relation[V] forcingCodeClause4_0 := by
  unfold forcingCodeClause4_0
  definability

private def forcingCodeClause4_1 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ j ∈ θ, ∀ k ∈ θ, i ⊆ j → j ⊆ k →
    ∀ a ∈ (forcingCodeP s) ‘ k, ∀ b ∈ (forcingCodeP s) ‘ i, ⟨b, ((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ (forcingCodeR s) ‘ i →
    ((forcingCodeπ s) ‘ ⟨j, k⟩ₖ) ‘ (((forcingCodeL s) ‘ ⟨i, k⟩ₖ) ‘ ⟨a, b⟩ₖ) =
      ((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨((forcingCodeπ s) ‘ ⟨j, k⟩ₖ) ‘ a, b⟩ₖ)

private instance forcingCodeClause4_1_definable : ℒₛₑₜ-relation[V] forcingCodeClause4_1 := by
  unfold forcingCodeClause4_1
  definability

private def forcingCodeLaws4 (θ s : V) : Prop :=
  forcingCodeClause4_0 θ s ∧
  forcingCodeClause4_1 θ s

private instance forcingCodeLaws4_definable : ℒₛₑₜ-relation[V] forcingCodeLaws4 := by
  unfold forcingCodeLaws4
  definability

private def forcingCodeClause5_0 (θ s : V) : Prop :=
  (∀ i ∈ θ, ∀ k ∈ θ, ∀ j ∈ θ, i ⊆ k → k ⊆ j →
    ∀ a ∈ (forcingCodeP s) ‘ k, ∀ b ∈ (forcingCodeP s) ‘ i, ⟨b, ((forcingCodeπ s) ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ (forcingCodeR s) ‘ i →
    ((forcingCodeL s) ‘ ⟨i, j⟩ₖ) ‘ ⟨((forcingCodeE s) ‘ ⟨k, j⟩ₖ) ‘ a, b⟩ₖ =
      ((forcingCodeE s) ‘ ⟨k, j⟩ₖ) ‘ (((forcingCodeL s) ‘ ⟨i, k⟩ₖ) ‘ ⟨a, b⟩ₖ))

private instance forcingCodeClause5_0_definable : ℒₛₑₜ-relation[V] forcingCodeClause5_0 := by
  unfold forcingCodeClause5_0
  definability

private def forcingCodeLaws5 (θ s : V) : Prop :=
  forcingCodeClause5_0 θ s

private instance forcingCodeLaws5_definable : ℒₛₑₜ-relation[V] forcingCodeLaws5 := by
  unfold forcingCodeLaws5
  definability

private def forcingCodeClause6_0 (_θ s : V) : Prop :=
  (IsFunction (forcingCodeP s))

private instance forcingCodeClause6_0_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_0 := by
  unfold forcingCodeClause6_0
  definability

private def forcingCodeClause6_1 (θ s : V) : Prop :=
  (domain (forcingCodeP s) = θ)

private instance forcingCodeClause6_1_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_1 := by
  unfold forcingCodeClause6_1
  definability

private def forcingCodeClause6_2 (_θ s : V) : Prop :=
  (IsFunction (forcingCodeR s))

private instance forcingCodeClause6_2_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_2 := by
  unfold forcingCodeClause6_2
  definability

private def forcingCodeClause6_3 (θ s : V) : Prop :=
  (domain (forcingCodeR s) = θ)

private instance forcingCodeClause6_3_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_3 := by
  unfold forcingCodeClause6_3
  definability

private def forcingCodeClause6_4 (_θ s : V) : Prop :=
  (IsFunction (forcingCodeπ s))

private instance forcingCodeClause6_4_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_4 := by
  unfold forcingCodeClause6_4
  definability

private def forcingCodeClause6_5 (θ s : V) : Prop :=
  (domain (forcingCodeπ s) = (θ ×ˢ θ))

private instance forcingCodeClause6_5_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_5 := by
  unfold forcingCodeClause6_5
  definability

private def forcingCodeClause6_6 (_θ s : V) : Prop :=
  (IsFunction (forcingCodeE s))

private instance forcingCodeClause6_6_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_6 := by
  unfold forcingCodeClause6_6
  definability

private def forcingCodeClause6_7 (θ s : V) : Prop :=
  (domain (forcingCodeE s) = (θ ×ˢ θ))

private instance forcingCodeClause6_7_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_7 := by
  unfold forcingCodeClause6_7
  definability

private def forcingCodeClause6_8 (_θ s : V) : Prop :=
  (IsFunction (forcingCodeL s))

private instance forcingCodeClause6_8_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_8 := by
  unfold forcingCodeClause6_8
  definability

private def forcingCodeClause6_9 (θ s : V) : Prop :=
  (domain (forcingCodeL s) = (θ ×ˢ θ))

private instance forcingCodeClause6_9_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_9 := by
  unfold forcingCodeClause6_9
  definability

private def forcingCodeClause6_10 (_θ s : V) : Prop :=
  (IsFunction (forcingCodet s))

private instance forcingCodeClause6_10_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_10 := by
  unfold forcingCodeClause6_10
  definability

private def forcingCodeClause6_11 (θ s : V) : Prop :=
  (domain (forcingCodet s) = θ)


private instance forcingCodeClause6_11_definable : ℒₛₑₜ-relation[V] forcingCodeClause6_11 := by
  unfold forcingCodeClause6_11
  definability

private def forcingCodeLaws6 (θ s : V) : Prop :=
  forcingCodeClause6_0 θ s ∧
  forcingCodeClause6_1 θ s ∧
  forcingCodeClause6_2 θ s ∧
  forcingCodeClause6_3 θ s ∧
  forcingCodeClause6_4 θ s ∧
  forcingCodeClause6_5 θ s ∧
  forcingCodeClause6_6 θ s ∧
  forcingCodeClause6_7 θ s ∧
  forcingCodeClause6_8 θ s ∧
  forcingCodeClause6_9 θ s ∧
  forcingCodeClause6_10 θ s ∧
  forcingCodeClause6_11 θ s

private instance forcingCodeLaws6_definable : ℒₛₑₜ-relation[V] forcingCodeLaws6 := by
  unfold forcingCodeLaws6
  definability

private def forcingIterationCodeLaws (θ s : V) : Prop :=
  forcingCodeLaws0 θ s ∧
  forcingCodeLaws1 θ s ∧
  forcingCodeLaws2 θ s ∧
  forcingCodeLaws3 θ s ∧
  forcingCodeLaws4 θ s ∧
  forcingCodeLaws5 θ s ∧
  forcingCodeLaws6 θ s

private theorem forcingIterationCodeLaws_iff (θ s : V) :
    IsForcingIterationCode θ s ↔ forcingIterationCodeLaws θ s := by
  constructor
  · intro h
    exact ⟨⟨h.system.split.projMaps, h.system.split.secMaps, h.system.split.secId, h.system.split.projComp, h.system.split.secComp, h.system.split.retraction⟩, ⟨h.system.order.preorder, h.system.order.projMono, h.system.order.below⟩, ⟨h.system.functions.projection, h.system.functions.sectionMap⟩, ⟨h.system.tops.top, h.system.tops.projTop, h.system.tops.secTop⟩, ⟨h.system.lifts.lift, h.system.lifts.commute⟩, h.system.compatible.compatible, ⟨h.tableP.function, h.tableP.domain_eq, h.tableR.function, h.tableR.domain_eq, h.tableπ.function, h.tableπ.domain_eq, h.tableE.function, h.tableE.domain_eq, h.tableL.function, h.tableL.domain_eq, h.tablet.function, h.tablet.domain_eq⟩⟩
  · rintro ⟨⟨p0, p1, p2, p3, p4, p5⟩, ⟨p6, p7, p8⟩, ⟨p9, p10⟩, ⟨p11, p12, p13⟩, ⟨p14, p15⟩, p16, ⟨p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28⟩⟩
    exact ⟨⟨⟨p0, p1, p2, p3, p4, p5⟩, ⟨p6, p7, p8⟩, ⟨p9, p10⟩, ⟨p11, p12, p13⟩, ⟨p14, p15⟩, ⟨p16⟩⟩, ⟨p17, p18⟩, ⟨p19, p20⟩, ⟨p21, p22⟩, ⟨p23, p24⟩, ⟨p25, p26⟩, ⟨p27, p28⟩⟩

instance forcingIterationCode_definable : ℒₛₑₜ-relation[V] IsForcingIterationCode := by
  have h : ℒₛₑₜ-relation[V] forcingIterationCodeLaws := by
    unfold forcingIterationCodeLaws
    definability
  apply Language.Definable.of_iff h
  intro v
  exact forcingIterationCodeLaws_iff (v 0) (v 1)

instance forcingCodeExtends_definable : ℒₛₑₜ-relation[V] ForcingCodeExtends := by
  have h : ℒₛₑₜ-relation (fun s z : V ↦
    forcingCodeP s ⊆ forcingCodeP z ∧
    forcingCodeR s ⊆ forcingCodeR z ∧
    forcingCodeπ s ⊆ forcingCodeπ z ∧
    forcingCodeE s ⊆ forcingCodeE z ∧
    forcingCodeL s ⊆ forcingCodeL z ∧
    forcingCodet s ⊆ forcingCodet z) := by definability
  apply Language.Definable.of_iff h
  intro v
  constructor
  · intro h
    exact ⟨h.subP, h.subR, h.subπ, h.subE, h.subL, h.subt⟩
  · rintro ⟨hP, hR, hπ, hE, hL, ht⟩
    exact ⟨hP, hR, hπ, hE, hL, ht⟩

instance forcingIterationHistory_definable : ℒₛₑₜ-relation[V] IsForcingIterationHistory := by
  have h : ℒₛₑₜ-relation (fun θ H : V ↦
    (IsFunction H ∧ domain H = θ) ∧
    (∀ i ∈ θ, IsForcingIterationCode (succ i) (H ‘ i)) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ForcingCodeExtends (H ‘ i) (H ‘ j))) := by definability
  apply Language.Definable.of_iff h
  intro v
  constructor
  · intro h
    exact ⟨⟨h.table.function, h.table.domain_eq⟩, h.stage, h.increasing⟩
  · rintro ⟨⟨hf, hd⟩, hs, hi⟩
    exact ⟨⟨hf, hd⟩, hs, hi⟩

instance forcingHistoryTable_definable (c : V → V) (hc : ℒₛₑₜ-function₁ c) :
    ℒₛₑₜ-function₂[V] (fun θ H ↦ forcingHistoryTable θ H c hc) := by
  have h : ℒₛₑₜ-relation₃ (fun y θ H : V ↦
    ∀ p, p ∈ y ↔ ∃ i ∈ θ, p ∈ c (H ‘ i)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingHistoryTable (v 1) (v 2) c hc ↔ _
  rw [mem_ext_iff]
  simp only [forcingHistoryTable, iterationTableUnion, mem_sUnion_iff, repl_spec]
  constructor
  · intro he p
    rw [he p]
    constructor
    · rintro ⟨f, ⟨i, hi, rfl⟩, hp⟩
      exact ⟨i, hi, hp⟩
    · rintro ⟨i, hi, hp⟩
      exact ⟨c ((v 2) ‘ i), ⟨i, hi, rfl⟩, hp⟩
  · intro he p
    rw [he p]
    constructor
    · rintro ⟨i, hi, hp⟩
      exact ⟨c ((v 2) ‘ i), ⟨i, hi, rfl⟩, hp⟩
    · rintro ⟨f, ⟨i, hi, rfl⟩, hp⟩
      exact ⟨i, hi, hp⟩

instance forcingIterationCodeUnion_definable : ℒₛₑₜ-function₂[V] forcingIterationCodeUnion := by
  have hP : ℒₛₑₜ-function₂[V] (fun θ H ↦
      forcingHistoryTable θ H forcingCodeP forcingCodeP_definable) :=
    forcingHistoryTable_definable forcingCodeP forcingCodeP_definable
  have hR : ℒₛₑₜ-function₂[V] (fun θ H ↦
      forcingHistoryTable θ H forcingCodeR forcingCodeR_definable) :=
    forcingHistoryTable_definable forcingCodeR forcingCodeR_definable
  have hπ : ℒₛₑₜ-function₂[V] (fun θ H ↦
      forcingHistoryTable θ H forcingCodeπ forcingCodeπ_definable) :=
    forcingHistoryTable_definable forcingCodeπ forcingCodeπ_definable
  have hE : ℒₛₑₜ-function₂[V] (fun θ H ↦
      forcingHistoryTable θ H forcingCodeE forcingCodeE_definable) :=
    forcingHistoryTable_definable forcingCodeE forcingCodeE_definable
  have hL : ℒₛₑₜ-function₂[V] (fun θ H ↦
      forcingHistoryTable θ H forcingCodeL forcingCodeL_definable) :=
    forcingHistoryTable_definable forcingCodeL forcingCodeL_definable
  have ht : ℒₛₑₜ-function₂[V] (fun θ H ↦
      forcingHistoryTable θ H forcingCodet forcingCodet_definable) :=
    forcingHistoryTable_definable forcingCodet forcingCodet_definable
  unfold forcingIterationCodeUnion forcingIterationCode
  definability

end ZFVP
