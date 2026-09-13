import ZFVP.SetTheory.CollapsingSystem
import ZFVP.SetTheory.SequenceTree
import ZFVP.SetTheory.WellFoundedRecursion
import ZFVP.SetTheory.NaturalPredecessor
import ZFVP.SetTheory.DenseEmbedding

/-! The tree-embedding lemma: a `λ`-splitting poset of size at most `λ` carrying a collapsing
system for `λ` receives a dense embedding of the tree `λ^{<ω}`. The tree map is built by
well-founded recursion on finite sequences; the children of a node form a `λ`-indexed maximal
antichain inside the decision set of the node. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem domain_empty_eq : domain (∅ : V) = ∅ := by
  apply mem_ext
  intro x
  simp only [mem_domain_iff]
  exact ⟨fun ⟨_, h⟩ ↦ (not_mem_empty h).elim, fun h ↦ (not_mem_empty h).elim⟩

theorem empty_mem_function_empty (A : V) : (∅ : V) ∈ A ^ (∅ : V) := by
  simp [mem_function_iff]

theorem value_insert_kpair {A t n x : V} (ht : t ∈ A ^ n) (hx : x ∈ A) :
    (insert ⟨n, x⟩ₖ t) ‘ n = x := by
  have : IsFunction (insert ⟨n, x⟩ₖ t) := IsFunction.of_mem (function_append_mem ht hx)
  exact value_eq_of_kpair_mem (mem_insert.mpr (Or.inl rfl))

/-- The family of `λ`-indexed maximal antichains below `p` inside the `n`-th decision set. -/
noncomputable def childFamily (P R lam A L E : V) (z : V) : V :=
  {f ∈ P ^ lam ; Injective f ∧ range f ⊆ splitDecisionSet P R A L E (kpair.π₁ z) (kpair.π₂ z) ∧
    IsForcingAntichain P R (range f) ∧
    ∀ r ∈ P, ⟨r, kpair.π₂ z⟩ₖ ∈ R → ∃ α ∈ lam, ForcingCompatible P R (f ‘ α) r}

theorem mem_childFamily_iff (P R lam A L E z f : V) :
    f ∈ childFamily P R lam A L E z ↔ f ∈ P ^ lam ∧ Injective f ∧
      range f ⊆ splitDecisionSet P R A L E (kpair.π₁ z) (kpair.π₂ z) ∧
      IsForcingAntichain P R (range f) ∧
      ∀ r ∈ P, ⟨r, kpair.π₂ z⟩ₖ ∈ R → ∃ α ∈ lam, ForcingCompatible P R (f ‘ α) r := by
  simp only [childFamily, mem_sep_iff, and_assoc]

theorem childFamily_definable (P R lam A L E : V) :
    ℒₛₑₜ-function₁[V] (childFamily P R lam A L E) := by
  have hd := decisionSet_definable P R A L E
  have h : ℒₛₑₜ-relation (fun S z : V ↦ ∀ f, f ∈ S ↔ f ∈ P ^ lam ∧ Injective f ∧
      range f ⊆ splitDecisionSet P R A L E (kpair.π₁ z) (kpair.π₂ z) ∧
      IsForcingAntichain P R (range f) ∧
      ∀ r ∈ P, ⟨r, kpair.π₂ z⟩ₖ ∈ R → ∃ α ∈ lam, ForcingCompatible P R (f ‘ α) r) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = childFamily P R lam A L E (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_childFamily_iff]

/-- The recursion step: the empty sequence goes to the top, and `s = t ⌢ α` goes to the `α`-th
child of the value at `t`. -/
noncomputable def treeStep (one Φ : V) (s g : V) : V := by
  classical
  exact if domain s = ∅ then one else
    (Φ ‘ ⟨⋃ˢ domain s, g ‘ (s ↾ (⋃ˢ domain s))⟩ₖ) ‘ (s ‘ (⋃ˢ domain s))

theorem treeStep_eq_iff (one Φ s g y : V) : treeStep one Φ s g = y ↔
    (domain s = ∅ ∧ y = one) ∨
      (domain s ≠ ∅ ∧ y = (Φ ‘ ⟨⋃ˢ domain s, g ‘ (s ↾ (⋃ˢ domain s))⟩ₖ) ‘ (s ‘ (⋃ˢ domain s))) := by
  by_cases h : domain s = ∅
  · simp [treeStep, h, eq_comm]
  · simp [treeStep, h, eq_comm]

theorem treeStep_definable (one Φ : V) : ℒₛₑₜ-function₂[V] (treeStep one Φ) := by
  have h : ℒₛₑₜ-relation₃ (fun y s g : V ↦ (domain s = ∅ ∧ y = one) ∨
      (domain s ≠ ∅ ∧ y = (Φ ‘ ⟨⋃ˢ domain s, g ‘ (s ↾ (⋃ˢ domain s))⟩ₖ) ‘ (s ‘ (⋃ˢ domain s)))) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (treeStep_eq_iff one Φ (v 1) (v 2) (v 0))

/-- The tree map `λ^{<ω} → P`. -/
noncomputable def treeMap (one Φ lam : V) : V :=
  wellFoundedRecursion (properSegmentRelation_wellFounded lam) (treeStep one Φ) (treeStep_definable one Φ)

theorem treeMap_isFunction (one Φ lam : V) : IsFunction (treeMap one Φ lam) :=
  wellFoundedRecursion_isFunction _ _ _

theorem treeMap_domain (one Φ lam : V) : domain (treeMap one Φ lam) = finiteSequences lam :=
  domain_wellFoundedRecursion _ _ _

theorem treeMap_value (one Φ lam : V) {s : V} (hs : s ∈ finiteSequences lam) :
    (treeMap one Φ lam) ‘ s = treeStep one Φ s
      ((treeMap one Φ lam) ↾ (predecessors (properSegmentRelation lam) (finiteSequences lam) s)) :=
  wellFoundedRecursion_value (properSegmentRelation_wellFounded lam) (treeStep one Φ)
    (treeStep_definable one Φ) hs

theorem treeMap_empty (one Φ lam : V) : (treeMap one Φ lam) ‘ ∅ = one := by
  rw [treeMap_value one Φ lam (empty_mem_finiteSequences lam)]
  exact ((treeStep_eq_iff _ _ _ _ _).mpr (Or.inl ⟨domain_empty_eq, rfl⟩))

theorem treeMap_append {one Φ lam t n α : V} (hn : n ∈ (ω : V)) (ht : t ∈ lam ^ n) (hα : α ∈ lam) :
    (treeMap one Φ lam) ‘ (insert ⟨n, α⟩ₖ t) = (Φ ‘ ⟨n, (treeMap one Φ lam) ‘ t⟩ₖ) ‘ α := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have hs : insert ⟨n, α⟩ₖ t ∈ lam ^ succ n := function_append_mem ht hα
  have hsF : insert ⟨n, α⟩ₖ t ∈ finiteSequences lam :=
    (mem_finiteSequences_iff _ _).mpr ⟨succ n, ω_succ_closed hn, hs⟩
  have htF : t ∈ finiteSequences lam := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩
  rw [treeMap_value one Φ lam hsF]
  have hd : domain (insert ⟨n, α⟩ₖ t) = succ n := domain_eq_of_mem_function hs
  have hne : domain (insert ⟨n, α⟩ₖ t) ≠ ∅ := by
    rw [hd]
    intro h0
    exact not_mem_empty (h0 ▸ mem_succ_self n)
  have hu : ⋃ˢ domain (insert ⟨n, α⟩ₖ t) = n := by
    rw [hd]
    exact sUnion_succ_of_transitive n
  apply (treeStep_eq_iff _ _ _ _ _).mpr
  refine Or.inr ⟨hne, ?_⟩
  rw [hu, function_append_restrict ht, value_insert_kpair ht hα]
  have hfun := treeMap_isFunction one Φ lam
  have htdom : t ∈ domain (treeMap one Φ lam) := by rw [treeMap_domain]; exact htF
  have htpred : t ∈ predecessors (properSegmentRelation lam) (finiteSequences lam) (insert ⟨n, α⟩ₖ t) := by
    refine (mem_predecessors_iff _ _ _ _).mpr ⟨htF, (pair_mem_properSegmentRelation_iff _ _ _).mpr
      ⟨htF, hsF, fun p hp ↦ mem_insert.mpr (Or.inr hp), ?_⟩⟩
    intro heq
    have : ⟨n, α⟩ₖ ∈ t := heq ▸ mem_insert.mpr (Or.inl rfl)
    have := mem_domain_of_kpair_mem this
    rw [domain_eq_of_mem_function ht] at this
    exact mem_irrefl n this
  rw [value_restrict htdom htpred]

section

variable (hAC : InternalChoice V) {P R one lam A L E : V} (hR : IsForcingPreorder P R)
  (hone : one ∈ P) (htop : ∀ p ∈ P, ⟨p, one⟩ₖ ∈ R) [IsOrdinal lam]
  (hP : P ≤# lam) (hsplit : IsSplitting P R lam) (hsys : IsCollapsingSystem P R lam A L)
  (hE : E ∈ P ^ lam)

include hAC hR hP hsplit hsys hE in
/-- A choice of `λ`-indexed maximal antichains for every node and level. -/
theorem exists_childChoice : ∃ Φ : V, IsFunction Φ ∧ domain Φ = (ω : V) ×ˢ P ∧
    ∀ n ∈ (ω : V), ∀ p ∈ P, Φ ‘ ⟨n, p⟩ₖ ∈ childFamily P R lam A L E ⟨n, p⟩ₖ := by
  obtain ⟨Φ, hΦ, hdom, hval⟩ := choice_for_definable_family hAC ((ω : V) ×ˢ P)
    (childFamily P R lam A L E) (childFamily_definable P R lam A L E) (by
      intro z hz
      obtain ⟨n, hn, p, hp, rfl⟩ := mem_prod_iff.mp hz
      obtain ⟨f, hf, hfinj, hfD, hfanti, hfmax⟩ := exists_indexed_maximalAntichain hAC hR hP hsplit hp
        (decisionSet_subset P R A L E n p) (decisionSet_dense hR hsys hE hn hp)
      refine ⟨f, (mem_childFamily_iff _ _ _ _ _ _ _ _).mpr ⟨hf, hfinj, ?_, hfanti, ?_⟩⟩
      · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hfD
      · simpa only [kpair.π₂_kpair] using hfmax)
  exact ⟨Φ, hΦ, hdom, fun n hn p hp ↦ hval _ (kpair_mem_iff.mpr ⟨hn, hp⟩)⟩

variable {Φ : V} (hΦ : ∀ n ∈ (ω : V), ∀ p ∈ P, Φ ‘ ⟨n, p⟩ₖ ∈ childFamily P R lam A L E ⟨n, p⟩ₖ)

include hone hΦ in
theorem treeMap_mem : ∀ s ∈ finiteSequences lam, (treeMap one Φ lam) ‘ s ∈ P := by
  apply finiteSequence_induction lam (fun s ↦ (treeMap one Φ lam) ‘ s ∈ P) (by definability)
  · rw [treeMap_empty]
    exact hone
  · intro n hn t ht α hα ih
    rw [treeMap_append hn ht hα]
    have hf := (mem_childFamily_iff _ _ _ _ _ _ _ _).mp (hΦ n hn _ ih)
    exact function_value_mem hf.1 hα

include hone hΦ in
theorem treeMap_child_mem_decisionSet {t n α : V} (hn : n ∈ (ω : V)) (ht : t ∈ lam ^ n) (hα : α ∈ lam) :
    (treeMap one Φ lam) ‘ (insert ⟨n, α⟩ₖ t) ∈
      splitDecisionSet P R A L E n ((treeMap one Φ lam) ‘ t) := by
  rw [treeMap_append hn ht hα]
  have htP := treeMap_mem hone hΦ t ((mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩)
  have hf := (mem_childFamily_iff _ _ _ _ _ _ _ _).mp (hΦ n hn _ htP)
  have := hf.2.2.1 _ (value_mem_range hf.1 hα)
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using this

include hone hΦ in
theorem treeMap_child_below {t n α : V} (hn : n ∈ (ω : V)) (ht : t ∈ lam ^ n) (hα : α ∈ lam) :
    ⟨(treeMap one Φ lam) ‘ (insert ⟨n, α⟩ₖ t), (treeMap one Φ lam) ‘ t⟩ₖ ∈ R :=
  decisionSet_below _ _ _ _ _ _ _ (treeMap_child_mem_decisionSet hone hΦ hn ht hα)

include hone hΦ in
theorem treeMap_children_incompatible {t n α β : V} (hn : n ∈ (ω : V)) (ht : t ∈ lam ^ n)
    (hα : α ∈ lam) (hβ : β ∈ lam) (hne : α ≠ β) :
    ¬ForcingCompatible P R ((treeMap one Φ lam) ‘ (insert ⟨n, α⟩ₖ t))
      ((treeMap one Φ lam) ‘ (insert ⟨n, β⟩ₖ t)) := by
  rw [treeMap_append hn ht hα, treeMap_append hn ht hβ]
  have htP := treeMap_mem hone hΦ t ((mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩)
  have hf := (mem_childFamily_iff _ _ _ _ _ _ _ _).mp (hΦ n hn _ htP)
  apply hf.2.2.2.1.2 _ (value_mem_range hf.1 hα) _ (value_mem_range hf.1 hβ)
  intro heq
  exact hne (injective_value_eq hf.1 hf.2.1 hα hβ heq)

include hone hΦ in
theorem treeMap_children_maximal {t n r : V} (hn : n ∈ (ω : V)) (ht : t ∈ lam ^ n) (hr : r ∈ P)
    (hrt : ⟨r, (treeMap one Φ lam) ‘ t⟩ₖ ∈ R) :
    ∃ α ∈ lam, ForcingCompatible P R ((treeMap one Φ lam) ‘ (insert ⟨n, α⟩ₖ t)) r := by
  have htP := treeMap_mem hone hΦ t ((mem_finiteSequences_iff _ _).mpr ⟨n, hn, ht⟩)
  have hf := (mem_childFamily_iff _ _ _ _ _ _ _ _).mp (hΦ n hn _ htP)
  obtain ⟨α, hα, hc⟩ := hf.2.2.2.2 r hr (by simpa only [kpair.π₂_kpair] using hrt)
  refine ⟨α, hα, ?_⟩
  rw [treeMap_append hn ht hα]
  exact hc

include hR hone hΦ in
/-- The tree map is order preserving. -/
theorem treeMap_mono : ∀ s ∈ finiteSequences lam, ∀ t ∈ finiteSequences lam, t ⊆ s →
    ⟨(treeMap one Φ lam) ‘ s, (treeMap one Φ lam) ‘ t⟩ₖ ∈ R := by
  apply finiteSequence_induction lam (fun s ↦ ∀ t ∈ finiteSequences lam, t ⊆ s →
    ⟨(treeMap one Φ lam) ‘ s, (treeMap one Φ lam) ‘ t⟩ₖ ∈ R) (by definability)
  · intro t _ hts
    have ht0 : t = ∅ := by
      apply mem_ext
      intro z
      exact ⟨fun hz ↦ hts z hz, fun hz ↦ (not_mem_empty hz).elim⟩
    rw [ht0, treeMap_empty]
    exact hR.2.1 one hone
  · intro n hn u hu α hα ih t ht hts
    have hs : insert ⟨n, α⟩ₖ u ∈ lam ^ succ n := function_append_mem hu hα
    by_cases heq : t = insert ⟨n, α⟩ₖ u
    · rw [heq]
      exact hR.2.1 _ (treeMap_mem hone hΦ _ ((mem_finiteSequences_iff _ _).mpr ⟨succ n, ω_succ_closed hn, hs⟩))
    · have htu : t ⊆ u := by
        have := subset_restrict_of_properSegment hn hs ht hts heq
        rwa [function_append_restrict hu] at this
      have h1 := treeMap_child_below hone hΦ hn hu hα
      have h2 := ih t ht htu
      exact hR.2.2 _ (treeMap_mem hone hΦ _ ((mem_finiteSequences_iff _ _).mpr ⟨succ n, ω_succ_closed hn, hs⟩))
        _ (treeMap_mem hone hΦ u ((mem_finiteSequences_iff _ _).mpr ⟨n, hn, hu⟩))
        _ (treeMap_mem hone hΦ t ht) h1 h2

include hR hone hΦ in
/-- Incomparable sequences have incompatible values. -/
theorem treeMap_incompatible_of_incomparable {s t n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hs : s ∈ lam ^ n) (ht : t ∈ lam ^ m) (h1 : ¬s ⊆ t) (h2 : ¬t ⊆ s) :
    ¬ForcingCompatible P R ((treeMap one Φ lam) ‘ s) ((treeMap one Φ lam) ‘ t) := by
  obtain ⟨k, hk, u, hu, a, ha, b, hb, hab, hus, hut⟩ := exists_branching_of_incomparable hn hm hs ht h1 h2
  have hsF : s ∈ finiteSequences lam := (mem_finiteSequences_iff _ _).mpr ⟨n, hn, hs⟩
  have htF : t ∈ finiteSequences lam := (mem_finiteSequences_iff _ _).mpr ⟨m, hm, ht⟩
  have hua : insert ⟨k, a⟩ₖ u ∈ finiteSequences lam :=
    (mem_finiteSequences_iff _ _).mpr ⟨succ k, ω_succ_closed hk, function_append_mem hu ha⟩
  have hub : insert ⟨k, b⟩ₖ u ∈ finiteSequences lam :=
    (mem_finiteSequences_iff _ _).mpr ⟨succ k, ω_succ_closed hk, function_append_mem hu hb⟩
  have hsa := treeMap_mono hR hone hΦ s hsF _ hua hus
  have htb := treeMap_mono hR hone hΦ t htF _ hub hut
  rintro ⟨r, hr, hrs, hrt⟩
  apply treeMap_children_incompatible hone hΦ hk hu ha hb hab
  exact ⟨r, hr, hR.2.2 r hr _ (treeMap_mem hone hΦ s hsF) _ (treeMap_mem hone hΦ _ hua) hrs hsa,
    hR.2.2 r hr _ (treeMap_mem hone hΦ t htF) _ (treeMap_mem hone hΦ _ hub) hrt htb⟩

include hR hone htop hΦ in
/-- Each level of the tree is predense. -/
theorem treeMap_level_predense : ∀ n ∈ (ω : V), ∀ r ∈ P,
    ∃ s ∈ lam ^ n, ForcingCompatible P R ((treeMap one Φ lam) ‘ s) r := by
  apply naturalNumber_induction (fun n ↦ ∀ r ∈ P,
    ∃ s ∈ lam ^ n, ForcingCompatible P R ((treeMap one Φ lam) ‘ s) r) (by definability)
  · intro r hr
    refine ⟨∅, empty_mem_function_empty lam, r, hr, ?_, hR.2.1 r hr⟩
    rw [treeMap_empty]
    exact htop r hr
  · intro n hn ih r hr
    obtain ⟨s, hs, r', hr', hr's, hr'r⟩ := ih r hr
    obtain ⟨α, hα, hc⟩ := treeMap_children_maximal hone hΦ hn hs hr' hr's
    refine ⟨insert ⟨n, α⟩ₖ s, function_append_mem hs hα, ?_⟩
    obtain ⟨u, hu, hu1, hu2⟩ := hc
    exact ⟨u, hu, hu1, hR.2.2 u hu r' hr' r hr hu2 hr'r⟩

include hR hone htop hΦ hsys hE in
/-- The tree map has dense range. -/
theorem treeMap_dense (hEsurj : range E = P) : ∀ q ∈ P, ∃ s ∈ finiteSequences lam,
    ⟨(treeMap one Φ lam) ‘ s, q⟩ₖ ∈ R := by
  intro q hq
  have : IsFunction E := IsFunction.of_mem hE
  obtain ⟨α, hαq⟩ := mem_range_iff.mp (hEsurj ▸ hq)
  have hα : α ∈ lam := domain_eq_of_mem_function hE ▸ mem_domain_of_kpair_mem hαq
  have hEα : E ‘ α = q := value_eq_of_kpair_mem hαq
  obtain ⟨n, hn, a, ha, hLa, r, hr, hra, hrq⟩ := hsys.cover α hα q hq
  obtain ⟨s, hs, r', hr', hr's, hr'r⟩ := treeMap_level_predense hR hone htop hΦ (succ n) (ω_succ_closed hn) r hr
  obtain ⟨u, β, hu, hβ, rfl⟩ := function_succ_decompose hs
  have hdec := treeMap_child_mem_decisionSet hone hΦ hn hu hβ
  obtain ⟨hsP, _, a', ha', hsa', hdecide⟩ := (mem_decisionSet_iff _ _ _ _ _ _ _ _).mp hdec
  have haP : a ∈ P := (hsys.antichain n hn).1.1 a ha
  have ha'P : a' ∈ P := (hsys.antichain n hn).1.1 a' ha'
  have haa' : a = a' := by
    by_contra hne
    apply (hsys.antichain n hn).1.2 a ha a' ha' hne
    exact ⟨r', hr', hR.2.2 r' hr' r hr a haP hr'r hra, hR.2.2 r' hr' _ hsP a' ha'P hr's hsa'⟩
  subst haa'
  rw [hLa, hEα] at hdecide
  refine ⟨insert ⟨n, β⟩ₖ u, (mem_finiteSequences_iff _ _).mpr ⟨succ n, ω_succ_closed hn, hs⟩, ?_⟩
  rcases hdecide with h | h
  · exact h
  · exfalso
    apply h
    exact ⟨r', hr', hr's, hR.2.2 r' hr' r hr q hq hr'r hrq⟩

include hR hone htop hΦ hsys hE in
/-- The tree-embedding lemma: the tree map is a dense embedding of `λ^{<ω}` into `P`. -/
theorem treeMap_denseEmbedding (hEsurj : range E = P) :
    IsDenseEmbedding (finiteSequences lam) (sequenceOrder lam) P R (treeMap one Φ lam) := by
  have hfun := treeMap_isFunction one Φ lam
  refine ⟨?_, ?_, ?_, treeMap_dense hR hone htop hsys hE hΦ hEsurj⟩
  · have h := IsFunction.mem_function (treeMap one Φ lam)
    rw [treeMap_domain] at h
    apply mem_function_of_mem_function_of_subset h
    intro y hy
    obtain ⟨s, hs⟩ := mem_range_iff.mp hy
    have hsF : s ∈ finiteSequences lam := treeMap_domain one Φ lam ▸ mem_domain_of_kpair_mem hs
    rw [← value_eq_of_kpair_mem hs]
    exact treeMap_mem hone hΦ s hsF
  · intro p hp q hq hqp
    obtain ⟨_, _, hpq⟩ := (pair_mem_sequenceOrder_iff _ _ _).mp hqp
    exact treeMap_mono hR hone hΦ q hq p hp hpq
  · intro p hp q hq hinc
    have hcomp := (sequence_compatible_iff hp hq).not.mp hinc
    push Not at hcomp
    obtain ⟨n, hn, hpn⟩ := (mem_finiteSequences_iff _ _).mp hp
    obtain ⟨m, hm, hqm⟩ := (mem_finiteSequences_iff _ _).mp hq
    exact treeMap_incompatible_of_incomparable hR hone hΦ hn hm hpn hqm hcomp.1 hcomp.2

end

end ZFVP
