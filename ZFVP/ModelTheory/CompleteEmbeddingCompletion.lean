import ZFVP.SetTheory.BooleanCompletion
import ZFVP.SetTheory.MaximalAntichains
import ZFVP.SetTheory.DenseEmbedding
import ZFVP.SetTheory.LevyAbsorptionChain
import ZFVP.SetTheory.GenericNameSeparative

/-! Complete embeddings of forcing preorders and the absorption step of Solovay's uniqueness
argument for the Levy algebra.

A complete embedding is an order preserving, incompatibility preserving map that carries maximal
antichains to maximal antichains. Every dense embedding is one, the cone map of a preorder into
its Boolean completion is one, and a preorder `Q` with a top and of size at most an infinite
`lam ∈ κ` embeds completely into the Boolean completion of `Coll(ω, <κ)`.

The main tool is `isCompleteEmbedding_of_projection`: if `d : Y → P'` is a dense embedding and
`H : Y → Q` is a projection (order preserving, refining, with cofinal image), then
`q ↦ RO-closure of {p ∈ P' : p ≤ d y for some y with H y ≤ q}` is a complete embedding of `Q`
into the Boolean completion of `P'`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `e` is a complete embedding of `(P, R)` into `(P', R')`: a function on `P` that preserves the
order and incompatibility, and for which every maximal antichain of `P` stays maximal in `P'`,
in the form that every `q ∈ P'` has an extension below the image of some member. -/
def IsCompleteEmbedding (P R P' R' e : V) : Prop :=
  IsFunction e ∧ domain e = P ∧
    (∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∈ R → ⟨e ‘ p, e ‘ q⟩ₖ ∈ R') ∧
    (∀ p ∈ P, ∀ q ∈ P, ¬ ForcingCompatible P R p q →
      ¬ ForcingCompatible P' R' (e ‘ p) (e ‘ q)) ∧
    ∀ A, IsMaximalAntichainIn P R P A →
      ∀ q ∈ P', ∃ a ∈ A, ∃ r ∈ P', ⟨r, q⟩ₖ ∈ R' ∧ ⟨r, e ‘ a⟩ₖ ∈ R'

/-! ## Dense embeddings are complete embeddings -/

/-- A dense embedding is a complete embedding. -/
theorem isCompleteEmbedding_of_denseEmbedding {P R P' R' e : V}
    (hR : IsForcingPreorder P R) (hR' : IsForcingPreorder P' R')
    (he : IsDenseEmbedding P R P' R' e) : IsCompleteEmbedding P R P' R' e := by
  refine ⟨IsFunction.of_mem he.1, domain_eq_of_mem_function he.1,
    fun p hp q hq hpq ↦ he.2.1 q hq p hp hpq, fun p hp q hq h ↦ he.2.2.1 p hp q hq h, ?_⟩
  intro A hA q hq
  obtain ⟨p, hp, hpq⟩ := he.2.2.2 q hq
  obtain ⟨a, ha, r, hr, hra, hrp⟩ := hA.2.2 p hp
  refine ⟨a, ha, e ‘ r, he.value_mem hr, ?_, he.2.1 a (hA.2.1 a ha) r hr hra⟩
  exact hR'.2.2 _ (he.value_mem hr) _ (he.value_mem hp) q hq (he.2.1 p hp r hr hrp) hpq

/-! ## The cone map into the Boolean completion -/

theorem coneRegular_definable' (P R : V) : ℒₛₑₜ-function₁[V] (coneRegular P R) := by
  have hd : ℒₛₑₜ-relation[V] (fun C p ↦ ∀ q, q ∈ C ↔ q ∈ P ∧
      ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → ∃ s ∈ P, ⟨s, p⟩ₖ ∈ R ∧ ⟨s, r⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = coneRegular P R (v 1) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h q ↦ (h q).trans mem_coneRegular_iff, fun h q ↦ (h q).trans mem_coneRegular_iff.symm⟩

/-- The internal function `p ↦ coneRegular P R p`. -/
noncomputable def coneRegularMap (P R : V) : V :=
  definableGraph P (coneRegular P R) (coneRegular_definable' P R)

theorem coneRegularMap_value {P R p : V} (hp : p ∈ P) :
    (coneRegularMap P R) ‘ p = coneRegular P R p :=
  value_definableGraph P (coneRegular P R) (coneRegular_definable' P R) hp

/-- The cone map is a complete embedding of a preorder into its Boolean completion. -/
theorem isCompleteEmbedding_coneRegular {P R : V} (hR : IsForcingPreorder P R) :
    IsCompleteEmbedding P R (booleanConditions P R) (booleanOrder P R) (coneRegularMap P R) := by
  refine ⟨definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rw [coneRegularMap_value hp, coneRegularMap_value hq]
    exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
      ⟨coneRegular_mem_booleanConditions hR hp, coneRegular_mem_booleanConditions hR hq,
        coneRegular_mono hR hq hp hpq⟩
  · intro p hp q hq hinc
    rw [coneRegularMap_value hp, coneRegularMap_value hq]
    rintro ⟨C, hC, hCp, hCq⟩
    obtain ⟨_, _, hCp'⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hCp
    obtain ⟨_, _, hCq'⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hCq
    obtain ⟨r, hr⟩ := ((mem_booleanConditions_iff _ _ _).mp hC).2
    have hrp : r ∈ coneRegular P R p := hCp' r hr
    have hrq : r ∈ coneRegular P R q := hCq' r hr
    obtain ⟨hrP, hhp⟩ := mem_coneRegular_iff.mp hrp
    obtain ⟨s, hsP, hsp, hsr⟩ := hhp r hrP (hR.2.1 r hrP)
    have hsq : s ∈ coneRegular P R q :=
      (coneRegular_regular hR q).2.1 r hrq s hsP hsr
    obtain ⟨_, hhq⟩ := mem_coneRegular_iff.mp hsq
    obtain ⟨t, htP, htq, hts⟩ := hhq s hsP (hR.2.1 s hsP)
    exact hinc ⟨t, htP, hR.2.2 t htP s hsP p hp hts hsp, htq⟩
  · intro A hA C hC
    obtain ⟨hCreg, p, hp⟩ := (mem_booleanConditions_iff _ _ _).mp hC
    obtain ⟨a, ha, r, hr, hra, hrp⟩ := hA.2.2 p (hCreg.1 p hp)
    have hrC : r ∈ C := hCreg.2.1 p hp r hr hrp
    refine ⟨a, ha, coneRegular P R r, coneRegular_mem_booleanConditions hR hr, ?_, ?_⟩
    · exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨coneRegular_mem_booleanConditions hR hr, hC, coneRegular_subset_of_mem hR hCreg hrC⟩
    · rw [coneRegularMap_value (hA.2.1 a ha)]
      exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨coneRegular_mem_booleanConditions hR hr,
          coneRegular_mem_booleanConditions hR (hA.2.1 a ha),
          coneRegular_mono hR (hA.2.1 a ha) hr hra⟩

/-- Separativity is what makes the cone map order reflecting: it is not needed for the complete
embedding conditions, but without it the map is not injective. -/
theorem le_of_coneRegular_subset {P R p q : V} (hR : IsForcingPreorder P R)
    (hsep : IsSeparative P R) (hp : p ∈ P) (hq : q ∈ P)
    (h : coneRegular P R p ⊆ coneRegular P R q) : ⟨p, q⟩ₖ ∈ R := by
  by_contra hnot
  obtain ⟨r, hr, hrp, hinc⟩ := hsep p hp q hq hnot
  have hrc : r ∈ coneRegular P R p :=
    mem_coneRegular_iff.mpr ⟨hr, fun s hs hsr ↦
      ⟨s, hs, hR.2.2 s hs r hr p hp hsr hrp, hR.2.1 s hs⟩⟩
  obtain ⟨_, hh⟩ := mem_coneRegular_iff.mp (h r hrc)
  obtain ⟨t, htP, htq, htr⟩ := hh r hr (hR.2.1 r hr)
  exact hinc ⟨t, htP, htr, htq⟩

/-! ## Projections give complete embeddings into a Boolean completion -/

/-- Conditions of `P'` below the image of some `Y`-condition whose projection is below `q`. -/
noncomputable def projectionBelow (Y S P' R' d : V) (H : V → V) (hH : ℒₛₑₜ-function₁[V] H)
    (q : V) : V :=
  haveI := hH
  {p ∈ P' ; ∃ y ∈ Y, ⟨p, d ‘ y⟩ₖ ∈ R' ∧ ⟨H y, q⟩ₖ ∈ S}

theorem mem_projectionBelow_iff (Y S P' R' d : V) (H : V → V) (hH : ℒₛₑₜ-function₁[V] H)
    (q p : V) : p ∈ projectionBelow Y S P' R' d H hH q ↔
      p ∈ P' ∧ ∃ y ∈ Y, ⟨p, d ‘ y⟩ₖ ∈ R' ∧ ⟨H y, q⟩ₖ ∈ S := mem_sep_iff

theorem projectionBelow_subset (Y S P' R' d : V) (H : V → V) (hH : ℒₛₑₜ-function₁[V] H) (q : V) :
    projectionBelow Y S P' R' d H hH q ⊆ P' :=
  fun p hp ↦ ((mem_projectionBelow_iff Y S P' R' d H hH q p).mp hp).1

theorem projectionBelow_downward {Y S P' R' d : V} (hR' : IsForcingPreorder P' R') (H : V → V)
    (hH : ℒₛₑₜ-function₁[V] H) (q : V) :
    IsForcingDownwardClosed P' R' (projectionBelow Y S P' R' d H hH q) := by
  intro p hp r hr hrp
  obtain ⟨hpP, y, hy, hpy, hyq⟩ := (mem_projectionBelow_iff Y S P' R' d H hH q p).mp hp
  refine (mem_projectionBelow_iff Y S P' R' d H hH q r).mpr ⟨hr, y, hy, ?_, hyq⟩
  exact hR'.2.2 r hr p hpP _ (by
    have := hR'.1 _ hpy
    exact (kpair_mem_iff.mp this).2) hrp hpy

theorem projectionCone_definable (Y S P' R' d : V) (H : V → V) (hH : ℒₛₑₜ-function₁[V] H) :
    ℒₛₑₜ-function₁[V] (fun q ↦ forcingClosure P' R' (projectionBelow Y S P' R' d H hH q)) := by
  have := hH
  have hd : ℒₛₑₜ-relation[V] (fun B q ↦ ∀ p, p ∈ B ↔ p ∈ P' ∧
      ∀ r ∈ P', ⟨r, p⟩ₖ ∈ R' → ∃ s, (s ∈ P' ∧ ∃ y ∈ Y, ⟨s, d ‘ y⟩ₖ ∈ R' ∧ ⟨H y, q⟩ₖ ∈ S) ∧
        ⟨s, r⟩ₖ ∈ R') := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = forcingClosure P' R' (projectionBelow Y S P' R' d H hH (v 1)) ↔ _
  rw [mem_ext_iff]
  simp only [mem_forcingClosure_iff, mem_projectionBelow_iff]

/-- A dense embedding `d : Y → P'` together with a projection `H : Y → Q` gives a complete
embedding of `Q` into the Boolean completion of `P'`. -/
theorem isCompleteEmbedding_of_projection {Y T Q S P' R' d : V} (H : V → V)
    (hH : ℒₛₑₜ-function₁[V] H) (hS : IsForcingPreorder Q S)
    (hR' : IsForcingPreorder P' R') (hd : IsDenseEmbedding Y T P' R' d)
    (hHmem : ∀ y ∈ Y, H y ∈ Q)
    (hmono : ∀ y ∈ Y, ∀ y' ∈ Y, ⟨y', y⟩ₖ ∈ T → ⟨H y', H y⟩ₖ ∈ S)
    (hproj : ∀ y ∈ Y, ∀ q ∈ Q, ⟨q, H y⟩ₖ ∈ S → ∃ y' ∈ Y, ⟨y', y⟩ₖ ∈ T ∧ ⟨H y', q⟩ₖ ∈ S)
    (hcover : ∀ q ∈ Q, ∃ y ∈ Y, ⟨H y, q⟩ₖ ∈ S) :
    ∃ e, IsCompleteEmbedding Q S (booleanConditions P' R') (booleanOrder P' R') e := by
  set B : V → V := fun q ↦ projectionBelow Y S P' R' d H hH q with hB
  set F : V → V := fun q ↦ forcingClosure P' R' (B q) with hF
  have hmemB : ∀ q p : V, p ∈ B q ↔ p ∈ P' ∧ ∃ y ∈ Y, ⟨p, d ‘ y⟩ₖ ∈ R' ∧ ⟨H y, q⟩ₖ ∈ S :=
    fun q p ↦ mem_projectionBelow_iff Y S P' R' d H hH q p
  have hBsub : ∀ q : V, B q ⊆ P' := fun q ↦ projectionBelow_subset Y S P' R' d H hH q
  have hBdown : ∀ q : V, IsForcingDownwardClosed P' R' (B q) :=
    fun q ↦ projectionBelow_downward hR' H hH q
  have hBF : ∀ q : V, B q ⊆ F q := fun q ↦ subset_forcingClosure hR' (hBsub q) (hBdown q)
  have hFreg : ∀ q : V, IsForcingRegular P' R' (F q) := fun q ↦ forcingClosure_regular hR' (hBsub q)
  have hFmem : ∀ q ∈ Q, F q ∈ booleanConditions P' R' := by
    intro q hq
    obtain ⟨y, hy, hyq⟩ := hcover q hq
    refine (mem_booleanConditions_iff _ _ _).mpr ⟨hFreg q, d ‘ y, hBF q _ ?_⟩
    exact (hmemB q _).mpr ⟨hd.value_mem hy, y, hy, hR'.2.1 _ (hd.value_mem hy), hyq⟩
  -- the map itself
  refine ⟨definableGraph Q F (projectionCone_definable Y S P' R' d H hH), ?_⟩
  have hval : ∀ q ∈ Q, (definableGraph Q F (projectionCone_definable Y S P' R' d H hH)) ‘ q = F q :=
    fun q hq ↦ value_definableGraph Q F _ hq
  refine ⟨definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_, ?_⟩
  · -- order preserving
    intro p hp q hq hpq
    rw [hval p hp, hval q hq]
    refine (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hFmem p hp, hFmem q hq, ?_⟩
    apply forcingClosure_mono
    intro z hz
    obtain ⟨hzP, y, hy, hzy, hyp⟩ := (hmemB p z).mp hz
    exact (hmemB q z).mpr ⟨hzP, y, hy, hzy, hS.2.2 _ (hHmem y hy) p hp q hq hyp hpq⟩
  · -- incompatibility preserving
    intro p hp q hq hinc
    rw [hval p hp, hval q hq]
    rintro ⟨C, hC, hCp, hCq⟩
    obtain ⟨_, _, hCp'⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hCp
    obtain ⟨_, _, hCq'⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hCq
    obtain ⟨t, ht⟩ := ((mem_booleanConditions_iff _ _ _).mp hC).2
    have htp : t ∈ F p := hCp' t ht
    have htq : t ∈ F q := hCq' t ht
    obtain ⟨htP, hhp⟩ := (mem_forcingClosure_iff _ _ _ _).mp htp
    obtain ⟨s, hs, hst⟩ := hhp t htP (hR'.2.1 t htP)
    have hsP : s ∈ P' := hBsub p s hs
    have hsq : s ∈ F q := (hFreg q).2.1 t htq s hsP hst
    obtain ⟨_, hhq⟩ := (mem_forcingClosure_iff _ _ _ _).mp hsq
    obtain ⟨u, hu, hus⟩ := hhq s hsP (hR'.2.1 s hsP)
    have huP : u ∈ P' := hBsub q u hu
    have hup : u ∈ B p := hBdown p s hs u huP hus
    obtain ⟨_, y, hy, huy, hyp⟩ := (hmemB p u).mp hup
    obtain ⟨_, y', hy', huy', hy'q⟩ := (hmemB q u).mp hu
    have hcomp : ForcingCompatible P' R' (d ‘ y) (d ‘ y') := ⟨u, huP, huy, huy'⟩
    obtain ⟨z, hz, hzy, hzy'⟩ := hd.compatible_of_value hy hy' hcomp
    exact hinc ⟨H z, hHmem z hz,
      hS.2.2 _ (hHmem z hz) _ (hHmem y hy) p hp (hmono y hy z hz hzy) hyp,
      hS.2.2 _ (hHmem z hz) _ (hHmem y' hy') q hq (hmono y' hy' z hz hzy') hy'q⟩
  · -- maximal antichains stay maximal
    intro A hA C hC
    obtain ⟨hCreg, p, hp⟩ := (mem_booleanConditions_iff _ _ _).mp hC
    have hpP : p ∈ P' := hCreg.1 p hp
    obtain ⟨y, hy, hyp⟩ := hd.2.2.2 p hpP
    obtain ⟨a, ha, r, hr, hra, hry⟩ := hA.2.2 (H y) (hHmem y hy)
    obtain ⟨y', hy', hy'y, hy'r⟩ := hproj y hy r hr hry
    have hdy' : d ‘ y' ∈ P' := hd.value_mem hy'
    have hdy'p : ⟨d ‘ y', p⟩ₖ ∈ R' :=
      hR'.2.2 _ hdy' _ (hd.value_mem hy) p hpP (hd.2.1 y hy y' hy' hy'y) hyp
    have hdy'C : d ‘ y' ∈ C := hCreg.2.1 p hp _ hdy' hdy'p
    have haQ : a ∈ Q := hA.2.1 a ha
    have hy'a : ⟨H y', a⟩ₖ ∈ S :=
      hS.2.2 _ (hHmem y' hy') r hr a haQ hy'r hra
    have hdy'B : d ‘ y' ∈ B a := (hmemB a _).mpr ⟨hdy', y', hy', hR'.2.1 _ hdy', hy'a⟩
    refine ⟨a, ha, coneRegular P' R' (d ‘ y'), coneRegular_mem_booleanConditions hR' hdy', ?_, ?_⟩
    · exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨coneRegular_mem_booleanConditions hR' hdy', hC,
          coneRegular_subset_of_mem hR' hCreg hdy'C⟩
    · rw [hval a haQ]
      exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr
        ⟨coneRegular_mem_booleanConditions hR' hdy', hFmem a haQ,
          coneRegular_subset_of_mem hR' (hFreg a) (hBF a _ hdy'B)⟩

/-! ## Absorption into the Levy algebra -/

/-- Every Levy condition is supported on the columns below `κ`. -/
theorem levyColumns_full (κ : V) : levyColumns κ κ = levyCollapse κ := by
  ext p
  rw [mem_levyColumns_iff]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  apply levyCut_of_subset
  intro z hz
  obtain ⟨n, α, γ, hn, hα, rfl⟩ := levyCollapse_mem_shape h hz
  exact ⟨⟨n, α⟩ₖ, kpair_mem_iff.mpr ⟨hn, hα⟩, γ, rfl⟩

theorem levyColumnsOrder_full (κ : V) : levyColumnsOrder κ κ = levyOrder κ := by
  unfold levyColumnsOrder levyOrder
  rw [levyColumns_full]

/-- Absorption with a trivial base algebra: a preorder with a top and of size at most an infinite
`lam ∈ κ` embeds completely into the Boolean completion of `Coll(ω, <κ)`. -/
theorem levy_exists_completeEmbedding_of_small {κ Q S one lam : V} [IsOrdinal κ]
    (hAC : InternalChoice V) (hR : IsForcingPreorder Q S) (htop : IsForcingTop Q S one)
    (hlam : lam ∈ κ) (hωlam : (ω : V) ⊆ lam) (hQ : Q ≤# lam) :
    ∃ e, IsCompleteEmbedding Q S
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) e := by
  have hR' : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hT : IsForcingPreorder (absorptionPoset κ κ lam) (absorptionOrder κ κ lam) :=
    absorptionOrder_preorder κ κ lam
  obtain ⟨d, hd0⟩ := absorptionPoset_denseEmbedding_columns (κ := κ) (C' := κ) hlam hlam hωlam
  have hd : IsDenseEmbedding (absorptionPoset κ κ lam) (absorptionOrder κ κ lam)
      (levyCollapse κ) (levyOrder κ) d := by
    rw [← levyColumns_full κ, ← levyColumnsOrder_full κ]
    exact hd0
  obtain ⟨g, hg0⟩ := absorptionPoset_denseEmbedding_product (κ := κ) (C' := κ) hlam hlam hωlam
    hAC hR htop hQ
  have hg : IsDenseEmbedding (absorptionPoset κ κ lam) (absorptionOrder κ κ lam)
      (Q ×ˢ levyCollapse κ) (productOrder Q S (levyCollapse κ) (levyOrder κ)) g := by
    rw [← levyColumns_full κ, ← levyColumnsOrder_full κ]
    exact hg0
  have hprod : IsForcingPreorder (Q ×ˢ levyCollapse κ)
      (productOrder Q S (levyCollapse κ) (levyOrder κ)) := productOrder_preorder hR hR'
  -- the projection to the first coordinate of the product
  have hH : ℒₛₑₜ-function₁[V] (fun y ↦ kpair.π₁ (g ‘ y)) := by definability
  have hpair : ∀ y ∈ absorptionPoset κ κ lam, ∃ a ∈ Q, ∃ b ∈ levyCollapse κ, g ‘ y = ⟨a, b⟩ₖ := by
    intro y hy
    obtain ⟨a, ha, b, hb, hab⟩ := mem_prod_iff.mp (hg.value_mem hy)
    exact ⟨a, ha, b, hb, hab⟩
  have hHmem : ∀ y ∈ absorptionPoset κ κ lam, kpair.π₁ (g ‘ y) ∈ Q := by
    intro y hy
    obtain ⟨a, ha, b, _, hab⟩ := hpair y hy
    rw [hab, kpair.π₁_kpair]
    exact ha
  have hmono : ∀ y ∈ absorptionPoset κ κ lam, ∀ y' ∈ absorptionPoset κ κ lam,
      ⟨y', y⟩ₖ ∈ absorptionOrder κ κ lam → ⟨kpair.π₁ (g ‘ y'), kpair.π₁ (g ‘ y)⟩ₖ ∈ S := by
    intro y hy y' hy' hyy
    obtain ⟨a, _, b, _, hab⟩ := hpair y hy
    obtain ⟨a', _, b', _, hab'⟩ := hpair y' hy'
    have := hg.2.1 y hy y' hy' hyy
    rw [hab, hab'] at this ⊢
    rw [kpair.π₁_kpair, kpair.π₁_kpair]
    exact ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp this).2.2.2.2.1
  have hproj : ∀ y ∈ absorptionPoset κ κ lam, ∀ q ∈ Q, ⟨q, kpair.π₁ (g ‘ y)⟩ₖ ∈ S →
      ∃ y' ∈ absorptionPoset κ κ lam, ⟨y', y⟩ₖ ∈ absorptionOrder κ κ lam ∧
        ⟨kpair.π₁ (g ‘ y'), q⟩ₖ ∈ S := by
    intro y hy q hq hqy
    obtain ⟨a, ha, b, hb, hab⟩ := hpair y hy
    rw [hab, kpair.π₁_kpair] at hqy
    have hmem : ⟨q, b⟩ₖ ∈ Q ×ˢ levyCollapse κ := kpair_mem_iff.mpr ⟨hq, hb⟩
    have hbelow : ⟨⟨q, b⟩ₖ, g ‘ y⟩ₖ ∈ productOrder Q S (levyCollapse κ) (levyOrder κ) := by
      rw [hab]
      exact (pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mpr
        ⟨hq, hb, ha, hb, hqy, hR'.2.1 b hb⟩
    obtain ⟨y', hy', hy'y, hgy'⟩ := hg.exists_below hT hprod hy hmem hbelow
    refine ⟨y', hy', hy'y, ?_⟩
    obtain ⟨a', _, b', _, hab'⟩ := hpair y' hy'
    rw [hab'] at hgy' ⊢
    rw [kpair.π₁_kpair]
    exact ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hgy').2.2.2.2.1
  have hcover : ∀ q ∈ Q, ∃ y ∈ absorptionPoset κ κ lam, ⟨kpair.π₁ (g ‘ y), q⟩ₖ ∈ S := by
    intro q hq
    have hmem : ⟨q, (∅ : V)⟩ₖ ∈ Q ×ˢ levyCollapse κ :=
      kpair_mem_iff.mpr ⟨hq, empty_mem_levyCollapse κ⟩
    obtain ⟨y, hy, hgy⟩ := hg.2.2.2 _ hmem
    refine ⟨y, hy, ?_⟩
    obtain ⟨a, _, b, _, hab⟩ := hpair y hy
    rw [hab] at hgy ⊢
    rw [kpair.π₁_kpair]
    exact ((pair_mem_productOrder_iff _ _ _ _ _ _ _ _).mp hgy).2.2.2.2.1
  exact isCompleteEmbedding_of_projection _ hH hR hR' hd hHmem hmono hproj hcover

end ZFVP
