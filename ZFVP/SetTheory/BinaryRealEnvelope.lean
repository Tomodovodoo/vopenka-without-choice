import ZFVP.SetTheory.RealGDeltaCodes
import ZFVP.SetTheory.LebesgueNull

/-! A real G-delta envelope whose excess lies in the binary image of the Cantor excess. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryEnvelopeOpen (g n : V) : V :=
  realUnitThickening n ∩ ((dedekindReals V) \ binaryImage (treeBody (avoidingTree (g ‘ n))))

instance binaryEnvelopeOpen_definable : ℒₛₑₜ-function₂[V] binaryEnvelopeOpen := by
  unfold binaryEnvelopeOpen
  definability

theorem binaryEnvelopeOpen_isOpen (g : V) {n : V} (hn : n ∈ (ω : V)) :
    IsRealOpen (binaryEnvelopeOpen g n) :=
  isRealOpen_inter (realUnitThickening_isOpen hn)
    (binaryTreeImage_complement_open (avoidingTree_isTree _))

noncomputable def binaryRealEnvelopeCode (g : V) : V :=
  definableGraph (ω : V) (fun n ↦ realInteriorCode (binaryEnvelopeOpen g n)) (by definability)

instance binaryRealEnvelopeCode_definable : ℒₛₑₜ-function₁[V] binaryRealEnvelopeCode := by
  have h : ℒₛₑₜ-relation (fun f g : V ↦ ∀ p, p ∈ f ↔ ∃ n ∈ (ω : V),
      p = ⟨n, realInteriorCode (binaryEnvelopeOpen g n)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [binaryRealEnvelopeCode, mem_definableGraph_iff]

theorem binaryRealEnvelopeCode_mem (g : V) :
    binaryRealEnvelopeCode g ∈ (℘ (realBasicCodes V)) ^ (ω : V) :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ _ ↦
    mem_power_iff.mpr (fun _ hp ↦ (mem_sep_iff.mp hp).1))

theorem binaryRealEnvelopeCode_open (g : V) {n : V} (hn : n ∈ (ω : V)) :
    realOpenFrom ((binaryRealEnvelopeCode g) ‘ n) = binaryEnvelopeOpen g n := by
  rw [binaryRealEnvelopeCode, value_definableGraph _ _ _ hn]
  exact (realOpen_eq_interiorCode (binaryEnvelopeOpen_isOpen g hn)).symm

theorem binaryRealEnvelope_iff {g x : V}
    (hg : g ∈ (℘ (binarySequences V)) ^ (ω : V)) :
    x ∈ realGDelta (binaryRealEnvelopeCode g) ↔
      x ∈ unitReals V ∧ ∀ c ∈ cantorSpace V, binaryReal c = x → c ∈ gDelta g := by
  have hgn : ∀ n ∈ (ω : V), g ‘ n ⊆ binarySequences V := fun n hn ↦
    mem_power_iff.mp (function_value_mem hg hn)
  constructor
  · intro hx
    obtain ⟨hxcut, hxn⟩ := (mem_realGDelta_iff _ _).mp hx
    have hrows : ∀ n ∈ (ω : V), x ∈ binaryEnvelopeOpen g n := by
      intro n hn
      simpa only [binaryRealEnvelopeCode_open _ hn] using hxn n hn
    refine ⟨(unitReals_iff_thickenings _).mpr ⟨hxcut,
      fun n hn ↦ (mem_inter_iff.mp (hrows n hn)).1⟩, ?_⟩
    intro c hc hcx
    apply (mem_gDelta_iff _ _).mpr
    refine ⟨hc, fun n hn ↦ ?_⟩
    by_contra hcnot
    have hcT : c ∈ treeBody (avoidingTree (g ‘ n)) :=
      (mem_treeBody_avoidingTree_iff (hgn n hn) hc).mpr (fun hmeet ↦ hcnot
        ((mem_openFrom_iff_meets _ _).mpr ⟨hc, hmeet⟩))
    exact (mem_sdiff_iff.mp (mem_inter_iff.mp (hrows n hn)).2).2
      ((mem_binaryImage_iff _ _).mpr ⟨c, hcT, hcx⟩)
  · rintro ⟨hxU, hfiber⟩
    have hxcut := ((mem_unitReals_iff _).mp hxU).1
    refine (mem_realGDelta_iff _ _).mpr ⟨hxcut, fun n hn ↦ ?_⟩
    rw [binaryRealEnvelopeCode_open _ hn]
    refine mem_inter_iff.mpr ⟨unit_subset_realUnitThickening hn x hxU,
      mem_sdiff_iff.mpr ⟨(mem_dedekindReals_iff _).mpr hxcut, ?_⟩⟩
    intro hxI
    obtain ⟨c, hcT, hcx⟩ := (mem_binaryImage_iff _ _).mp hxI
    have hc := treeBody_subset_cantorSpace _ c hcT
    have hcg := ((mem_gDelta_iff _ _).mp (hfiber c hc hcx)).2 n hn
    exact ((mem_treeBody_avoidingTree_iff (hgn n hn) hc).mp hcT)
      ((mem_openFrom_iff_meets _ _).mp hcg).2

theorem unitReal_coded_envelope_reduction {A : V} (hA : A ⊆ unitReals V)
    (hLM : IsLebesgueMeasurable (binaryPreimage A)) :
    ∃ g ∈ (℘ (realBasicCodes V)) ^ (ω : V), ∃ N,
      IsNull N ∧ A ⊆ realGDelta g ∧ (realGDelta g \ A) ⊆ binaryImage N := by
  obtain ⟨g, hg, hBg, hN⟩ := hLM
  refine ⟨binaryRealEnvelopeCode g, binaryRealEnvelopeCode_mem g,
    gDelta g \ binaryPreimage A, hN, ?_, ?_⟩
  · intro x hx
    apply (binaryRealEnvelope_iff hg).mpr
    refine ⟨hA x hx, fun c hc hcx ↦ hBg c ?_⟩
    exact (mem_binaryPreimage_iff _ _).mpr ⟨hc, hcx.symm ▸ hx⟩
  · intro x hx
    obtain ⟨hxg, hxA⟩ := mem_sdiff_iff.mp hx
    obtain ⟨hxU, hfiber⟩ := (binaryRealEnvelope_iff hg).mp hxg
    obtain ⟨c, hc, hcx⟩ := binaryReal_surjective hxU
    refine (mem_binaryImage_iff _ _).mpr ⟨c, mem_sdiff_iff.mpr ⟨hfiber c hc hcx, ?_⟩, hcx⟩
    intro hcB
    exact hxA (hcx ▸ ((mem_binaryPreimage_iff _ _).mp hcB).2)

end ZFVP
