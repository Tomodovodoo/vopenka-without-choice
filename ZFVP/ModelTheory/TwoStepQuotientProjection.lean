import ZFVP.ModelTheory.ProjectionQuotient
import ZFVP.ModelTheory.TwoStepSecondFilter
import ZFVP.ModelTheory.ForcingModelEvaluation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Every stronger interpreted iterand condition has a representative below a
specified condition in the projection quotient. -/
theorem twoStep_quotient_lift (A : ForcingContext V) {Q S t p : V}
    (h : IsForcingIterand A.P A.R Q S t) (τ : ForcingName A.P)
    (ha : ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t) (hp : p ∈ A.G)
    {x : A.Model} (hx : x ∈ A.ofName ⟨Q, h.posetName⟩)
    (hle : ⟨x, A.ofName τ⟩ₖ ∈ A.ofName ⟨S, h.orderName⟩) :
    ∃ r ∈ A.G, ∃ σ : ForcingName A.P,
      ⟨r, σ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t ∧
      ⟨⟨r, σ.val⟩ₖ, ⟨p, τ.val⟩ₖ⟩ₖ ∈ twoStepOrder A.P A.R Q S t ∧
      A.ofName σ = x := by
  obtain ⟨σ, q, hq, hσq, rfl⟩ := (A.mem_ofName_iff ⟨Q, h.posetName⟩ x).mp hx
  have he : boundedPairMemberFormula.Evalb
      (fun i ↦ A.ofName (![⟨S, h.orderName⟩, σ, τ] i)) :=
    (Defined.eval_iff _).mpr hle
  obtain ⟨s, hs, hforce⟩ :=
    (A.formula_truth boundedPairMemberFormula ![⟨S, h.orderName⟩, σ, τ]).mp he
  change s ∈ forcingFormula A.P A.R boundedPairMemberFormula (standardTuple ![S, σ.val, τ.val]) at hforce
  obtain ⟨u, hu, hup, huq⟩ := A.generic.1.2.2.2 p hp q hq
  obtain ⟨r, hr, hru, hrs⟩ := A.generic.1.2.2.2 u hu s hs
  have hrP := A.generic.1.1 r hr
  have hrp := A.order.2.2 r hrP u (A.generic.1.1 u hu) p
    (A.generic.1.1 p hp) hru hup
  have hrq := A.order.2.2 r hrP u (A.generic.1.1 u hu) q
    (A.generic.1.1 q hq) hru huq
  have hm := atomicMembership_mono A.order
    (atomicMembership_of_pair A.order (A.generic.1.1 q hq) hσq) hrP hrq
  have hσ : σ.val ∈ twoStepNames Q t := by
    exact mem_union_iff.mpr (Or.inl (mem_domain_of_kpair_mem hσq))
  have hb : ⟨r, σ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr ⟨hrP, hσ, hm⟩
  refine ⟨r, hr, σ, hb, ?_, rfl⟩
  apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
  refine ⟨hb, ha, ?_, ?_⟩
  · simpa only [kpair.π₁_kpair] using hrp
  · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      (forcingFormula_regular A.order boundedPairMemberFormula _).2.1 s hforce r hrP hrs


noncomputable def twoStepQuotientProjection (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) : A.Model :=
  definableGraph (A.projectionQuotient (twoStepConditions A.P A.R Q t)
    (twoStepProjection A.P A.R Q t))
    (fun a ↦ (A.evaluationGraph (twoStepNames Q t) (fun _ hσ ↦ h.name hσ)) ‘ (kpair.π₂ a))
    (by definability)

theorem twoStepQuotientProjection_value (A : ForcingContext V) {Q S t p : V}
    (h : IsForcingIterand A.P A.R Q S t) (τ : ForcingName A.P)
    (ha : ⟨p, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t) (hp : p ∈ A.G) :
    (A.twoStepQuotientProjection h) ‘ (A.check ⟨p, τ.val⟩ₖ) = A.ofName τ := by
  have hq := (A.check_mem_projectionQuotient_iff (twoStepProjection_maps A.P A.R Q t)).mpr
    ⟨ha, by simpa only [twoStepProjection_value ha, kpair.π₁_kpair] using hp⟩
  rw [twoStepQuotientProjection, value_definableGraph _ _ _ hq,
    A.check_kpair, kpair.π₂_kpair]
  exact A.evaluationGraph_value _ _ τ.val
    ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp ha).2.1

theorem twoStepQuotientProjection_maps (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) :
    A.twoStepQuotientProjection h ∈ (A.ofName ⟨Q, h.posetName⟩) ^
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t)) := by
  apply definableGraph_mem_function_of_mapsTo
  intro a ha
  obtain ⟨b, hb, hbg, rfl⟩ := (A.mem_projectionQuotient_iff
    (twoStepProjection_maps A.P A.R Q t) a).mp ha
  obtain ⟨p, _, σ, hσ, rfl, hm⟩ := (mem_twoStepConditions _ _ _ _ _).mp hb
  rw [twoStepProjection_value hb, kpair.π₁_kpair] at hbg
  rw [A.check_kpair, kpair.π₂_kpair, A.evaluationGraph_value _ _ σ hσ]
  exact A.ofName_mem_of_forcedMember ⟨σ, h.name hσ⟩ ⟨Q, h.posetName⟩ hbg hm

theorem twoStepQuotientProjection_projection (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) :
    IsForcingProjection (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩)
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
        (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))
      (A.twoStepQuotientProjection h) := by
  refine ⟨A.twoStepQuotientProjection_maps h, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨c, hc, hcg, rfl⟩ := (A.mem_projectionQuotient_iff
      (twoStepProjection_maps A.P A.R Q t) a).mp ha
    obtain ⟨d, hd, hdg, rfl⟩ := (A.mem_projectionQuotient_iff
      (twoStepProjection_maps A.P A.R Q t) b).mp hb
    obtain ⟨p, _, σ, hσ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
    obtain ⟨q, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hd
    rw [twoStepProjection_value hc, kpair.π₁_kpair] at hcg
    rw [twoStepProjection_value hd, kpair.π₁_kpair] at hdg
    rw [A.twoStepQuotientProjection_value h ⟨σ, h.name hσ⟩ hc hcg,
      A.twoStepQuotientProjection_value h ⟨τ, h.name hτ⟩ hd hdg]
    have hcd := ((A.projectionQuotientOrder_pair_iff _ _ _ _ _).mp hab).1
    rw [← A.check_kpair, A.check_mem_iff] at hcd
    have hf := ((kpair_mem_twoStepOrder _ _ _ _ _ _ _).mp hcd).2.2.2
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hf
    exact A.ofName_pair_mem_of_forced ⟨S, h.orderName⟩ ⟨σ, h.name hσ⟩ ⟨τ, h.name hτ⟩ hcg hf
  · intro a ha x hx hxa
    obtain ⟨b, hb, hbg, rfl⟩ := (A.mem_projectionQuotient_iff
      (twoStepProjection_maps A.P A.R Q t) a).mp ha
    obtain ⟨p, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hb
    rw [twoStepProjection_value hb, kpair.π₁_kpair] at hbg
    rw [A.twoStepQuotientProjection_value h ⟨τ, h.name hτ⟩ hb hbg] at hxa
    obtain ⟨r, hr, σ, hc, hcb, he⟩ := A.twoStep_quotient_lift h ⟨τ, h.name hτ⟩ hb hbg hx hxa
    have hcq := (A.check_mem_projectionQuotient_iff (twoStepProjection_maps A.P A.R Q t)).mpr
      ⟨hc, by simpa only [twoStepProjection_value hc, kpair.π₁_kpair] using hr⟩
    refine ⟨A.check ⟨r, σ.val⟩ₖ, hcq, ?_, ?_⟩
    · exact (A.projectionQuotientOrder_pair_iff _ _ _ _ _).mpr
        ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr hcb, hcq, ha⟩
    · exact (A.twoStepQuotientProjection_value h σ hc hr).trans he


/-- A semantic comparison can be made into a ground two-step comparison by
strengthening the first coordinate inside the generic filter. -/
theorem twoStep_quotient_refine (A : ForcingContext V) {Q S t p q : V}
    (h : IsForcingIterand A.P A.R Q S t) (σ τ : ForcingName A.P)
    (ha : ⟨p, σ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t) (hp : p ∈ A.G)
    (hb : ⟨q, τ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t) (hq : q ∈ A.G)
    (hle : ⟨A.ofName σ, A.ofName τ⟩ₖ ∈ A.ofName ⟨S, h.orderName⟩) :
    ∃ r ∈ A.G, ⟨r, σ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t ∧
      ⟨⟨r, σ.val⟩ₖ, ⟨p, σ.val⟩ₖ⟩ₖ ∈ twoStepOrder A.P A.R Q S t ∧
      ⟨⟨r, σ.val⟩ₖ, ⟨q, τ.val⟩ₖ⟩ₖ ∈ twoStepOrder A.P A.R Q S t := by
  have he : boundedPairMemberFormula.Evalb
      (fun i ↦ A.ofName (![⟨S, h.orderName⟩, σ, τ] i)) :=
    (Defined.eval_iff _).mpr hle
  obtain ⟨s, hs, hf⟩ :=
    (A.formula_truth boundedPairMemberFormula ![⟨S, h.orderName⟩, σ, τ]).mp he
  change s ∈ forcingFormula A.P A.R boundedPairMemberFormula (standardTuple ![S, σ.val, τ.val]) at hf
  obtain ⟨u, hu, hup, huq⟩ := A.generic.1.2.2.2 p hp q hq
  obtain ⟨r, hr, hru, hrs⟩ := A.generic.1.2.2.2 u hu s hs
  have hrP := A.generic.1.1 r hr
  have hrp := A.order.2.2 r hrP u (A.generic.1.1 u hu) p (A.generic.1.1 p hp) hru hup
  have hrq := A.order.2.2 r hrP u (A.generic.1.1 u hu) q (A.generic.1.1 q hq) hru huq
  have hm := atomicMembership_mono A.order
    ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp ha).2.2 hrP hrp
  have hc : ⟨r, σ.val⟩ₖ ∈ twoStepConditions A.P A.R Q t :=
    (kpair_mem_twoStepConditions _ _ _ _ _ _).mpr
      ⟨hrP, ((kpair_mem_twoStepConditions _ _ _ _ _ _).mp ha).2.1, hm⟩
  refine ⟨r, hr, hc, ?_, ?_⟩
  · apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    refine ⟨hc, ha, ?_, ?_⟩
    · simpa only [kpair.π₁_kpair] using hrp
    · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
        forcedPreorder_refl A.order A.top hrP ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ σ
          (h.preorder r hrP) hm
  · apply (kpair_mem_twoStepOrder _ _ _ _ _ _ _).mpr
    refine ⟨hc, hb, ?_, ?_⟩
    · simpa only [kpair.π₁_kpair] using hrq
    · simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
        (forcingFormula_regular A.order boundedPairMemberFormula _).2.1 s hf r hrP hrs


 theorem twoStepQuotientProjection_compatible_iff (A : ForcingContext V) {Q S t : V}
    (h : IsForcingIterand A.P A.R Q S t) {a b : A.Model}
    (ha : a ∈ A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
    (hb : b ∈ A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t)) :
    ForcingCompatible (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
        (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t)) a b ↔
    ForcingCompatible (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩)
      ((A.twoStepQuotientProjection h) ‘ a) ((A.twoStepQuotientProjection h) ‘ b) := by
  have hπ := A.twoStepQuotientProjection_projection h
  constructor
  · rintro ⟨c, hc, hca, hcb⟩
    exact ⟨_, function_value_mem hπ.maps hc, hπ.monotone c hc a ha hca, hπ.monotone c hc b hb hcb⟩
  · obtain ⟨c, hc, hcg, rfl⟩ := (A.mem_projectionQuotient_iff
      (twoStepProjection_maps A.P A.R Q t) a).mp ha
    obtain ⟨d, hd, hdg, rfl⟩ := (A.mem_projectionQuotient_iff
      (twoStepProjection_maps A.P A.R Q t) b).mp hb
    obtain ⟨p, _, σ, hσ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hc
    obtain ⟨q, _, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hd
    rw [twoStepProjection_value hc, kpair.π₁_kpair] at hcg
    rw [twoStepProjection_value hd, kpair.π₁_kpair] at hdg
    rw [A.twoStepQuotientProjection_value h ⟨σ, h.name hσ⟩ hc hcg,
      A.twoStepQuotientProjection_value h ⟨τ, h.name hτ⟩ hd hdg]
    rintro ⟨x, hx, hxa, hxb⟩
    obtain ⟨r, hr, ν, he, hea, hev⟩ := A.twoStep_quotient_lift h ⟨σ, h.name hσ⟩ hc hcg hx hxa
    rw [← hev] at hxb
    obtain ⟨s, hs, hf, hfe, hfb⟩ := A.twoStep_quotient_refine h ν ⟨τ, h.name hτ⟩ he hr hd hdg hxb
    have hfa := (twoStep_preorder A.order A.top h).2.2 _ hf _ he _ hc hfe hea
    have hfq := (A.check_mem_projectionQuotient_iff (twoStepProjection_maps A.P A.R Q t)).mpr
      ⟨hf, by simpa only [twoStepProjection_value hf, kpair.π₁_kpair] using hs⟩
    refine ⟨A.check ⟨s, ν.val⟩ₖ, hfq, ?_, ?_⟩
    · exact (A.projectionQuotientOrder_pair_iff _ _ _ _ _).mpr
        ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr hfa, hfq, ha⟩
    · exact (A.projectionQuotientOrder_pair_iff _ _ _ _ _).mpr
        ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr hfb, hfq, hb⟩

end ForcingContext
end ZFVP




