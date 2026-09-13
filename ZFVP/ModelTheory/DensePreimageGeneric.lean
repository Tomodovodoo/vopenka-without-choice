import ZFVP.ModelTheory.DenseEmbeddingTransfer

/-! Pulling a generic back along a dense embedding: the preimage of a `P'`-generic filter under a
dense embedding `e : P → P'` is `P`-generic, and its image filter recovers the original generic.
Hence an extension by `P'` is (up to a membership-preserving bijection fixing checks) an extension
by `P`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The preimage of a filter on `P'` under `e`. -/
def densePreimageFilter (P e : V) (G' : Set V) : Set V := {p | p ∈ P ∧ e ‘ p ∈ G'}

section

variable {P R P' R' e : V} {G' : Set V} (hR : IsForcingPreorder P R) (hR' : IsForcingPreorder P' R')
  (he : IsDenseEmbedding P R P' R' e) (hG' : IsExternalForcingGeneric P' R' G')

include hR hR' he hG' in
/-- Every generic on the target contains an image `e ‘ p` below any of its elements. -/
theorem exists_value_mem_below {p' : V} (hp' : p' ∈ G') : ∃ p ∈ P, e ‘ p ∈ G' ∧ ⟨e ‘ p, p'⟩ₖ ∈ R' := by
  have hp'P := hG'.1.1 p' hp'
  have hE : ForcingDense P' R' {q' ∈ P' ; ¬ForcingCompatible P' R' q' p' ∨
      ∃ p ∈ P, ⟨q', e ‘ p⟩ₖ ∈ R' ∧ ⟨e ‘ p, p'⟩ₖ ∈ R'} := by
    refine ⟨sep_subset, fun q' hq' ↦ ?_⟩
    by_cases hc : ForcingCompatible P' R' q' p'
    · obtain ⟨s', hs', hsq, hsp⟩ := hc
      obtain ⟨p, hp, hps⟩ := he.2.2.2 s' hs'
      refine ⟨e ‘ p, mem_sep_iff.mpr ⟨he.value_mem hp, Or.inr ⟨p, hp, hR'.2.1 _ (he.value_mem hp),
        hR'.2.2 _ (he.value_mem hp) s' hs' p' hp'P hps hsp⟩⟩, ?_⟩
      exact hR'.2.2 _ (he.value_mem hp) s' hs' q' hq' hps hsq
    · exact ⟨q', mem_sep_iff.mpr ⟨hq', Or.inl hc⟩, hR'.2.1 q' hq'⟩
  obtain ⟨g', hg', hgE⟩ := hG'.2 _ hE
  obtain ⟨hg'P, hcase⟩ := mem_sep_iff.mp hgE
  rcases hcase with hinc | ⟨p, hp, hgp, hpp'⟩
  · exfalso
    exact hinc (externalForcingFilter_compatible hG'.1 hg' hp')
  · exact ⟨p, hp, hG'.1.2.2.1 g' hg' _ (he.value_mem hp) hgp, hpp'⟩

include hR hR' he hG' in
/-- The preimage of a generic under a dense embedding is generic. -/
theorem densePreimageFilter_generic : IsExternalForcingGeneric P R (densePreimageFilter P e G') := by
  refine ⟨⟨fun p hp ↦ hp.1, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨p', hp'⟩ := hG'.1.2.1
    obtain ⟨p, hp, hpG, _⟩ := exists_value_mem_below hR hR' he hG' hp'
    exact ⟨p, hp, hpG⟩
  · rintro p ⟨hp, hpG⟩ q hq hpq
    exact ⟨hq, hG'.1.2.2.1 _ hpG _ (he.value_mem hq) (he.2.1 q hq p hp hpq)⟩
  · rintro p ⟨hp, hpG⟩ q ⟨hq, hqG⟩
    obtain ⟨r', hr', hrp, hrq⟩ := hG'.1.2.2.2 _ hpG _ hqG
    have hr'P := hG'.1.1 r' hr'
    have hE : ForcingDense P' R' {q' ∈ P' ; ¬ForcingCompatible P' R' q' r' ∨
        ∃ r ∈ P, ⟨r, p⟩ₖ ∈ R ∧ ⟨r, q⟩ₖ ∈ R ∧ ⟨q', e ‘ r⟩ₖ ∈ R'} := by
      refine ⟨sep_subset, fun q' hq' ↦ ?_⟩
      by_cases hc : ForcingCompatible P' R' q' r'
      · obtain ⟨s', hs', hsq, hsr⟩ := hc
        have hsp : ⟨s', e ‘ p⟩ₖ ∈ R' := hR'.2.2 s' hs' r' hr'P _ (he.value_mem hp) hsr hrp
        have hsq' : ⟨s', e ‘ q⟩ₖ ∈ R' := hR'.2.2 s' hs' r' hr'P _ (he.value_mem hq) hsr hrq
        obtain ⟨r₁, hr₁, hr₁p, hr₁s⟩ := he.exists_below hR hR' hp hs' hsp
        have hcomp : ForcingCompatible P' R' (e ‘ r₁) (e ‘ q) :=
          ⟨e ‘ r₁, he.value_mem hr₁, hR'.2.1 _ (he.value_mem hr₁),
            hR'.2.2 _ (he.value_mem hr₁) s' hs' _ (he.value_mem hq) hr₁s hsq'⟩
        obtain ⟨r, hr, hrr₁, hrq'⟩ := he.compatible_of_value hr₁ hq hcomp
        refine ⟨e ‘ r, mem_sep_iff.mpr ⟨he.value_mem hr, Or.inr ⟨r, hr, hR.2.2 r hr r₁ hr₁ p hp hrr₁ hr₁p,
          hrq', hR'.2.1 _ (he.value_mem hr)⟩⟩, ?_⟩
        exact hR'.2.2 _ (he.value_mem hr) s' hs' q' hq'
          (hR'.2.2 _ (he.value_mem hr) _ (he.value_mem hr₁) s' hs' (he.2.1 r₁ hr₁ r hr hrr₁) hr₁s) hsq
      · exact ⟨q', mem_sep_iff.mpr ⟨hq', Or.inl hc⟩, hR'.2.1 q' hq'⟩
    obtain ⟨g', hg', hgE⟩ := hG'.2 _ hE
    obtain ⟨_, hcase⟩ := mem_sep_iff.mp hgE
    rcases hcase with hinc | ⟨r, hr, hrp', hrq', hgr⟩
    · exact (hinc (externalForcingFilter_compatible hG'.1 hg' hr')).elim
    · exact ⟨r, ⟨hr, hG'.1.2.2.1 g' hg' _ (he.value_mem hr) hgr⟩, hrp', hrq'⟩
  · intro D hD
    have hD' : ForcingDense P' R' {q' ∈ P' ; ∃ d ∈ D, ⟨q', e ‘ d⟩ₖ ∈ R'} := by
      refine ⟨sep_subset, fun q' hq' ↦ ?_⟩
      obtain ⟨p, hp, hpq⟩ := he.2.2.2 q' hq'
      obtain ⟨d, hd, hdp⟩ := hD.2 p hp
      have hdP := hD.1 d hd
      refine ⟨e ‘ d, mem_sep_iff.mpr ⟨he.value_mem hdP, d, hd, hR'.2.1 _ (he.value_mem hdP)⟩, ?_⟩
      exact hR'.2.2 _ (he.value_mem hdP) _ (he.value_mem hp) q' hq' (he.2.1 p hp d hdP hdp) hpq
    obtain ⟨g', hg', hgD⟩ := hG'.2 _ hD'
    obtain ⟨_, d, hd, hgd⟩ := mem_sep_iff.mp hgD
    exact ⟨d, ⟨hD.1 d hd, hG'.1.2.2.1 g' hg' _ (he.value_mem (hD.1 d hd)) hgd⟩, hd⟩

include hR hR' he hG' in
/-- The image filter of the preimage is the original generic. -/
theorem denseImageFilter_densePreimage : denseImageFilter P' R' e (densePreimageFilter P e G') = G' := by
  ext p'
  constructor
  · rintro ⟨hp', p, ⟨hp, hpG⟩, hpp'⟩
    exact hG'.1.2.2.1 _ hpG p' hp' hpp'
  · intro hp'
    obtain ⟨p, hp, hpG, hpp'⟩ := exists_value_mem_below hR hR' he hG' hp'
    exact ⟨hG'.1.1 p' hp', p, ⟨hp, hpG⟩, hpp'⟩

end

namespace ForcingContext

theorem ext {A B : ForcingContext V} (hP : A.P = B.P) (hR : A.R = B.R) (hone : A.one = B.one)
    (hG : A.G = B.G) : A = B := by
  cases A
  cases B
  cases hP
  cases hR
  cases hone
  cases hG
  rfl

/-- Transport along an equality of contexts. -/
def modelCast {A B : ForcingContext V} (h : A = B) : A.Model ≃ B.Model :=
  Equiv.cast (congrArg ForcingContext.Model h)

theorem modelCast_mem_iff {A B : ForcingContext V} (h : A = B) (x y : A.Model) :
    modelCast h x ∈ modelCast h y ↔ x ∈ y := by
  subst h
  rfl

theorem modelCast_check {A B : ForcingContext V} (h : A = B) (a : V) :
    modelCast h (A.check a) = B.check a := by
  subst h
  rfl

variable (B : ForcingContext V) {P R one e : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  (he : IsDenseEmbedding P R B.P B.R e)

/-- The extension by the source of a dense embedding, with the pulled-back generic. -/
noncomputable def densePreimage : ForcingContext V where
  P := P
  R := R
  one := one
  G := densePreimageFilter P e B.G
  order := hR
  top := htop
  generic := densePreimageFilter_generic hR B.order he B.generic

theorem densePreimage_denseImage_eq :
    (B.densePreimage hR htop he).denseImage B.order B.top he = B :=
  ForcingContext.ext rfl rfl rfl (denseImageFilter_densePreimage hR B.order he B.generic)

/-- An extension by the target of a dense embedding is an extension by the source. -/
noncomputable def densePreimageEquiv : (B.densePreimage hR htop he).Model ≃ B.Model :=
  ((B.densePreimage hR htop he).denseEquiv B.order B.top he).trans
    (modelCast (B.densePreimage_denseImage_eq hR htop he))

theorem densePreimageEquiv_mem_iff (x y : (B.densePreimage hR htop he).Model) :
    B.densePreimageEquiv hR htop he x ∈ B.densePreimageEquiv hR htop he y ↔ x ∈ y := by
  unfold densePreimageEquiv
  rw [Equiv.trans_apply, Equiv.trans_apply, modelCast_mem_iff]
  exact (B.densePreimage hR htop he).denseEquiv_mem_iff B.order B.top he x y

theorem densePreimageEquiv_check (a : V) :
    B.densePreimageEquiv hR htop he ((B.densePreimage hR htop he).check a) = B.check a := by
  unfold densePreimageEquiv
  rw [Equiv.trans_apply, (B.densePreimage hR htop he).denseEquiv_check B.order B.top he, modelCast_check]

end ForcingContext

end ZFVP
