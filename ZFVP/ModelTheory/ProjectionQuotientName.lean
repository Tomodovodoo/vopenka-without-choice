import ZFVP.ModelTheory.ProjectionQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def projectionQuotientName (Q π one : V) : V :=
  repl (fun q ↦ (⟨checkName one q, π ‘ q⟩ₖ : V)) (by definability) Q

theorem mem_projectionQuotientName_iff (Q π one z : V) :
    z ∈ projectionQuotientName Q π one ↔ ∃ q ∈ Q, z = ⟨checkName one q, π ‘ q⟩ₖ := by
  simp only [projectionQuotientName, repl_spec]

instance projectionQuotientName_definable : ℒₛₑₜ-function₃[V] projectionQuotientName := by
  have h : ℒₛₑₜ-relation₄ (fun C Q π one : V ↦
      ∀ z, z ∈ C ↔ ∃ q ∈ Q, z = ⟨checkName one q, π ‘ q⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = projectionQuotientName (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [mem_projectionQuotientName_iff]

theorem projectionQuotientName_isName {P Q π one : V} (hone : one ∈ P) (hπ : π ∈ P ^ Q) :
    IsForcingName P (projectionQuotientName Q π one) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨q, hq, rfl⟩ := (mem_projectionQuotientName_iff _ _ _ _).mp hz
  exact ⟨checkName one q, π ‘ q, function_value_mem hπ hq, rfl, checkName_isName hone q⟩

theorem ForcingContext.ofName_projectionQuotient (A : ForcingContext V) {Q π : V}
    (hπ : π ∈ A.P ^ Q) :
    A.ofName ⟨projectionQuotientName Q π A.one, projectionQuotientName_isName A.top.1 hπ⟩ =
      A.projectionQuotient Q π := by
  apply SetTheory.mem_ext_iff.mpr
  intro x
  rw [A.mem_ofName_iff, A.mem_projectionQuotient_iff hπ]
  constructor
  · rintro ⟨ν, p, hp, hνp, hx⟩
    obtain ⟨q, hq, he⟩ := (mem_projectionQuotientName_iff _ _ _ _).mp hνp
    obtain ⟨hν, rfl⟩ := kpair_iff.mp he
    have hν' : ν = (⟨checkName A.one q, checkName_isName A.top.1 q⟩ : ForcingName A.P) :=
      Subtype.ext hν
    exact ⟨q, hq, hp, hx.trans (congrArg A.ofName hν')⟩
  · rintro ⟨q, hq, hp, hx⟩
    exact ⟨⟨checkName A.one q, checkName_isName A.top.1 q⟩, π ‘ q, hp,
      (mem_projectionQuotientName_iff _ _ _ _).mpr ⟨q, hq, rfl⟩, hx⟩

/-- An ordered pair is activated by the projection of its stronger coordinate. -/
noncomputable def projectionQuotientOrderName (S π one : V) : V :=
  repl (fun z ↦ (⟨checkName one z, π ‘ (kpair.π₁ z)⟩ₖ : V)) (by definability) S

theorem mem_projectionQuotientOrderName_iff (S π one z : V) :
    z ∈ projectionQuotientOrderName S π one ↔
      ∃ w ∈ S, z = ⟨checkName one w, π ‘ (kpair.π₁ w)⟩ₖ := by
  simp only [projectionQuotientOrderName, repl_spec]

instance projectionQuotientOrderName_definable : ℒₛₑₜ-function₃[V] projectionQuotientOrderName := by
  have h : ℒₛₑₜ-relation₄ (fun C S π one : V ↦
      ∀ z, z ∈ C ↔ ∃ w ∈ S, z = ⟨checkName one w, π ‘ (kpair.π₁ w)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = projectionQuotientOrderName (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [mem_projectionQuotientOrderName_iff]

theorem projectionQuotientOrderName_isName {P Q S π one : V} (hone : one ∈ P)
    (hπ : π ∈ P ^ Q) (hS : IsForcingPreorder Q S) :
    IsForcingName P (projectionQuotientOrderName S π one) := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨w, hw, rfl⟩ := (mem_projectionQuotientOrderName_iff _ _ _ _).mp hz
  obtain ⟨q, hq, r, _, rfl⟩ := mem_prod_iff.mp (hS.1 w hw)
  refine ⟨checkName one ⟨q, r⟩ₖ, π ‘ (kpair.π₁ ⟨q, r⟩ₖ), ?_, rfl, checkName_isName hone _⟩
  simpa using function_value_mem hπ hq

theorem ForcingContext.ofName_projectionQuotientOrder (A : ForcingContext V) {Q S π : V}
    (hπ : IsForcingProjection A.P A.R Q S π) (hS : IsForcingPreorder Q S) :
    A.ofName ⟨projectionQuotientOrderName S π A.one,
      projectionQuotientOrderName_isName A.top.1 hπ.maps hS⟩ =
      A.projectionQuotientOrder Q S π := by
  apply SetTheory.mem_ext_iff.mpr
  intro x
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hp, hνp, hx⟩
    obtain ⟨w, hw, he⟩ := (mem_projectionQuotientOrderName_iff _ _ _ _).mp hνp
    obtain ⟨hν, rfl⟩ := kpair_iff.mp he
    have hν' : ν = (⟨checkName A.one w, checkName_isName A.top.1 w⟩ : ForcingName A.P) :=
      Subtype.ext hν
    have hx' : x = A.check w := hx.trans (congrArg A.ofName hν')
    obtain ⟨q, hq, r, hr, rfl⟩ := mem_prod_iff.mp (hS.1 w hw)
    simp only [kpair.π₁_kpair] at hp
    rw [hx', A.check_kpair]
    apply (A.projectionQuotientOrder_pair_iff Q S π _ _).mpr
    refine ⟨A.check_kpair q r ▸ (A.check_mem_iff _ _).mpr hw,
      (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hq, hp⟩,
      (A.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hr, ?_⟩⟩
    exact A.generic.1.2.2.1 _ hp _ (function_value_mem hπ.maps hr)
      (hπ.monotone q hq r hr hw)
  · intro hx
    obtain ⟨hxS, hxprod⟩ := mem_sep_iff.mp hx
    obtain ⟨w, hw, rfl⟩ := (A.mem_check_iff S x).mp hxS
    obtain ⟨q, hq, r, _, rfl⟩ := mem_prod_iff.mp (hS.1 w hw)
    rw [A.check_kpair, kpair_mem_iff] at hxprod
    have hqG := ((A.check_mem_projectionQuotient_iff hπ.maps).mp hxprod.1).2
    refine ⟨⟨checkName A.one ⟨q, r⟩ₖ, checkName_isName A.top.1 _⟩, π ‘ q, hqG, ?_, rfl⟩
    apply (mem_projectionQuotientOrderName_iff _ _ _ _).mpr
    exact ⟨⟨q, r⟩ₖ, hw, by simp⟩

end ZFVP
