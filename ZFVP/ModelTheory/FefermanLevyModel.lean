import ZFVP.SetTheory.FefermanLevyNames
import ZFVP.ModelTheory.SymmetricModelZF
import ZFVP.ModelTheory.SymmetricModelOrdinals
import ZFVP.SetTheory.AtomicForcingAction
import ZFVP.SetTheory.EndExtensionCoding

/-! The Feferman-Levy symmetric extension. A hereditarily symmetric name is fixed by the
pointwise stabilizer of some stage; membership of check naturals in its value is then
decided by the restriction of conditions to that stage, so every real of the extension
is the value of a nice name of some stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def flContext (G : Set V) (hG : IsExternalForcingGeneric (flConditions V) (flOrder V) G) :
    SymmetricContext V where
  P := flConditions V
  R := flOrder V
  one := ∅
  G := G
  order := fl_poset.1
  top := fl_top
  generic := hG
  Γ := flGroup V
  F := flFilter V
  poset := fl_poset
  group := flGroup_group
  normal := flFilter_normal

/-- Decisions about check naturals in a name fixed by the stage-`n` stabilizer are made by
the restriction of a condition to the first `n` columns. -/
theorem fl_restrict_atomicMembership {n k τ p : V} (hn : n ∈ (ω : V))
    (hτ : IsForcingName (flConditions V) τ)
    (hsupp : ∀ σ ∈ pointwiseStabilizer (flGroup V) (flStage n), nameAction σ τ = τ)
    (hp : p ∈ atomicMembership (flConditions V) (flOrder V) (checkName ∅ k) τ) :
    p ↾ (n ×ˢ (ω : V)) ∈ atomicMembership (flConditions V) (flOrder V) (checkName ∅ k) τ := by
  classical
  have hR := fl_poset (V := V) |>.1
  have hpP : p ∈ flConditions V := atomicMembership_subset _ _ _ _ p hp
  have hpn := flRestrict_mem hpP n
  have hpnP : p ↾ (n ×ˢ (ω : V)) ∈ flConditions V := flStage_subset hn _ hpn
  by_contra hnot
  have hex : ∃ q ∈ flConditions V, ⟨q, p ↾ (n ×ˢ (ω : V))⟩ₖ ∈ flOrder V ∧
      ∀ r ∈ atomicMembership (flConditions V) (flOrder V) (checkName ∅ k) τ, ⟨r, q⟩ₖ ∉ flOrder V := by
    by_contra hall
    apply hnot
    apply atomicMembership_dense hR hpnP
    intro q hq hqp
    by_contra hno
    exact hall ⟨q, hq, hqp, fun r hr hrq ↦ hno ⟨r, hr, hrq⟩⟩
  obtain ⟨q, hq, hqp, hqbad⟩ := hex
  let X : V := {z ∈ domain p ; kpair.π₁ z ∉ n}
  obtain ⟨π, hπ, hfix, hmove⟩ := exists_columnPermutation_moving (n := n) (X := X) (Y := domain q)
    (internallyFinite_subset (flStage_finite_domain hpP) (fun z hz ↦ (mem_sep_iff.mp hz).1))
    (fun z hz ↦ flStage_domain hpP z (mem_sep_iff.mp hz).1) (fun z hz ↦ (mem_sep_iff.mp hz).2)
    (flStage_finite_domain hq)
  have hσ : flPermutation π ∈ pointwiseStabilizer (flGroup V) (flStage n) :=
    flPermutation_mem_stabilizer hn hπ hfix
  have hσG : flPermutation π ∈ flGroup V := ((mem_pointwiseStabilizer _ _ _).mp hσ).1
  have ha := flGroup_group.1 _ hσG
  have hσp : (flPermutation π) ‘ p ∈ atomicMembership (flConditions V) (flOrder V) (checkName ∅ k) τ := by
    have h := (atomicMembership_nameAction_iff ha (checkName_isName fl_top.1 k) hτ hpP).mpr hp
    rwa [flGroup_checkName hσG, hsupp _ hσ] at h
  have hσpP : (flPermutation π) ‘ p ∈ flConditions V := function_value_mem ha.1 hpP
  have hcompat : ForcingCompatible (flConditions V) (flOrder V) ((flPermutation π) ‘ p) q := by
    apply (fl_compatible_iff hσpP hq).mpr
    intro x y z hxy hxz
    rw [flPermutation_value hpP] at hxy
    have : IsFunction p := flStage_function hpP
    have : IsFunction q := flStage_function hq
    obtain ⟨u, huy, rfl⟩ := (pair_mem_permutedGraph π p x y).mp hxy
    have hud : u ∈ domain p := mem_domain_of_kpair_mem huy
    have huc : u ∈ columnCoordinates V := flStage_domain hpP u hud
    by_cases hun : kpair.π₁ u ∈ n
    · have hfixu : π ‘ u = u := hfix u huc hun
      rw [hfixu] at hxz
      have hun' : u ∈ n ×ˢ (ω : V) := by
        obtain ⟨m, hm, k', hk', rfl⟩ := mem_prod_iff.mp huc
        simp only [kpair.π₁_kpair] at hun
        exact kpair_mem_iff.mpr ⟨hun, hk'⟩
      have hres : ⟨u, y⟩ₖ ∈ p ↾ (n ×ˢ (ω : V)) := mem_restrict_iff.mpr ⟨huy, u, hun', y, rfl⟩
      have hq_sup : p ↾ (n ×ˢ (ω : V)) ⊆ q := ((pair_mem_flOrder _ _).mp hqp).2.2
      exact IsFunction.unique (hq_sup _ hres) hxz
    · have huX : u ∈ X := mem_sep_iff.mpr ⟨hud, hun⟩
      exact absurd (mem_domain_of_kpair_mem hxz) (hmove u huX)
  obtain ⟨r, hr, hrσp, hrq⟩ := hcompat
  exact hqbad r (atomicMembership_mono hR hσp hr hrσp) hrq

namespace FefermanLevyModel

variable {G : Set V} (hG : IsExternalForcingGeneric (flConditions V) (flOrder V) G)

/-- Every hereditarily symmetric name is fixed by the stabilizer of some stage. -/
theorem name_support (τ : (flContext G hG).Name) :
    ∃ n ∈ (ω : V), ∀ σ ∈ pointwiseStabilizer (flGroup V) (flStage n), nameAction σ τ.val = τ.val := by
  obtain ⟨_, n, hn, hnH⟩ := (mem_flFilter _).mp (hereditarilySymmetric_symmetric τ.property).2
  exact ⟨n, hn, fun σ hσ ↦ (mem_sep_iff.mp (hnH σ hσ)).2⟩

theorem check_mem_ofName_iff (τ : (flContext G hG).Name) (k : V) :
    (flContext G hG).check k ∈ (flContext G hG).ofName τ ↔
      GenericMeets G (atomicMembership (flConditions V) (flOrder V) (checkName ∅ k) τ.val) := by
  let S := flContext G hG
  rw [← S.toOrdinary_mem_iff]
  change S.toForcingContext.ofName ⟨checkName ∅ k, checkName_isName fl_top.1 k⟩ ∈
    S.toForcingContext.ofName ⟨τ.val, τ.property.1⟩ ↔ _
  exact forcingQuotientMk_mem_iff _ _ _ _ _ _ _

/-- Membership of check naturals is decided inside the support stage. -/
theorem check_mem_iff_stage (τ : (flContext G hG).Name) {n : V} (hn : n ∈ (ω : V))
    (hsupp : ∀ σ ∈ pointwiseStabilizer (flGroup V) (flStage n), nameAction σ τ.val = τ.val) (k : V) :
    (flContext G hG).check k ∈ (flContext G hG).ofName τ ↔
      ∃ q ∈ G, q ∈ flStage n ∧ q ∈ atomicMembership (flConditions V) (flOrder V) (checkName ∅ k) τ.val := by
  rw [check_mem_ofName_iff]
  constructor
  · rintro ⟨p, hpG, hp⟩
    have hpP : p ∈ flConditions V := hG.1.1 p hpG
    refine ⟨p ↾ (n ×ˢ (ω : V)), hG.1.2.2.1 p hpG _ (flStage_subset hn _ (flRestrict_mem hpP n))
      (flRestrict_le hpP hn), flRestrict_mem hpP n,
      fl_restrict_atomicMembership hn τ.property.1 hsupp hp⟩
  · rintro ⟨q, hqG, _, hq⟩
    exact ⟨q, hqG, hq⟩

/-- The nice name of stage `n` collecting the decisions about check naturals. -/
noncomputable def niceName (n τ : V) : V :=
  {z ∈ repl (fun z ↦ ⟨checkName ∅ (kpair.π₁ z), kpair.π₂ z⟩ₖ) (by definability) ((ω : V) ×ˢ flStage n) ;
    kpair.π₂ z ∈ atomicMembership (flConditions V) (flOrder V) (kpair.π₁ z) τ}

theorem pair_mem_niceName (n τ k q : V) :
    ⟨checkName ∅ k, q⟩ₖ ∈ niceName n τ ↔ k ∈ (ω : V) ∧ q ∈ flStage n ∧
      q ∈ atomicMembership (flConditions V) (flOrder V) (checkName ∅ k) τ := by
  simp only [niceName, mem_sep_iff, repl_spec, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨⟨u, hu, he⟩, hq⟩
    obtain ⟨k', hk', q', hq', rfl⟩ := mem_prod_iff.mp hu
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at he
    obtain ⟨hk, rfl⟩ := kpair_iff.mp he
    have hkk : k = k' := checkName_injective ∅ hk
    subst hkk
    exact ⟨hk', hq', hq⟩
  · rintro ⟨hk, hq, hforce⟩
    exact ⟨⟨⟨k, q⟩ₖ, kpair_mem_iff.mpr ⟨hk, hq⟩, by simp⟩, hforce⟩

theorem mem_niceName (n τ z : V) (hz : z ∈ niceName n τ) :
    ∃ k ∈ (ω : V), ∃ q ∈ flStage n, z = ⟨checkName ∅ k, q⟩ₖ := by
  obtain ⟨u, hu, rfl⟩ := (repl_spec _).mp (mem_sep_iff.mp hz).1
  obtain ⟨k, hk, q, hq, rfl⟩ := mem_prod_iff.mp hu
  exact ⟨k, hk, q, hq, by simp⟩

theorem niceName_mem_flNames {n : V} (hn : n ∈ (ω : V)) (τ : V) : niceName n τ ∈ flNames n :=
  (mem_flNames hn).mpr (fun z hz ↦ mem_niceName n τ z hz)

theorem niceName_hereditarilySymmetric {n : V} (hn : n ∈ (ω : V)) (τ : V) :
    IsHereditarilySymmetricName (flConditions V) (flGroup V) (flFilter V) (niceName n τ) :=
  flName_hereditarilySymmetric hn (niceName_mem_flNames hn τ)

/-- A real of the extension with stage-`n` support is the value of its nice name. -/
theorem ofName_niceName (τ : (flContext G hG).Name) {n : V} (hn : n ∈ (ω : V))
    (hsupp : ∀ σ ∈ pointwiseStabilizer (flGroup V) (flStage n), nameAction σ τ.val = τ.val)
    (hsub : (flContext G hG).ofName τ ⊆ (ω : (flContext G hG).Model)) :
    (flContext G hG).ofName ⟨niceName n τ.val, niceName_hereditarilySymmetric hn τ.val⟩ =
      (flContext G hG).ofName τ := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  apply S.extensionality
  intro x
  rw [S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, q, hqG, hνq, rfl⟩
    obtain ⟨k, hk, q', hq', he⟩ := mem_niceName n τ.val _ hνq
    obtain ⟨hν, rfl⟩ := kpair_iff.mp he
    have hνk : ν = ⟨checkName ∅ k, checkName_isName fl_top.1 k |> fun h ↦
        hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top k⟩ := Subtype.ext hν
    rw [hνk]
    change S.check k ∈ S.ofName τ
    rw [hν] at hνq
    obtain ⟨_, hqs, hforce⟩ := (pair_mem_niceName n τ.val k q).mp hνq
    exact (check_mem_iff_stage hG τ hn hsupp k).mpr ⟨q, hqG, hqs, hforce⟩
  · intro hx
    have hxω : x ∈ S.check (ω : V) := by rw [hω]; exact hsub x hx
    obtain ⟨k, hk, rfl⟩ := (S.mem_check_iff ω x).mp hxω
    obtain ⟨q, hqG, hqs, hforce⟩ := (check_mem_iff_stage hG τ hn hsupp k).mp hx
    exact ⟨⟨checkName ∅ k, hereditarilySymmetric_checkName fl_poset flGroup_group flFilter_normal fl_top k⟩,
      q, hqG, (pair_mem_niceName n τ.val k q).mpr ⟨hk, hqs, hforce⟩, rfl⟩

/-- The set of stage-`n` reals. -/
noncomputable def stageSet {n : V} (hn : n ∈ (ω : V)) : (flContext G hG).Model :=
  (flContext G hG).ofName ⟨flStageName n, flStageName_hereditarilySymmetric hn⟩

theorem mem_stageSet_iff {n : V} (hn : n ∈ (ω : V)) (x : (flContext G hG).Model) :
    x ∈ stageSet hG hn ↔ ∃ τ : V, ∃ hτ : τ ∈ flNames n,
      x = (flContext G hG).ofName ⟨τ, flName_hereditarilySymmetric hn hτ⟩ := by
  let S := flContext G hG
  rw [stageSet, S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, _, hνp, rfl⟩
    obtain ⟨τ, hτ, he⟩ := (mem_flStageName n _).mp hνp
    have hν : ν = ⟨τ, flName_hereditarilySymmetric hn hτ⟩ := Subtype.ext (kpair_iff.mp he).1
    exact ⟨τ, hτ, congrArg S.ofName hν⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, flName_hereditarilySymmetric hn hτ⟩, ∅, externalForcingFilter_top hG.1 fl_top,
      (mem_flStageName n _).mpr ⟨τ, hτ, rfl⟩, rfl⟩

/-- Values of stage names are sets of naturals. -/
theorem ofName_flName_subset_omega {n τ : V} (hn : n ∈ (ω : V)) (hτ : τ ∈ flNames n) :
    (flContext G hG).ofName ⟨τ, flName_hereditarilySymmetric hn hτ⟩ ⊆ (ω : (flContext G hG).Model) := by
  let S := flContext G hG
  have hω : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  intro x hx
  obtain ⟨ν, q, _, hνq, rfl⟩ := (S.mem_ofName_iff _ x).mp hx
  obtain ⟨k, hk, q', _, he⟩ := (mem_flNames hn).mp hτ _ hνq
  have hν : ν.val = checkName ∅ k := (kpair_iff.mp he).1
  have : S.ofName ν = S.check k := congrArg S.ofName (Subtype.ext hν)
  rw [this, ← hω]
  exact (S.check_mem_iff k ω).mpr hk

/-- Every real of the extension lies in some stage set. -/
theorem real_mem_stageSet (x : (flContext G hG).Model) (hx : x ⊆ (ω : (flContext G hG).Model)) :
    ∃ n : V, ∃ hn : n ∈ (ω : V), x ∈ stageSet hG hn := by
  let S := flContext G hG
  obtain ⟨τ, rfl⟩ := S.ofName_surjective x
  obtain ⟨n, hn, hsupp⟩ := name_support hG τ
  refine ⟨n, hn, (mem_stageSet_iff hG hn _).mpr ⟨niceName n τ.val, niceName_mem_flNames hn τ.val, ?_⟩⟩
  exact (ofName_niceName hG τ hn hsupp hx).symm

end FefermanLevyModel
end ZFVP
