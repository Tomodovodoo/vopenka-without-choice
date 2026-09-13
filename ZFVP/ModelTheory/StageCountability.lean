import ZFVP.ModelTheory.LevyGroundChange
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.CheckNames

/-! Nice names for subsets of a checked set: every subset of `Q̌` in an extension is the internal
value of a checked name from the ground set of names `℘ (Q̌-names × P)`, so the power set of `Q̌`
is bounded by that checked set. In the Levy extension of a measurable, the power sets of small
checked sets in a bounded stage are countable; in particular the reals of a stage are countable. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The check names of the members of `Q`. -/
noncomputable def checkNames (one Q : V) : V := repl (checkName one) (by definability) Q

theorem mem_checkNames_iff (one Q ν : V) : ν ∈ checkNames one Q ↔ ∃ q ∈ Q, ν = checkName one q :=
  repl_spec _

/-- The ground set of names for subsets of `Q̌`. -/
noncomputable def subsetNames (one Q P : V) : V := ℘ (checkNames one Q ×ˢ P)

theorem subsetNames_isName {one Q P τ : V} (hone : one ∈ P) (hτ : τ ∈ subsetNames one Q P) :
    IsForcingName P τ := by
  rw [forcingName_iff]
  intro z hz
  obtain ⟨ν, hν, p, hp, rfl⟩ := mem_prod_iff.mp (mem_power_iff.mp hτ z hz)
  obtain ⟨q, _, rfl⟩ := (mem_checkNames_iff _ _ _).mp hν
  exact ⟨checkName one q, p, hp, rfl, checkName_isName hone q⟩

/-- The canonical name of the intersection of the value of `σ` with `Q̌`. -/
noncomputable def memberName (P R one Q σ : V) : V :=
  {z ∈ checkNames one Q ×ˢ P ; ∃ q ∈ Q, kpair.π₁ z = checkName one q ∧
    ForcesCheckedMember P R one σ (kpair.π₂ z) q}

theorem memberName_mem_subsetNames (P R one Q σ : V) : memberName P R one Q σ ∈ subsetNames one Q P :=
  mem_power_iff.mpr sep_subset

theorem kpair_mem_memberName_iff (P R one Q σ ν p : V) :
    ⟨ν, p⟩ₖ ∈ memberName P R one Q σ ↔ (∃ m ∈ Q, ν = checkName one m) ∧ p ∈ P ∧
      ∃ q ∈ Q, ν = checkName one q ∧ ForcesCheckedMember P R one σ p q := by
  unfold memberName
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, mem_checkNames_iff, and_assoc]

theorem memberName_isName {P R one Q σ : V} (hone : one ∈ P) : IsForcingName P (memberName P R one Q σ) :=
  subsetNames_isName hone (memberName_mem_subsetNames P R one Q σ)

namespace ForcingContext

variable (S : ForcingContext V)

theorem ofName_memberName (σ : ForcingName S.P) (Q : V) :
    S.ofName ⟨memberName S.P S.R S.one Q σ.val, memberName_isName S.top.1⟩ = S.ofName σ ∩ S.check Q := by
  apply mem_ext
  intro z
  rw [mem_inter_iff, S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hp, hνp, rfl⟩
    obtain ⟨_, _, q, hq, hν, hforce⟩ := (kpair_mem_memberName_iff _ _ _ _ _ _ _).mp hνp
    have hν' : ν = ⟨checkName S.one q, checkName_isName S.top.1 q⟩ := Subtype.ext hν
    rw [hν']
    exact ⟨(S.checkedMember_truth σ q).mpr ⟨p, hp, hforce⟩, (S.check_mem_iff _ _).mpr hq⟩
  · rintro ⟨hz, hzQ⟩
    obtain ⟨q, hq, rfl⟩ := (S.mem_check_iff _ _).mp hzQ
    obtain ⟨p, hp, hforce⟩ := (S.checkedMember_truth σ q).mp hz
    refine ⟨⟨checkName S.one q, checkName_isName S.top.1 q⟩, p, hp, ?_, rfl⟩
    exact (kpair_mem_memberName_iff _ _ _ _ _ _ _).mpr ⟨⟨q, hq, rfl⟩, S.generic.1.1 p hp, q, hq, rfl, hforce⟩

/-- Every subset of `Q̌` is the internal value of a checked name from the ground name set. -/
theorem exists_subsetName {Q : V} {X : S.Model} (hX : X ⊆ S.check Q) :
    ∃ τ ∈ subsetNames S.one Q S.P, nameValue S.genericSet (S.check τ) = X := by
  obtain ⟨σ, rfl⟩ := S.ofName_surjective X
  refine ⟨memberName S.P S.R S.one Q σ.val, memberName_mem_subsetNames _ _ _ _ _, ?_⟩
  rw [S.nameValue_genericSet_check ⟨memberName S.P S.R S.one Q σ.val, memberName_isName S.top.1⟩,
    S.ofName_memberName]
  apply mem_ext
  intro z
  rw [mem_inter_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hX z h⟩⟩

/-- The values of checked names from the ground name set are subsets of `Q̌`. -/
theorem nameValue_subsetNames_subset {Q τ : V} (hτ : τ ∈ subsetNames S.one Q S.P) :
    nameValue S.genericSet (S.check τ) ⊆ S.check Q := by
  rw [S.nameValue_genericSet_check ⟨τ, subsetNames_isName S.top.1 hτ⟩]
  intro z hz
  obtain ⟨ν, p, _, hνp, rfl⟩ := (S.mem_ofName_iff _ _).mp hz
  obtain ⟨ν₀, hν₀, p₀, _, he⟩ := mem_prod_iff.mp (mem_power_iff.mp hτ _ hνp)
  obtain ⟨hν, _⟩ := kpair_iff.mp he
  obtain ⟨q, hq, rfl⟩ := (mem_checkNames_iff _ _ _).mp hν₀
  have hν' : ν = ⟨checkName S.one q, checkName_isName S.top.1 q⟩ := Subtype.ext hν
  rw [hν']
  exact (S.check_mem_iff _ _).mpr hq

/-- The power set of a checked set is bounded by the checked ground name set. -/
theorem power_check_cardLE (hAC : InternalChoice S.Model) (Q : V) :
    ℘ (S.check Q) ≤# S.check (subsetNames S.one Q S.P) := by
  have hF : ℒₛₑₜ-function₁ (fun τ : S.Model ↦ nameValue S.genericSet τ) := by definability
  let F := definableGraph (S.check (subsetNames S.one Q S.P)) (fun τ ↦ nameValue S.genericSet τ) hF
  have hFmem : F ∈ (℘ (S.check Q)) ^ (S.check (subsetNames S.one Q S.P)) := by
    apply definableGraph_mem_function_of_mapsTo
    intro τ hτ
    obtain ⟨τ₀, hτ₀, rfl⟩ := (S.mem_check_iff _ _).mp hτ
    exact mem_power_iff.mpr (S.nameValue_subsetNames_subset hτ₀)
  have hrange : range F = ℘ (S.check Q) := by
    apply SetTheory.subset_antisymm (range_subset_of_mem_function hFmem)
    intro X hX
    obtain ⟨τ, hτ, hval⟩ := S.exists_subsetName (mem_power_iff.mp hX)
    have hτ' : S.check τ ∈ S.check (subsetNames S.one Q S.P) := (S.check_mem_iff _ _).mpr hτ
    have := value_mem_range hFmem hτ'
    rwa [value_definableGraph _ _ hF hτ', hval] at this
  exact cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC _) hFmem hrange

end ForcingContext

/-- The check names of `Q` are no more numerous than `Q`. -/
theorem checkNames_cardLE (hAC : InternalChoice V) (one Q : V) : checkNames one Q ≤# Q := by
  have hF : ℒₛₑₜ-function₁ (checkName one) := by definability
  let F := definableGraph Q (checkName one) hF
  have hFmem : F ∈ (checkNames one Q) ^ Q :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun q hq ↦ (mem_checkNames_iff _ _ _).mpr ⟨q, hq, rfl⟩)
  have hrange : range F = checkNames one Q := by
    apply SetTheory.subset_antisymm (range_subset_of_mem_function hFmem)
    intro ν hν
    obtain ⟨q, hq, rfl⟩ := (mem_checkNames_iff _ _ _).mp hν
    have := value_mem_range hFmem hq
    rwa [value_definableGraph _ _ hF hq] at this
  exact cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC _) hFmem hrange

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (ξ : V) [IsOrdinal ξ] (hξ : ξ ∈ κ)

include hAC hU hc hω hξ in
/-- The ground name set for subsets of a small set over a small collapse is small. -/
theorem subsetNames_small {Q ν : V} (hQν : Q ≤# ν) (hν : ν ∈ κ) :
    ∃ μ ∈ κ, subsetNames (∅ : V) Q (levyCollapse ξ) ≤# μ := by
  obtain ⟨ν', hν', hcoll⟩ := levyCollapse_cardLE_small hAC hU hc hω hξ
  have : IsOrdinal ν := IsOrdinal.of_mem hν
  have : IsOrdinal ν' := IsOrdinal.of_mem hν'
  have hνν' : IsOrdinal (ν ∪ ν') := ordinal_union_isOrdinal ν ν'
  have hlam : (ν ∪ ν') ∪ (ω : V) ∈ κ := union_mem_of_ordinals (union_mem_of_ordinals hν hν') hω
  have h1 : checkNames (∅ : V) Q ×ˢ levyCollapse ξ ≤# (ν ∪ ν') ×ˢ (ν ∪ ν') :=
    prod_cardLE_prod ((checkNames_cardLE hAC ∅ Q).trans (hQν.trans (cardLE_of_subset (subset_union_left _ _))))
      (hcoll.trans (cardLE_of_subset (subset_union_right _ _)))
  have h2 : checkNames (∅ : V) Q ×ˢ levyCollapse ξ ≤# (ν ∪ ν') ∪ (ω : V) :=
    h1.trans (ordinal_prod_cardLE_union_omega (ν ∪ ν'))
  exact power_small_of_measurable hAC hU hc hlam h2

end

section

variable {A B : ForcingContext V} (L : ForcingRealization A B.Model)
  (hground : ∀ a : V, L.ground a = B.check a) (hAC' : InternalChoice A.Model)

include hground in
theorem value_cardLE_of_check {X : A.Model} {Y : V} (h : X ≤# A.check Y) : L.value X ≤# B.check Y := by
  have h2 := L.embedding.map_cardLE h
  rw [show L.embedding (A.check Y) = B.check Y from (L.value_check Y).trans (hground Y)] at h2
  exact h2

include hground hAC' in
/-- The image of the power set of a checked set is countable when the checked name set is. -/
theorem value_power_countable {Q : V}
    (hcount : IsInternallyCountable (B.check (subsetNames A.one Q A.P))) :
    IsInternallyCountable (L.value (℘ (A.check Q))) :=
  (value_cardLE_of_check L hground (A.power_check_cardLE hAC' Q)).trans hcount

include hground hAC' in
/-- The image of the reals of a realized extension is countable when the name set for subsets of
`ω × 2` is. -/
theorem value_cantorSpace_countable
    (hcount : IsInternallyCountable (B.check (subsetNames A.one ((ω : V) ×ˢ ((2 : ℕ) : V)) A.P))) :
    IsInternallyCountable (L.value (cantorSpace A.Model)) := by
  have hsub : cantorSpace A.Model ⊆ ℘ (A.check ((ω : V) ×ˢ ((2 : ℕ) : V))) := by
    intro x hx
    have hprod : A.check ((ω : V) ×ˢ ((2 : ℕ) : V)) = (ω : A.Model) ×ˢ ((2 : ℕ) : A.Model) := by
      have h := A.checkEmbedding.map_prod (ω : V) ((2 : ℕ) : V)
      change A.check _ = A.check _ ×ˢ A.check _ at h
      have h2 : A.check ((2 : ℕ) : V) = ((2 : ℕ) : A.Model) := A.checkEmbedding.map_numeral 2
      rw [h, A.check_omega_eq, h2]
    rw [hprod]
    exact mem_power_iff.mpr (subset_prod_of_mem_function hx)
  exact (cardLE_of_subset ((L.embedding.subset_iff _ _).mpr hsub)).trans
    (value_power_countable L hground hAC' hcount)

end

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (ξ : V) [IsOrdinal ξ] (hξ : ξ ∈ κ)

include hAC hU hc hω hκ hξ in
/-- The checked name set for subsets of a small set over a bounded stage is countable in `V[G]`. -/
theorem levy_subsetNames_countable {Q ν : V} (hQν : Q ≤# ν) (hν : ν ∈ κ) :
    IsInternallyCountable ((levyContext κ hG).check (subsetNames (∅ : V) Q (levyCollapse ξ))) := by
  obtain ⟨μ, hμ, hsmall⟩ := subsetNames_small hAC hU hc hω ξ hξ hQν hν
  exact ((levyContext κ hG).checkEmbedding.map_cardLE hsmall).trans (levy_check_countable hG hμ)

include hAC hU hc hω hκ in
/-- The power set of a small checked set in a bounded stage is countable in `V[G]`. -/
theorem stage_power_countable {Q ν : V} (hQν : Q ≤# ν) (hν : ν ∈ κ) :
    IsInternallyCountable ((levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value
      (℘ ((levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).check Q))) :=
  value_power_countable (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG)
    (levySubRealization_ground ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG)
    ((levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).internalChoice_of_ground hAC)
    (levy_subsetNames_countable hAC hU hc hω hκ hG ξ hξ hQν hν)

theorem omega_prod_two_cardLE : (ω : V) ×ˢ ((2 : ℕ) : V) ≤# (ω : V) := by
  refine (cardLE_of_subset ?_).trans ((ordinal_prod_cardLE_union_omega (ω : V)).trans ?_)
  · intro z hz
    obtain ⟨n, hn, i, hi, rfl⟩ := mem_prod_iff.mp hz
    exact kpair_mem_iff.mpr ⟨hn, IsTransitive.ω.transitive _ (ofNat_mem_ω 2) i hi⟩
  · apply cardLE_of_subset
    intro z hz
    rcases mem_union_iff.mp hz with h | h <;> exact h

include hAC hU hc hω hκ in
/-- The reals of a bounded stage are countable in `V[G]`. -/
theorem stage_reals_countable :
    IsInternallyCountable ((levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value
      (cantorSpace (levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).Model)) :=
  value_cantorSpace_countable (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG)
    (levySubRealization_ground ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG)
    ((levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).internalChoice_of_ground hAC)
    (levy_subsetNames_countable hAC hU hc hω hκ hG ξ hξ omega_prod_two_cardLE hω)

end

end ZFVP
