import ZFVP.SetTheory.ForcedStabilizerFilter
import ZFVP.SetTheory.CheckNames
import ZFVP.SetTheory.NameActionClosure
import ZFVP.SetTheory.AtomicCheckNames
import ZFVP.SetTheory.AtomicForcingSubstitution
import ZFVP.SetTheory.HereditarySymmetry

/-! Saturated nice names `{⟨ǩ, p⟩ : k ∈ K, p ⊩ ǩ ∈ τ}` for subsets of a ground set `K`. They are
fixed syntactically by every automorphism fixing them up to forced equality, the class is closed
under automorphisms, and they are hereditarily symmetric for the forced-stabilizer filter they
generate: the class name `Ṙ_can` of Karagila–Schilhan realized by nice names. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The nice name with codes in `K` attached to `τ`: `{⟨ǩ, p⟩ : k ∈ K, p ⊩ ǩ ∈ τ}`. -/
noncomputable def niceName (P R one K τ : V) : V :=
  sep ((repl (checkName one) (by definability) K) ×ˢ P)
    (fun z ↦ kpair.π₂ z ∈ atomicMembership P R (kpair.π₁ z) τ)
    (by have := atomicMembership_definable P R; definability)

theorem mem_niceName_iff (P R one K τ z : V) :
    z ∈ niceName P R one K τ ↔ ∃ k ∈ K, ∃ p ∈ P, z = ⟨checkName one k, p⟩ₖ ∧
      p ∈ atomicMembership P R (checkName one k) τ := by
  unfold niceName
  rw [mem_sep_iff, mem_prod_iff]
  constructor
  · rintro ⟨⟨σ, hσ, p, hp, rfl⟩, h⟩
    obtain ⟨k, hk, rfl⟩ := (repl_spec (by definability)).mp hσ
    rw [kpair.π₁_kpair, kpair.π₂_kpair] at h
    exact ⟨k, hk, p, hp, rfl, h⟩
  · rintro ⟨k, hk, p, hp, rfl, h⟩
    refine ⟨⟨_, (repl_spec (by definability)).mpr ⟨k, hk, rfl⟩, p, hp, rfl⟩, ?_⟩
    rw [kpair.π₁_kpair, kpair.π₂_kpair]
    exact h

theorem niceName_definable_one (P R one K : V) : ℒₛₑₜ-function₁[V] (niceName P R one K) := by
  have h : ℒₛₑₜ-relation[V] (fun ν τ ↦ ∀ z, z ∈ ν ↔ ∃ k ∈ K, ∃ p ∈ P, z = ⟨checkName one k, p⟩ₖ ∧
      p ∈ atomicMembership P R (checkName one k) τ) := by
    have := atomicMembership_definable P R
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = niceName P R one K (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_niceName_iff]

/-- Names all of whose members are `⟨ǩ, p⟩` with `k ∈ K`. -/
def IsNiceName (P one K τ : V) : Prop := ∀ z ∈ τ, ∃ k ∈ K, ∃ p ∈ P, z = ⟨checkName one k, p⟩ₖ

instance isNiceName_definable : ℒₛₑₜ-relation₄[V] IsNiceName := by
  unfold IsNiceName
  definability

theorem IsNiceName.isName {P one K τ : V} (hone : one ∈ P) (h : IsNiceName P one K τ) :
    IsForcingName P τ :=
  (forcingName_iff P τ).mpr fun z hz ↦ by
    obtain ⟨k, _, p, hp, rfl⟩ := h z hz
    exact ⟨_, p, hp, rfl, checkName_isName hone k⟩

theorem niceName_nice (P R one K τ : V) : IsNiceName P one K (niceName P R one K τ) := by
  intro z hz
  obtain ⟨k, hk, p, hp, rfl, _⟩ := (mem_niceName_iff _ _ _ _ _ _).mp hz
  exact ⟨k, hk, p, hp, rfl⟩

theorem niceName_isName {P one : V} (R K τ : V) (hone : one ∈ P) :
    IsForcingName P (niceName P R one K τ) :=
  (niceName_nice P R one K τ).isName hone

/-- The nice name has the same membership forcing as `τ` at every code. -/
theorem atomicMembership_niceName {P R one K k : V} (hR : IsForcingPreorder P R)
    (hone : IsForcingTop P R one) (hk : k ∈ K) (τ : V) :
    atomicMembership P R (checkName one k) (niceName P R one K τ) =
      atomicMembership P R (checkName one k) τ := by
  ext p
  constructor
  · intro hp
    have hpP : p ∈ P := atomicMembership_subset _ _ _ _ p hp
    apply atomicMembership_dense hR hpP
    intro q hq hqp
    obtain ⟨_, ht⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
    obtain ⟨r, hr, hrq, ν, s, hνs, hrs, hrE⟩ := ht q hq hqp
    obtain ⟨j, _, s', _, hz, hs⟩ := (mem_niceName_iff _ _ _ _ _ _).mp hνs
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hz
    have hkj := atomicEquality_checkName_injective hR hone k j r hrE
    subst hkj
    exact ⟨r, atomicMembership_mono hR hs hr hrs, hrq⟩
  · intro hp
    have hpP : p ∈ P := atomicMembership_subset _ _ _ _ p hp
    refine (mem_atomicMembership_iff _ _ _ _ _).mpr ⟨hpP, fun q hq hqp ↦ ?_⟩
    refine ⟨q, hq, hR.2.1 q hq, checkName one k, p, ?_, hqp, ?_⟩
    · exact (mem_niceName_iff _ _ _ _ _ _).mpr ⟨k, hk, p, hpP, rfl, hp⟩
    · rw [atomicEquality_refl hR]
      exact hq

/-- Saturated nice names: fixed points of the nice-name operator. -/
def IsSaturatedNiceName (P R one K τ : V) : Prop := τ = niceName P R one K τ

theorem isSaturatedNiceName_definable (P R one K : V) :
    ℒₛₑₜ-predicate[V] (IsSaturatedNiceName P R one K) := by
  unfold IsSaturatedNiceName
  have := niceName_definable_one P R one K
  definability

theorem IsSaturatedNiceName.isName {P R one K τ : V} (hone : one ∈ P)
    (h : IsSaturatedNiceName P R one K τ) : IsForcingName P τ := by
  rw [h]
  exact niceName_isName R K τ hone

theorem IsSaturatedNiceName.nice {P R one K τ : V} (h : IsSaturatedNiceName P R one K τ) :
    IsNiceName P one K τ := by
  rw [h]
  exact niceName_nice P R one K τ

/-- The nice name of any name is saturated. -/
theorem niceName_saturated {P R one K : V} (hR : IsForcingPreorder P R) (hone : IsForcingTop P R one)
    (τ : V) : IsSaturatedNiceName P R one K (niceName P R one K τ) := by
  unfold IsSaturatedNiceName
  ext z
  simp only [mem_niceName_iff]
  constructor
  · rintro ⟨k, hk, p, hp, rfl, h⟩
    exact ⟨k, hk, p, hp, rfl, by rw [atomicMembership_niceName hR hone hk]; exact h⟩
  · rintro ⟨k, hk, p, hp, rfl, h⟩
    rw [atomicMembership_niceName hR hone hk] at h
    exact ⟨k, hk, p, hp, rfl, h⟩

/-- Automorphisms commute with the nice-name operator. -/
theorem nameAction_niceName {P R one K π : V} (hR : IsForcingPoset P R) (hone : IsForcingTop P R one)
    (hπ : IsForcingAutomorphism P R π) {τ : V} (hτ : IsForcingName P τ) :
    nameAction π (niceName P R one K τ) = niceName P R one K (nameAction π τ) := by
  have hfix : π ‘ one = one := forcingAutomorphism_top hR hone hπ
  ext z
  rw [mem_nameAction_iff (niceName_isName R K τ hone.1), mem_niceName_iff]
  constructor
  · rintro ⟨σ, p, hσp, rfl⟩
    obtain ⟨k, hk, p', hp', hz, hp⟩ := (mem_niceName_iff _ _ _ _ _ _).mp hσp
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp hz
    refine ⟨k, hk, π ‘ p, function_value_mem hπ.1 hp', ?_, ?_⟩
    · rw [nameAction_checkName hone.1 hfix]
    · rw [← nameAction_checkName hone.1 hfix k]
      exact (atomicMembership_nameAction_iff hπ (checkName_isName hone.1 k) hτ hp').mpr hp
  · rintro ⟨k, hk, q, hq, rfl, hqm⟩
    obtain ⟨p, hp, rfl⟩ := forcingAutomorphism_surjective hπ q hq
    refine ⟨checkName one k, p, ?_, by rw [nameAction_checkName hone.1 hfix]⟩
    refine (mem_niceName_iff _ _ _ _ _ _).mpr ⟨k, hk, p, hp, rfl, ?_⟩
    rw [← nameAction_checkName hone.1 hfix k] at hqm
    exact (atomicMembership_nameAction_iff hπ (checkName_isName hone.1 k) hτ hp).mp hqm

theorem saturatedNiceName_nameAction {P R one K π τ : V} (hR : IsForcingPoset P R)
    (hone : IsForcingTop P R one) (hπ : IsForcingAutomorphism P R π)
    (h : IsSaturatedNiceName P R one K τ) : IsSaturatedNiceName P R one K (nameAction π τ) := by
  have hτ := h.isName hone.1
  unfold IsSaturatedNiceName
  conv_lhs => rw [h]
  rw [nameAction_niceName hR hone hπ hτ]

/-- An automorphism fixing a saturated nice name up to forced equality fixes it syntactically. -/
theorem saturatedNiceName_fixed_of_forcedEqual {P R one K π τ : V} (hR : IsForcingPoset P R)
    (hone : IsForcingTop P R one) (hπ : IsForcingAutomorphism P R π)
    (h : IsSaturatedNiceName P R one K τ) (he : ForcedEqual P R (nameAction π τ) τ) :
    nameAction π τ = τ := by
  have hτ := h.isName hone.1
  have hm : ∀ k ∈ K, atomicMembership P R (checkName one k) (nameAction π τ) =
      atomicMembership P R (checkName one k) τ := by
    intro k _
    ext p
    constructor
    · intro hp
      exact ((atomicEquality_membership_iff hR.1 (he p (atomicMembership_subset _ _ _ _ p hp)) _).2).mp hp
    · intro hp
      exact ((atomicEquality_membership_iff hR.1 (he p (atomicMembership_subset _ _ _ _ p hp)) _).2).mpr hp
  have h1 : nameAction π τ = niceName P R one K (nameAction π τ) := by
    conv_lhs => rw [h]
    rw [nameAction_niceName hR hone hπ hτ]
  rw [h1]
  conv_rhs => rw [h]
  ext z
  simp only [mem_niceName_iff]
  constructor
  · rintro ⟨k, hk, p, hp, rfl, hpm⟩
    exact ⟨k, hk, p, hp, rfl, by rw [← hm k hk]; exact hpm⟩
  · rintro ⟨k, hk, p, hp, rfl, hpm⟩
    exact ⟨k, hk, p, hp, rfl, by rw [hm k hk]; exact hpm⟩

/-- The forced stabilizer of a saturated nice name is contained in its syntactic stabilizer. -/
theorem forcedStabilizer_subset_nameStabilizer {P R Γ one K τ : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one)
    (h : IsSaturatedNiceName P R one K τ) :
    forcedStabilizer P R Γ ({τ} : V) ⊆ nameStabilizer Γ τ := by
  intro π hπ
  obtain ⟨hπΓ, hfix⟩ := (mem_forcedStabilizer _ _ _ _ _).mp hπ
  exact mem_sep_iff.mpr ⟨hπΓ,
    saturatedNiceName_fixed_of_forcedEqual hR hone (hΓ.1 π hπΓ) h (hfix τ (mem_singleton_iff.mpr rfl))⟩

/-- The filter generated by forced stabilizers of finitely many saturated nice names. -/
noncomputable def niceNameFilter (P R Γ one K : V) : V :=
  forcedStabilizerFilter P R Γ (IsSaturatedNiceName P R one K) (isSaturatedNiceName_definable P R one K)

theorem niceNameFilter_normal {P R Γ one K : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one) :
    IsNormalSubgroupFilter P Γ (niceNameFilter P R Γ one K) :=
  forcedStabilizerFilter_normal hR.1 hΓ _ (fun _ h ↦ h.isName hone.1)
    (fun π hπ _ h ↦ saturatedNiceName_nameAction hR hone (hΓ.1 π hπ) h)

/-- Saturated nice names are hereditarily symmetric for the nice-name filter. -/
theorem saturatedNiceName_hereditarilySymmetric {P R Γ one K τ : V} (hR : IsForcingPoset P R)
    (hΓ : IsForcingAutomorphismGroup P R Γ) (hone : IsForcingTop P R one)
    (h : IsSaturatedNiceName P R one K τ) :
    IsHereditarilySymmetricName P Γ (niceNameFilter P R Γ one K) τ := by
  have hF := niceNameFilter_normal (K := K) hR hΓ hone
  rw [hereditarilySymmetric_iff]
  refine ⟨⟨h.isName hone.1, ?_⟩, ?_⟩
  · have hmem : forcedStabilizer P R Γ ({τ} : V) ∈ niceNameFilter P R Γ one K :=
      forcedStabilizer_mem_forcedStabilizerFilter hR.1 hΓ _ (fun _ h ↦ h.isName hone.1)
        (by
          have h1 := internallyFinite_insert (internallyFinite_empty (V := V)) τ
          rwa [show insert τ (∅ : V) = {τ} by ext; simp] at h1)
        (fun σ hσ ↦ by rw [mem_singleton_iff.mp hσ]; exact h)
    exact hF.2.2.1 _ hmem _ (nameStabilizer_subgroup hΓ (h.isName hone.1))
      (forcedStabilizer_subset_nameStabilizer hR hΓ hone h)
  · intro σ p hσp
    obtain ⟨k, _, p', _, hz⟩ := h.nice _ hσp
    rw [(kpair_iff.mp hz).1]
    exact hereditarilySymmetric_checkName hR hΓ hF hone k

end ZFVP
