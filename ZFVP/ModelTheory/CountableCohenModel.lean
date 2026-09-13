import ZFVP.SetTheory.CountableCohenNames
import ZFVP.ModelTheory.SymmetricModelZF

/-! The countable-support Cohen symmetric extension at the first uncountable ordinal:
rows and columns are both indexed by `hartogsNumber ω`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem zero_mem_hartogs_omega : (0 : V) ∈ hartogsNumber (ω : V) :=
  IsOrdinal.toIsTransitive.mem_trans (by simp) omega_mem_hartogs_omega

noncomputable def omegaOneCohenContext (G : Set V)
    (hG : IsExternalForcingGeneric (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
      (countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) G) : SymmetricContext V where
  P := countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V))
  R := countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))
  G := G
  order := (countableCohen_poset _ _).1
  generic := hG
  one := ∅
  top := countableCohen_top _ _
  Γ := countableCohenGroup (hartogsNumber (ω : V)) (hartogsNumber (ω : V))
  F := countableCohenFilter (hartogsNumber (ω : V)) (hartogsNumber (ω : V))
  poset := countableCohen_poset _ _
  group := countableCohenGroup_group _ _
  normal := countableCohenFilter_normal _ _

namespace OmegaOneCohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
    (countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) G)

noncomputable def subsetName (ξ : V) (hξ : ξ ∈ hartogsNumber (ω : V)) : (omegaOneCohenContext G hG).Name :=
  ⟨countableCohenSubsetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) ξ,
    countableCohenSubsetName_hereditarilySymmetric hξ zero_mem_hartogs_omega⟩

noncomputable def subset (ξ : V) (hξ : ξ ∈ hartogsNumber (ω : V)) : (omegaOneCohenContext G hG).Model :=
  (omegaOneCohenContext G hG).ofName (subsetName hG ξ hξ)

noncomputable def subsetsName : (omegaOneCohenContext G hG).Name :=
  ⟨countableCohenSetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)),
    countableCohenSetName_hereditarilySymmetric _ _ zero_mem_hartogs_omega⟩

noncomputable def subsets : (omegaOneCohenContext G hG).Model :=
  (omegaOneCohenContext G hG).ofName (subsetsName hG)

theorem mem_subset_iff (ξ : V) (hξ : ξ ∈ hartogsNumber (ω : V)) (x : (omegaOneCohenContext G hG).Model) :
    x ∈ subset hG ξ hξ ↔ ∃ n ∈ hartogsNumber (ω : V), ∃ p ∈ G,
      ⟨⟨ξ, n⟩ₖ, (1 : V)⟩ₖ ∈ p ∧ x = (omegaOneCohenContext G hG).check n := by
  let S := omegaOneCohenContext G hG
  rw [subset, S.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, hx⟩
    obtain ⟨_, n, hn, hσ, hb⟩ := (pair_mem_countableCohenSubsetName _ _ ξ σ.val p).mp hσp
    have he : S.ofName σ = S.check n := congrArg S.ofName (Subtype.ext hσ)
    exact ⟨n, hn, p, hp, hb, hx.trans he⟩
  · rintro ⟨n, hn, p, hp, hb, rfl⟩
    refine ⟨⟨checkName ∅ n, hereditarilySymmetric_checkName (countableCohen_poset _ _)
      (countableCohenGroup_group _ _) (countableCohenFilter_normal _ _) (countableCohen_top _ _) n⟩,
      p, hp, ?_, rfl⟩
    exact (pair_mem_countableCohenSubsetName _ _ ξ _ p).mpr ⟨hG.1.1 p hp, n, hn, rfl, hb⟩

theorem check_mem_subset_iff {ξ n : V} (hξ : ξ ∈ hartogsNumber (ω : V)) :
    (omegaOneCohenContext G hG).check n ∈ subset hG ξ hξ ↔
      n ∈ hartogsNumber (ω : V) ∧ ∃ p ∈ G, ⟨⟨ξ, n⟩ₖ, (1 : V)⟩ₖ ∈ p := by
  rw [mem_subset_iff]
  constructor
  · rintro ⟨m, hm, p, hp, hb, he⟩
    obtain rfl := ((omegaOneCohenContext G hG).check_eq_iff n m).mp he
    exact ⟨hm, p, hp, hb⟩
  · rintro ⟨hn, p, hp, hb⟩
    exact ⟨n, hn, p, hp, hb, rfl⟩

theorem mem_subsets_iff (x : (omegaOneCohenContext G hG).Model) :
    x ∈ subsets hG ↔ ∃ ξ : V, ∃ hξ : ξ ∈ hartogsNumber (ω : V), x = subset hG ξ hξ := by
  let S := omegaOneCohenContext G hG
  rw [subsets, S.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, hx⟩
    obtain ⟨ξ, hξ, he⟩ := (mem_countableCohenSetName _ _ _).mp hσp
    have he' : S.ofName σ = subset hG ξ hξ := congrArg S.ofName (Subtype.ext (kpair_iff.mp he).1)
    exact ⟨ξ, hξ, hx.trans he'⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨subsetName hG ξ hξ, ∅, externalForcingFilter_top hG.1 (countableCohen_top _ _),
      (mem_countableCohenSetName _ _ _).mpr ⟨ξ, hξ, rfl⟩, rfl⟩

theorem check_not_mem_subset_of_zero {ξ n p : V} (hξ : ξ ∈ hartogsNumber (ω : V)) (hp : p ∈ G)
    (hb : ⟨⟨ξ, n⟩ₖ, (0 : V)⟩ₖ ∈ p) : (omegaOneCohenContext G hG).check n ∉ subset hG ξ hξ := by
  intro hm
  obtain ⟨_, q, hq, hqbit⟩ := (check_mem_subset_iff hG hξ).mp hm
  have hc := (countablePartialFunctions_compatible_iff (hG.1.1 p hp) (hG.1.1 q hq)).mp
    (externalForcingFilter_compatible hG.1 hp hq)
  have h01 := hc ⟨ξ, n⟩ₖ 0 1 hb hqbit
  simp at h01

theorem subset_ne {ξ ζ : V} (hξ : ξ ∈ hartogsNumber (ω : V)) (hζ : ζ ∈ hartogsNumber (ω : V))
    (hne : ξ ≠ ζ) : subset hG ξ hξ ≠ subset hG ζ hζ := by
  obtain ⟨p, hp, hpd⟩ := hG.2 _ (countableCohen_separate_rows_dense hξ hζ hne)
  obtain ⟨_, n, hn, hb0, hb1⟩ := mem_sep_iff.mp hpd
  intro he
  have hnmem := (check_mem_subset_iff hG hζ).mpr ⟨hn, p, hp, hb1⟩
  exact check_not_mem_subset_of_zero hG hξ hp hb0 (he.symm ▸ hnmem)

theorem subset_eq_iff {ξ ζ : V} (hξ : ξ ∈ hartogsNumber (ω : V)) (hζ : ζ ∈ hartogsNumber (ω : V)) :
    subset hG ξ hξ = subset hG ζ hζ ↔ ξ = ζ := by
  constructor
  · intro he
    by_contra hn
    exact subset_ne hG hξ hζ hn he
  · rintro rfl
    rfl

end OmegaOneCohenModel
end ZFVP
