import ZFVP.SetTheory.BinaryExpansionReals
import ZFVP.SetTheory.DedekindRealTopology
import ZFVP.SetTheory.BaireCore

/-! Continuity of the actual binary map for internally coded open sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binaryPrefixEnds_inside {c a b : V} (hc : c ∈ cantorSpace V)
    (ha : a ∈ internalRationals V) (hb : b ∈ internalRationals V)
    (hx : binaryReal c ∈ realInterval a b) :
    ∃ n ∈ (ω : V), InternalRationalLT a (binaryValue c n) ∧
      InternalRationalLT (binaryUpper c n) b := by
  obtain ⟨hxCut, hax, hxb⟩ := (mem_realInterval_iff _ _ _).mp hx
  obtain ⟨_, k, hk, hak⟩ := (mem_binaryReal_iff c a).mp
    ((rationalCut_lt_iff_mem hxCut ha).mp hax)
  obtain ⟨r, hr, hxr, hrb⟩ := rationalCuts_dense hxCut (rationalCut_isCut hb) hxb
  let A : InternalRational V := ⟨a, ha⟩
  let B : InternalRational V := ⟨b, hb⟩
  let R : InternalRational V := ⟨r, hr⟩
  have hRB : R < B := (rationalCut_lt_iff hr hb).mp hrb
  obtain ⟨m, hm⟩ := InternalRational.exists_dyadic_lt (sub_pos.mpr hRB)
  let K : InternalNatural V := ⟨k, hk⟩
  let n : InternalNatural V := max K m
  have hLnR : InternalRational.binaryApprox c hc n ≤ R :=
    InternalRational.le_of_rationalCut_subset (subset_trans (binaryReal_lower n.property) hxr.1)
  have heps : InternalRational.dyadic n < B - R :=
    lt_of_le_of_lt (InternalRational.dyadic_antitone (le_max_right K m)) hm
  have hup : InternalRational.binaryApprox c hc n + InternalRational.dyadic n < B := by
    exact lt_of_le_of_lt (by simpa only [add_comm] using
      (add_le_add_right hLnR (InternalRational.dyadic n))) (by
      simpa only [add_comm] using (lt_sub_iff_add_lt).mp heps)
  have hlo : A < InternalRational.binaryApprox c hc n :=
    lt_of_lt_of_le (show A < InternalRational.binaryApprox c hc K from hak)
      (InternalRational.binaryApprox_mono c hc (le_max_left K m))
  exact ⟨n.val, n.property, hlo, hup⟩

theorem binaryReal_interval_of_prefix {c d a b n : V}
    (hc : c ∈ cantorSpace V) (hd : d ∈ cantorSpace V) (hn : n ∈ (ω : V))
    (ha : a ∈ internalRationals V) (hb : b ∈ internalRationals V)
    (hlo : InternalRationalLT a (binaryValue c n))
    (hup : InternalRationalLT (binaryUpper c n) b) (hp : c ↾ n ⊆ d) :
    binaryReal d ∈ realInterval a b := by
  have : IsFunction c := IsFunction.of_mem hc
  have : IsFunction d := IsFunction.of_mem hd
  have hagree : ∀ i ∈ n, c ‘ i = d ‘ i := by
    intro i hi
    have hiω := IsTransitive.ω.transitive n hn i hi
    exact (value_eq_of_kpair_mem (hp _ (kpair_mem_restrict_iff.mpr
      ⟨kpair_value_mem (by rwa [domain_eq_of_mem_function hc]), hi⟩))).symm
  have helo := binaryValue_eq_of_agree c d hn hagree
  have heup := binaryUpper_eq_of_agree c d hn hagree
  rw [helo] at hlo
  rw [heup] at hup
  exact (mem_realInterval_iff _ _ _).mpr ⟨binaryReal_isCut hd,
    dedekindLT_of_lt_of_subset ((rationalCut_lt_iff ha (binaryValue_mem hd hn)).mpr hlo)
      (binaryReal_lower hn),
    dedekindLT_of_subset_of_lt (binaryReal_upper hd hn)
      ((rationalCut_lt_iff (binaryUpper_mem hd hn) hb).mpr hup)⟩

def binaryPreimageFormula : SetTheorySemisentence 2 :=
  f“P U. ∀ c, c ∈ P ↔ c ∈ !cantorSpaceFormula ∧ !binaryRealFormula c ∈ U”

def binaryOpenPreimageCodeFormula : SetTheorySemisentence 2 :=
  f“S U. ∀ s, s ∈ S ↔ s ∈ !binarySequencesFormula ∧
    ∀ c ∈ !cantorSpaceFormula, s ⊆ c → !binaryRealFormula c ∈ U”

noncomputable def binaryPreimage (U : V) : V :=
  {c ∈ cantorSpace V ; binaryReal c ∈ U}

theorem mem_binaryPreimage_iff (U c : V) : c ∈ binaryPreimage U ↔
    c ∈ cantorSpace V ∧ binaryReal c ∈ U := by simp [binaryPreimage]

instance binaryPreimageFormula_defined : ℒₛₑₜ-function₁[V] binaryPreimage via binaryPreimageFormula :=
  ⟨fun v ↦ by simp [binaryPreimageFormula, mem_ext_iff (y := binaryPreimage _), mem_binaryPreimage_iff]⟩

instance binaryPreimage_definable : ℒₛₑₜ-function₁[V] binaryPreimage := binaryPreimageFormula_defined.to_definable

noncomputable def binaryOpenPreimageCode (U : V) : V :=
  {s ∈ binarySequences V ; ∀ c ∈ cantorSpace V, s ⊆ c → binaryReal c ∈ U}

theorem mem_binaryOpenPreimageCode_iff (U s : V) : s ∈ binaryOpenPreimageCode U ↔
    s ∈ binarySequences V ∧ ∀ c ∈ cantorSpace V, s ⊆ c → binaryReal c ∈ U := by
  simp [binaryOpenPreimageCode]

instance binaryOpenPreimageCodeFormula_defined :
    ℒₛₑₜ-function₁[V] binaryOpenPreimageCode via binaryOpenPreimageCodeFormula :=
  ⟨fun v ↦ by simp [binaryOpenPreimageCodeFormula,
    mem_ext_iff (y := binaryOpenPreimageCode _), mem_binaryOpenPreimageCode_iff]⟩

instance binaryOpenPreimageCode_definable : ℒₛₑₜ-function₁[V] binaryOpenPreimageCode :=
  binaryOpenPreimageCodeFormula_defined.to_definable

theorem binaryPreimage_eq_openFrom {U : V} (hU : IsRealOpen U) :
    binaryPreimage U = openFrom (binaryOpenPreimageCode U) := by
  apply mem_ext
  intro c
  rw [mem_binaryPreimage_iff, mem_openFrom_iff]
  constructor
  · rintro ⟨hc, hxc⟩
    obtain ⟨a, ha, b, hb, _, hxi, hiU⟩ := realOpen_neighborhood hU hxc
    obtain ⟨n, hn, hlo, hup⟩ := binaryPrefixEnds_inside hc ha hb hxi
    have hs := restrict_mem_binarySequences hc hn
    refine ⟨hc, c ↾ n, (mem_binaryOpenPreimageCode_iff _ _).mpr ⟨hs, ?_⟩,
      (subset_iff_restrict_eq hc hs).mp (restrict_subset c n)⟩
    intro d hd hsd
    exact hiU _ (binaryReal_interval_of_prefix hc hd hn ha hb hlo hup hsd)
  · rintro ⟨hc, s, hs, hsc⟩
    obtain ⟨hsB, hsU⟩ := (mem_binaryOpenPreimageCode_iff _ _).mp hs
    exact ⟨hc, hsU c hc ((subset_iff_restrict_eq hc hsB).mpr hsc)⟩

theorem binaryReal_continuous {U : V} (hU : IsRealOpen U) : IsOpen (binaryPreimage U) :=
  ⟨binaryOpenPreimageCode U,
    fun s hs ↦ ((mem_binaryOpenPreimageCode_iff U s).mp hs).1, binaryPreimage_eq_openFrom hU⟩

end ZFVP
