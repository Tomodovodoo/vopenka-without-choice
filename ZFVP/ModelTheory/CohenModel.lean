import ZFVP.SetTheory.CohenSetName
import ZFVP.ModelTheory.SymmetricModelZF

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def cohenContext (I : V) (G : Set V)
    (hG : IsExternalForcingGeneric (cohenConditions I) (cohenOrder I) G) : SymmetricContext V where
  P := cohenConditions I
  R := cohenOrder I
  G := G
  order := (cohen_poset I).1
  generic := hG
  one := ∅
  top := cohen_top I
  Γ := cohenGroup I
  F := cohenFilter I
  poset := cohen_poset I
  group := cohenGroup_group I
  normal := cohenFilter_normal I

namespace CohenModel

variable {I : V} {G : Set V} (hG : IsExternalForcingGeneric (cohenConditions I) (cohenOrder I) G)

noncomputable def real (i : V) (hi : i ∈ I) : (cohenContext I G hG).Model :=
  (cohenContext I G hG).ofName ⟨cohenRealName I i, cohenRealName_hereditarilySymmetric hi⟩

noncomputable def reals : (cohenContext I G hG).Model :=
  (cohenContext I G hG).ofName ⟨cohenSetName I, cohenSetName_hereditarilySymmetric I⟩

theorem mem_real_iff (i : V) (hi : i ∈ I) (x : (cohenContext I G hG).Model) :
    x ∈ real hG i hi ↔ ∃ n ∈ (ω : V), ∃ p ∈ G,
      ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ p ∧ x = (cohenContext I G hG).check n := by
  let S := cohenContext I G hG
  rw [real, S.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, hx⟩
    obtain ⟨_, n, hn, hσ, hb⟩ := (pair_mem_cohenRealName I i σ.val p).mp hσp
    have he : S.ofName σ = S.check n := congrArg S.ofName (Subtype.ext hσ)
    exact ⟨n, hn, p, hp, hb, hx.trans he⟩
  · rintro ⟨n, hn, p, hp, hb, rfl⟩
    refine ⟨⟨checkName ∅ n, hereditarilySymmetric_checkName (cohen_poset I)
      (cohenGroup_group I) (cohenFilter_normal I) (cohen_top I) n⟩, p, hp, ?_, rfl⟩
    exact (pair_mem_cohenRealName I i _ p).mpr ⟨hG.1.1 p hp, n, hn, rfl, hb⟩

theorem check_mem_real_iff {i n : V} (hi : i ∈ I) :
    (cohenContext I G hG).check n ∈ real hG i hi ↔
      n ∈ (ω : V) ∧ ∃ p ∈ G, ⟨⟨i, n⟩ₖ, (1 : V)⟩ₖ ∈ p := by
  rw [mem_real_iff]
  constructor
  · rintro ⟨m, hm, p, hp, hb, he⟩
    obtain rfl := ((cohenContext I G hG).check_eq_iff n m).mp he
    exact ⟨hm, p, hp, hb⟩
  · rintro ⟨hn, p, hp, hb⟩
    exact ⟨n, hn, p, hp, hb, rfl⟩

theorem mem_reals_iff (x : (cohenContext I G hG).Model) :
    x ∈ reals hG ↔ ∃ i : V, ∃ hi : i ∈ I, x = real hG i hi := by
  let S := cohenContext I G hG
  rw [reals, S.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, hp, hσp, hx⟩
    obtain ⟨i, hi, he⟩ := (mem_cohenSetName I _).mp hσp
    have he' : S.ofName σ = real hG i hi := congrArg S.ofName (Subtype.ext (kpair_iff.mp he).1)
    exact ⟨i, hi, hx.trans he'⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨cohenRealName I i, cohenRealName_hereditarilySymmetric hi⟩, ∅,
      externalForcingFilter_top hG.1 (cohen_top I), (mem_cohenSetName I _).mpr ⟨i, hi, rfl⟩, rfl⟩

theorem check_not_mem_real_of_zero {i n p : V} (hi : i ∈ I) (hp : p ∈ G)
    (hb : ⟨⟨i, n⟩ₖ, (0 : V)⟩ₖ ∈ p) : (cohenContext I G hG).check n ∉ real hG i hi := by
  intro hm
  obtain ⟨_, q, hq, hqbit⟩ := (check_mem_real_iff hG hi).mp hm
  have hc := (finitePartialFunctions_compatible_iff (hG.1.1 p hp) (hG.1.1 q hq)).mp
    (externalForcingFilter_compatible hG.1 hp hq)
  have h01 := hc ⟨i, n⟩ₖ 0 1 hb hqbit
  simp at h01

theorem real_ne {i j : V} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    real hG i hi ≠ real hG j hj := by
  obtain ⟨p, hp, hpd⟩ := hG.2 _ (cohen_separate_rows_dense hi hj hij)
  obtain ⟨_, n, hn, hb0, hb1⟩ := mem_sep_iff.mp hpd
  intro he
  have hnmem := (check_mem_real_iff hG hj).mpr ⟨hn, p, hp, hb1⟩
  exact check_not_mem_real_of_zero hG hi hp hb0 (he.symm ▸ hnmem)

theorem real_eq_iff {i j : V} (hi : i ∈ I) (hj : j ∈ I) :
    real hG i hi = real hG j hj ↔ i = j := by
  constructor
  · intro he
    by_contra hn
    exact real_ne hG hi hj hn he
  · rintro rfl
    rfl

end CohenModel
end ZFVP
