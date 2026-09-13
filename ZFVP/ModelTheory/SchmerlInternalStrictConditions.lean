import ZFVP.ModelTheory.SchmerlInternalSpecialization
import ZFVP.SetTheory.FiniteCardinalArithmetic

/-! Compatibility and deletion for internally finite strict-coloring conditions.
The size reduction is a statement about internal cardinal comparison. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalSpecialization_compatible_iff {D S p q : V}
    (hp : p ∈ internalSpecialization D S) (hq : q ∈ internalSpecialization D S) :
    ForcingCompatible (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) p q ↔
      (∀ x m n, ⟨x, m⟩ₖ ∈ p → ⟨x, n⟩ₖ ∈ q → m = n) ∧
      (∀ x y n, ⟨x, n⟩ₖ ∈ p → ⟨y, n⟩ₖ ∈ q →
        ⟨x, y⟩ₖ ∈ S ∨ ⟨y, x⟩ₖ ∈ S → x = y) := by
  obtain ⟨hpfin, hpstrict⟩ := (mem_internalSpecialization _ _ _).mp hp
  obtain ⟨hqfin, hqstrict⟩ := (mem_internalSpecialization _ _ _).mp hq
  constructor
  · rintro ⟨r, hr, hrp, hrq⟩
    obtain ⟨hrfin, hrstrict⟩ := (mem_internalSpecialization _ _ _).mp hr
    have : IsFunction r := ((mem_finitePartialFunctions _ _ _).mp hrfin).2.1
    have hpr := ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
    have hqr := ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
    refine ⟨fun x m n hm hn ↦ IsFunction.unique (hpr _ hm) (hqr _ hn), ?_⟩
    intro x y n hx hy hxy
    rcases hxy with hxy | hyx
    · exact hrstrict x y n (hpr _ hx) (hqr _ hy) hxy
    · exact (hrstrict y x n (hqr _ hy) (hpr _ hx) hyx).symm
  · rintro ⟨hfun, hstrict⟩
    have hufin := finitePartialFunction_union hpfin hqfin hfun
    have hustrict : InternallyStrict S (p ∪ q) := by
      intro x y n hx hy hxy
      rcases mem_union_iff.mp hx with hx | hx <;>
        rcases mem_union_iff.mp hy with hy | hy
      · exact hpstrict x y n hx hy hxy
      · exact hstrict x y n hx hy (Or.inl hxy)
      · exact (hstrict y x n hy hx (Or.inr hxy)).symm
      · exact hqstrict x y n hx hy hxy
    have hu := (mem_internalSpecialization _ _ _).mpr ⟨hufin, hustrict⟩
    exact ⟨p ∪ q, hu,
      (pair_mem_reverseInclusionOrder _ _ _).mpr
        ⟨hu, hp, fun z hz ↦ mem_union_iff.mpr (Or.inl hz)⟩,
      (pair_mem_reverseInclusionOrder _ _ _).mpr
        ⟨hu, hq, fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩⟩

theorem internalSpecialization_exists_comparable_of_not_compatible {D S p q : V}
    (hp : p ∈ internalSpecialization D S) (hq : q ∈ internalSpecialization D S)
    (href : ∀ x ∈ D, ⟨x, x⟩ₖ ∈ S)
    (h : ¬ForcingCompatible (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) p q) :
    ∃ a ∈ p, ∃ b ∈ q,
      ⟨kpair.π₁ a, kpair.π₁ b⟩ₖ ∈ S ∨ ⟨kpair.π₁ b, kpair.π₁ a⟩ₖ ∈ S := by
  classical
  by_contra hn
  apply h
  apply (internalSpecialization_compatible_iff hp hq).mpr
  constructor
  · intro x m n hm hn'
    have hx : x ∈ D := (kpair_mem_iff.mp
      (((mem_finitePartialFunctions _ _ _).mp
        ((mem_internalSpecialization _ _ _).mp hp).1).1 _ hm)).1
    exact False.elim (hn ⟨⟨x, m⟩ₖ, hm, ⟨x, n⟩ₖ, hn', by simpa using href x hx⟩)
  · intro x y n hx hy hxy
    exact False.elim (hn ⟨⟨x, n⟩ₖ, hx, ⟨y, n⟩ₖ, hy, by simpa using hxy⟩)

theorem internalSpecialization_erase {D S p a : V}
    (hp : p ∈ internalSpecialization D S) : p \ {a} ∈ internalSpecialization D S :=
  internalSpecialization_subset hp (fun _ hz ↦ (mem_sdiff_iff.mp hz).1)

theorem internalSpecialization_compatible_of_erase {D S p q a : V}
    (hp : p ∈ internalSpecialization D S) (hq : q ∈ internalSpecialization D S)
    (hap : a ∈ p) (haq : a ∈ q)
    (h : ForcingCompatible (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) (p \ {a}) (q \ {a})) :
    ForcingCompatible (internalSpecialization D S)
      (reverseInclusionOrder (internalSpecialization D S)) p q := by
  classical
  have hpstrict := ((mem_internalSpecialization _ _ _).mp hp).2
  have hqstrict := ((mem_internalSpecialization _ _ _).mp hq).2
  have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp
    ((mem_internalSpecialization _ _ _).mp hp).1).2.1
  have : IsFunction q := ((mem_finitePartialFunctions _ _ _).mp
    ((mem_internalSpecialization _ _ _).mp hq).1).2.1
  obtain ⟨hfun, hstrict⟩ := (internalSpecialization_compatible_iff
    (internalSpecialization_erase hp) (internalSpecialization_erase hq)).mp h
  apply (internalSpecialization_compatible_iff hp hq).mpr
  constructor
  · intro x m n hm hn
    by_cases hem : ⟨x, m⟩ₖ = a
    · exact IsFunction.unique (hem.symm ▸ haq) hn
    by_cases hen : ⟨x, n⟩ₖ = a
    · exact IsFunction.unique hm (hen.symm ▸ hap)
    exact hfun x m n (mem_sdiff_iff.mpr ⟨hm, by simpa using hem⟩)
      (mem_sdiff_iff.mpr ⟨hn, by simpa using hen⟩)
  · intro x y n hx hy hxy
    by_cases hex : ⟨x, n⟩ₖ = a
    · rcases hxy with hxy | hyx
      · exact hqstrict x y n (hex.symm ▸ haq) hy hxy
      · exact (hqstrict y x n hy (hex.symm ▸ haq) hyx).symm
    by_cases hey : ⟨y, n⟩ₖ = a
    · rcases hxy with hxy | hyx
      · exact hpstrict x y n hx (hey.symm ▸ hap) hxy
      · exact (hpstrict y x n (hey.symm ▸ hap) hx hyx).symm
    exact hstrict x y n (mem_sdiff_iff.mpr ⟨hx, by simpa using hex⟩)
      (mem_sdiff_iff.mpr ⟨hy, by simpa using hey⟩) hxy

theorem internal_erase_injective {p q a : V} (hap : a ∈ p) (haq : a ∈ q)
    (heq : p \ {a} = q \ {a}) : p = q := by
  apply mem_ext
  intro z
  by_cases hza : z = a
  · subst z
    exact iff_of_true hap haq
  · have hz : z ∈ p \ {a} ↔ z ∈ q \ {a} := by rw [heq]
    simpa only [mem_sdiff_iff, mem_singleton_iff, hza, not_false_eq_true, and_true] using hz

/-- An injection into `succ n` loses one unit of its internal bound when a
specified member is deleted. The deleted member's image replaces `n`. -/
theorem internal_erase_cardLE {A a n : V} (hA : A ≤# succ n) (ha : a ∈ A) :
    A \ {a} ≤# n := by
  classical
  obtain ⟨f, hf, hfi⟩ := hA
  let F : V → V := fun x ↦ if f ‘ x = n then f ‘ a else f ‘ x
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun y x : V ↦
      (f ‘ x = n ∧ y = f ‘ a) ∨ (f ‘ x ≠ n ∧ y = f ‘ x)) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = F (v 1) ↔ _
    unfold F
    split <;> simp_all
  apply cardLE_of_injective_map F hF
  · intro x hx
    obtain ⟨hxA, hxa⟩ := mem_sdiff_iff.mp hx
    have hxa' : x ≠ a := by simpa using hxa
    dsimp only [F]
    split_ifs with hxn
    · apply (mem_succ_iff.mp (function_value_mem hf ha)).resolve_left
      intro han
      exact hxa' (injective_value_eq hf hfi hxA ha (hxn.trans han.symm))
    · exact (mem_succ_iff.mp (function_value_mem hf hxA)).resolve_left hxn
  · intro x hx y hy he
    obtain ⟨hxA, hxa⟩ := mem_sdiff_iff.mp hx
    obtain ⟨hyA, hya⟩ := mem_sdiff_iff.mp hy
    have hxa' : x ≠ a := by simpa using hxa
    have hya' : y ≠ a := by simpa using hya
    dsimp only [F] at he
    split_ifs at he with hxn hyn hyn
    · exact injective_value_eq hf hfi hxA hyA (hxn.trans hyn.symm)
    · exact False.elim (hya' (injective_value_eq hf hfi hyA ha he.symm))
    · exact False.elim (hxa' (injective_value_eq hf hfi hxA ha he))
    · exact injective_value_eq hf hfi hxA hyA he

end ZFVP.Schmerl
