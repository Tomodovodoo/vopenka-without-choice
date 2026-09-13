import ZFVP.SetTheory.DedekindRealTopology

/-! Refinement and separation for the internal rational interval basis. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realInterval_order {a b x : V} (ha : a ∈ internalRationals V)
    (hb : b ∈ internalRationals V) (hx : x ∈ realInterval a b) : InternalRationalLT a b := by
  obtain ⟨_, hax, hxb⟩ := (mem_realInterval_iff _ _ _).mp hx
  exact (rationalCut_lt_iff ha hb).mp (dedekindLT_trans hax hxb)

theorem realInterval_neighborhood {x : V} (hx : IsDedekindCut x) :
    ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V, x ∈ realInterval a b := by
  obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hxb⟩⟩ := dedekindCuts_noEndpoints hx
  exact ⟨a, ha, b, hb, (mem_realInterval_iff _ _ _).mpr ⟨hx, hax, hxb⟩⟩

theorem realInterval_mono (a b c d : InternalRational V) (hca : c ≤ a) (hbd : b ≤ d) :
    realInterval a.val b.val ⊆ realInterval c.val d.val := by
  intro x hx
  obtain ⟨hxCut, hax, hxb⟩ := (mem_realInterval_iff _ _ _).mp hx
  exact (mem_realInterval_iff _ _ _).mpr ⟨hxCut,
    dedekindLT_of_subset_of_lt (InternalRational.rationalCut_mono hca) hax,
    dedekindLT_of_lt_of_subset hxb (InternalRational.rationalCut_mono hbd)⟩

theorem realInterval_refine_inter {x a b c d : V}
    (ha : a ∈ internalRationals V) (hb : b ∈ internalRationals V)
    (hc : c ∈ internalRationals V) (hd : d ∈ internalRationals V)
    (hx1 : x ∈ realInterval a b) (hx2 : x ∈ realInterval c d) :
    ∃ u ∈ internalRationals V, ∃ v ∈ internalRationals V,
      x ∈ realInterval u v ∧ realInterval u v ⊆ realInterval a b ∧
        realInterval u v ⊆ realInterval c d := by
  let A : InternalRational V := ⟨a, ha⟩
  let B : InternalRational V := ⟨b, hb⟩
  let C : InternalRational V := ⟨c, hc⟩
  let D : InternalRational V := ⟨d, hd⟩
  let U := max A C
  let W := min B D
  obtain ⟨hxCut, hax, hxb⟩ := (mem_realInterval_iff _ _ _).mp hx1
  obtain ⟨_, hcx, hxd⟩ := (mem_realInterval_iff _ _ _).mp hx2
  have hlo : DedekindLT (rationalCut U.val) x := by
    rcases le_total A C with h | h
    · simpa only [U, max_eq_right h] using hcx
    · simpa only [U, max_eq_left h] using hax
  have hup : DedekindLT x (rationalCut W.val) := by
    rcases le_total B D with h | h
    · simpa only [W, min_eq_left h] using hxb
    · simpa only [W, min_eq_right h] using hxd
  exact ⟨U.val, U.property, W.val, W.property,
    (mem_realInterval_iff _ _ _).mpr ⟨hxCut, hlo, hup⟩,
    realInterval_mono U W A B (le_max_left _ _) (min_le_left _ _),
    realInterval_mono U W C D (le_max_right _ _) (min_le_right _ _)⟩

theorem realIntervals_disjoint_at (a q b : V) :
    ∀ z ∈ realInterval q b, z ∉ realInterval a q := by
  intro z hz hz'
  have h1 := ((mem_realInterval_iff _ _ _).mp hz).2.1
  have h2 := ((mem_realInterval_iff _ _ _).mp hz').2.2
  exact dedekindLT_irrefl _ (dedekindLT_trans h1 h2)

theorem realIntervals_separate_lt {x y : V} (hx : IsDedekindCut x) (hy : IsDedekindCut y)
    (hxy : DedekindLT x y) :
    ∃ a ∈ internalRationals V, ∃ q ∈ internalRationals V, ∃ b ∈ internalRationals V,
      x ∈ realInterval a q ∧ y ∈ realInterval q b := by
  obtain ⟨q, hq, hxq, hqy⟩ := rationalCuts_dense hx hy hxy
  obtain ⟨a, ha, hax⟩ := (dedekindCuts_noEndpoints hx).1
  obtain ⟨b, hb, hyb⟩ := (dedekindCuts_noEndpoints hy).2
  exact ⟨a, ha, q, hq, b, hb,
    (mem_realInterval_iff _ _ _).mpr ⟨hx, hax, hxq⟩,
    (mem_realInterval_iff _ _ _).mpr ⟨hy, hqy, hyb⟩⟩

theorem realIntervals_separate {x y : V} (hx : IsDedekindCut x) (hy : IsDedekindCut y)
    (hne : x ≠ y) :
    ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V,
    ∃ u ∈ internalRationals V, ∃ v ∈ internalRationals V,
      x ∈ realInterval a b ∧ y ∈ realInterval u v ∧
        ∀ z ∈ realInterval u v, z ∉ realInterval a b := by
  rcases dedekindCuts_comparable hx hy with hxy | hyx
  · obtain ⟨a, ha, q, hq, b, hb, hxi, hyi⟩ := realIntervals_separate_lt hx hy ⟨hxy, hne⟩
    exact ⟨a, ha, q, hq, q, hq, b, hb, hxi, hyi, realIntervals_disjoint_at _ _ _⟩
  · obtain ⟨a, ha, q, hq, b, hb, hyi, hxi⟩ := realIntervals_separate_lt hy hx ⟨hyx, Ne.symm hne⟩
    exact ⟨q, hq, b, hb, a, ha, q, hq, hxi, hyi,
      fun z hz hz' ↦ realIntervals_disjoint_at a q b z hz' hz⟩

end ZFVP
