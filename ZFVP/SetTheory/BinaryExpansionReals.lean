import ZFVP.SetTheory.BinaryExpansionIntervals
import ZFVP.SetTheory.InternalDedekindReals

/-! Binary expansion as an actual, uniformly definable map to internal Dedekind cuts. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def binaryRealFormula : SetTheorySemisentence 2 :=
  f“x c. ∀ q, q ∈ x ↔ q ∈ !internalRationalsFormula ∧
    ∃ n ∈ !isω, !internalRationalLTFormula q (!binaryValueFormula c n)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryReal (c : V) : V :=
  {q ∈ internalRationals V ; ∃ n ∈ (ω : V), InternalRationalLT q (binaryValue c n)}

theorem mem_binaryReal_iff (c q : V) : q ∈ binaryReal c ↔
    q ∈ internalRationals V ∧ ∃ n ∈ (ω : V), InternalRationalLT q (binaryValue c n) := by
  simp [binaryReal]

instance binaryRealFormula_defined : ℒₛₑₜ-function₁[V] binaryReal via binaryRealFormula :=
  ⟨fun v ↦ by simp [binaryRealFormula, mem_ext_iff (y := binaryReal _), mem_binaryReal_iff]⟩

instance binaryReal_definable : ℒₛₑₜ-function₁[V] binaryReal := binaryRealFormula_defined.to_definable

theorem binaryReal_eq_sUnion (c : V) :
    binaryReal c = ⋃ˢ repl (fun n ↦ rationalCut (binaryValue c n)) (by definability) (ω : V) := by
  apply mem_ext
  intro q
  rw [mem_binaryReal_iff, mem_sUnion_iff]
  constructor
  · rintro ⟨hq, n, hn, hqn⟩
    exact ⟨rationalCut (binaryValue c n), (repl_spec _).mpr ⟨n, hn, rfl⟩,
      (mem_rationalCut_iff _ _).mpr ⟨hq, hqn⟩⟩
  · rintro ⟨y, hy, hqy⟩
    obtain ⟨n, hn, rfl⟩ := (repl_spec _).mp hy
    obtain ⟨hq, hqn⟩ := (mem_rationalCut_iff _ _).mp hqy
    exact ⟨hq, n, hn, hqn⟩

theorem binaryReal_isCut {c : V} (hc : c ∈ cantorSpace V) : IsDedekindCut (binaryReal c) := by
  refine ⟨fun q hq ↦ ((mem_binaryReal_iff c q).mp hq).1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq, hq0⟩ := (internalRational_noEndpoints (rationalZero_mem (V := V))).1
    exact ⟨q, (mem_binaryReal_iff c q).mpr ⟨hq, 0, by simp, by rwa [binaryValue_zero]⟩⟩
  · refine ⟨rationalOne V, rationalOne_mem, ?_⟩
    intro h
    obtain ⟨_, n, hn, h1n⟩ := (mem_binaryReal_iff c (rationalOne V)).mp h
    have hn1 := InternalRational.binaryApprox_lt_one c hc (⟨n, hn⟩ : InternalNatural V)
    exact lt_asymm hn1 h1n
  · intro q hq r hr hrq
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_binaryReal_iff c q).mp hq
    exact (mem_binaryReal_iff c r).mpr
      ⟨hr, n, hn, internalRationalLT_trans hr hqQ (binaryValue_mem hc hn) hrq hqn⟩
  · intro q hq
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_binaryReal_iff c q).mp hq
    obtain ⟨r, hrQ, hqr, hrn⟩ := internalRational_dense hqQ (binaryValue_mem hc hn) hqn
    exact ⟨r, (mem_binaryReal_iff c r).mpr ⟨hrQ, n, hn, hrn⟩, hqr⟩

theorem binaryReal_mem {c : V} (hc : c ∈ cantorSpace V) : binaryReal c ∈ dedekindReals V :=
  (mem_dedekindReals_iff _).mpr (binaryReal_isCut hc)

theorem binaryReal_lower {c n : V} (hn : n ∈ (ω : V)) :
    rationalCut (binaryValue c n) ⊆ binaryReal c := by
  intro q hq
  obtain ⟨hqQ, hqn⟩ := (mem_rationalCut_iff _ _).mp hq
  exact (mem_binaryReal_iff c q).mpr ⟨hqQ, n, hn, hqn⟩

theorem binaryReal_upper {c n : V} (hc : c ∈ cantorSpace V) (hn : n ∈ (ω : V)) :
    binaryReal c ⊆ rationalCut (binaryUpper c n) := by
  intro q hq
  obtain ⟨hqQ, m, hm, hqm⟩ := (mem_binaryReal_iff c q).mp hq
  exact (mem_rationalCut_iff _ _).mpr ⟨hqQ,
    internalRationalLT_trans hqQ (binaryValue_mem hc hm) (binaryUpper_mem hc hn)
      hqm (binaryValue_lt_upper hc hm hn)⟩

theorem binaryReal_unitInterval {c : V} (hc : c ∈ cantorSpace V) :
    rationalCut (rationalZero V) ⊆ binaryReal c ∧ binaryReal c ⊆ rationalCut (rationalOne V) := by
  constructor
  · simpa only [binaryValue_zero] using (binaryReal_lower (c := c) (n := 0) (by simp))
  · intro q hq
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_binaryReal_iff c q).mp hq
    exact (mem_rationalCut_iff _ _).mpr ⟨hqQ,
      internalRationalLT_trans hqQ (binaryValue_mem hc hn) rationalOne_mem hqn
        (InternalRational.binaryApprox_lt_one c hc (⟨n, hn⟩ : InternalNatural V))⟩

theorem binaryReal_unique {c x : V} (hc : c ∈ cantorSpace V) (hx : IsDedekindCut x)
    (hlo : ∀ n ∈ (ω : V), rationalCut (binaryValue c n) ⊆ x)
    (hup : ∀ n ∈ (ω : V), x ⊆ rationalCut (binaryUpper c n)) : x = binaryReal c := by
  apply SetTheory.subset_antisymm
  · intro q hqx
    obtain ⟨r, hrx, hqr⟩ := hx.2.2.2.2 q hqx
    let a : InternalRational V := ⟨q, hx.1 q hqx⟩
    let b : InternalRational V := ⟨r, hx.1 r hrx⟩
    have hab : a < b := hqr
    obtain ⟨n, hn⟩ := InternalRational.exists_dyadic_lt (sub_pos.mpr hab)
    have hbn : b < InternalRational.binaryApprox c hc n + InternalRational.dyadic n :=
      ((mem_rationalCut_iff _ _).mp (hup n.val n.property r hrx)).2
    have haeps : a + InternalRational.dyadic n < b := by
      simpa only [add_comm] using (lt_sub_iff_add_lt).mp hn
    have han : a < InternalRational.binaryApprox c hc n :=
      lt_of_add_lt_add_right (lt_trans haeps hbn)
    exact (mem_binaryReal_iff c q).mpr ⟨a.property, n.val, n.property, han⟩
  · intro q hq
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_binaryReal_iff c q).mp hq
    exact hlo n hn q ((mem_rationalCut_iff _ _).mpr ⟨hqQ, hqn⟩)

end ZFVP
