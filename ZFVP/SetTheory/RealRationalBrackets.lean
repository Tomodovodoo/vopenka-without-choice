import ZFVP.SetTheory.RealCoverUnion

/-! Rational brackets of arbitrarily small positive width around a Dedekind cut. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem real_rational_bracket {x : V} (hx : IsDedekindCut x)
    (e : InternalRational V) (he : 0 < e) :
    ∃ a ∈ x, rationalAdd a e.val ∉ x := by
  obtain ⟨q, hqx⟩ := hx.2.1
  obtain ⟨b, hb, hbx⟩ := hx.2.2.1
  let p : InternalRational V := ⟨q, hx.1 q hqx⟩
  let t : InternalRational V := ⟨b, hb⟩
  obtain ⟨n, hn⟩ := InternalRational.exists_natural_gt ((t - p) / e)
  have hbn : t < p + InternalRational.ofNatural n * e := by
    have h := (div_lt_iff₀ he).mp hn
    simpa only [add_comm] using (sub_lt_iff_lt_add).mp h
  have hnot : rationalAdd q (rationalMul (rationalNatural n.val) e.val) ∉ x := by
    intro h
    exact hbx (hx.2.2.2.1 _ h b hb hbn)
  have h : ∀ k ∈ (ω : V), rationalAdd q (rationalMul (rationalNatural k) e.val) ∉ x →
      ∃ a ∈ x, rationalAdd a e.val ∉ x := by
    apply naturalNumber_induction (fun k ↦
      rationalAdd q (rationalMul (rationalNatural k) e.val) ∉ x →
        ∃ a ∈ x, rationalAdd a e.val ∉ x) (by definability)
    · intro h
      apply False.elim
      apply h
      have hz : rationalAdd q (rationalMul (rationalNatural (0 : V)) e.val) = q := by
        rw [rationalNatural_zero]
        exact congrArg Subtype.val (show p + 0 * e = p from by ring)
      rwa [hz]
    · intro k hk ih hnext
      by_cases hkx : rationalAdd q (rationalMul (rationalNatural k) e.val) ∈ x
      · refine ⟨_, hkx, ?_⟩
        have heq : rationalAdd q (rationalMul (rationalNatural (succ k)) e.val) =
            rationalAdd (rationalAdd q (rationalMul (rationalNatural k) e.val)) e.val := by
          rw [rationalNatural_succ hk]
          let r : InternalRational V := ⟨rationalNatural k, rationalNatural_mem hk⟩
          exact congrArg Subtype.val (show p + (r + 1) * e = (p + r * e) + e from by ring)
        rwa [heq] at hnext
      · exact ih hkx
  exact h n.val n.property hnot

end ZFVP
