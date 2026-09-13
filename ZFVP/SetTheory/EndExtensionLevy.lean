import ZFVP.SetTheory.MembershipEndExtension
import ZFVP.SetTheory.LevyAbsoluteness

/-! Level-one formula transport along arbitrary membership end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]

theorem levy_one_transport (j : MembershipEndExtension V W) {p k n} {φ : SetTheorySemisentence n}
    (hφ : IsLevyFormula p k φ) : k ≤ 1 → ∀ b : Fin n → V,
      p.Preserves (φ.Evalb b) (φ.Evalb (fun i ↦ j (b i))) := by
  induction hφ with
  | @bounded p k n φ hφ =>
    intro _ b
    cases p
    · exact (j.bounded_elementary hφ b).mp
    · exact (j.bounded_elementary hφ b).mpr
  | @raise p q k n φ hφ ih =>
    intro hk b
    have hzero : k = 0 := by omega
    have habs := j.bounded_elementary (hφ.zero_bounded hzero) b
    cases q
    · exact habs.mp
    · exact habs.mpr
  | @and p k n φ ψ hφ hψ ihφ ihψ =>
    intro hk b
    cases p
    · exact fun h ↦ ⟨ihφ hk b h.1, ihψ hk b h.2⟩
    · exact fun h ↦ ⟨ihφ hk b h.1, ihψ hk b h.2⟩
  | @or p k n φ ψ hφ hψ ihφ ihψ =>
    intro hk b
    cases p
    · exact fun h ↦ h.elim (fun h ↦ Or.inl (ihφ hk b h)) (fun h ↦ Or.inr (ihψ hk b h))
    · exact fun h ↦ h.elim (fun h ↦ Or.inl (ihφ hk b h)) (fun h ↦ Or.inr (ihψ hk b h))
  | @boundedAll p k n t φ hφ ih =>
    intro hk b
    cases p
    · intro h
      apply (eval_boundedSetAll _ _ _).mpr
      intro y hy
      rw [j.val_term] at hy
      obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
      have hh := ih hk (x :> b) ((eval_boundedSetAll _ _ _).mp h x hx)
      simpa only [j.map_cons] using hh
    · intro h
      apply (eval_boundedSetAll _ _ _).mpr
      intro x hx
      apply ih hk (x :> b)
      rw [j.map_cons]
      exact (eval_boundedSetAll _ _ _).mp h (j x) (by rw [j.val_term]; exact (j.mem_iff _ _).mpr hx)
  | @boundedExs p k n t φ hφ ih =>
    intro hk b
    cases p
    · intro h
      obtain ⟨x, hx, hh⟩ := (eval_boundedSetExs _ _ _).mp h
      apply (eval_boundedSetExs _ _ _).mpr
      refine ⟨j x, ?_, ?_⟩
      · rw [j.val_term]; exact (j.mem_iff _ _).mpr hx
      · simpa only [j.map_cons] using ih hk (x :> b) hh
    · intro h
      obtain ⟨y, hy, hh⟩ := (eval_boundedSetExs _ _ _).mp h
      rw [j.val_term] at hy
      obtain ⟨x, hx, rfl⟩ := j.endExtension _ y hy
      apply (eval_boundedSetExs _ _ _).mpr
      exact ⟨x, hx, ih hk (x :> b) (by simpa only [j.map_cons] using hh)⟩
  | @exs k n φ hφ ih =>
    intro hk b h
    obtain ⟨x, hx⟩ := h
    refine ⟨j x, ?_⟩
    have hh := ih hk (x :> b) hx
    rw [j.map_cons] at hh
    exact hh
  | @all k n φ hφ ih =>
    intro hk b h x
    apply ih hk (x :> b)
    rw [j.map_cons]
    exact h (j x)

theorem sigma_one_upward (j : MembershipEndExtension V W) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsSigmaFormula 1 φ) (b : Fin n → V) :
    φ.Evalb b → φ.Evalb (fun i ↦ j (b i)) := j.levy_one_transport hφ (by omega) b

theorem pi_one_downward (j : MembershipEndExtension V W) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsPiFormula 1 φ) (b : Fin n → V) :
    φ.Evalb (fun i ↦ j (b i)) → φ.Evalb b := j.levy_one_transport hφ (by omega) b

theorem bounded_defined (j : MembershipEndExtension V W) {n : ℕ}
    {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (R : (Fin n → V) → Prop) (S : (Fin n → W) → Prop)
    [Defined R φ] [Defined S φ] (b : Fin n → V) :
    R b ↔ S (fun i ↦ j (b i)) :=
  (Defined.eval_iff b).symm.trans ((j.bounded_elementary hφ b).trans (Defined.eval_iff _))

theorem deltaOne_defined (j : MembershipEndExtension V W) {n : ℕ}
    {σ π : SetTheorySemisentence n} (hσ : IsSigmaFormula 1 σ) (hπ : IsPiFormula 1 π)
    (R : (Fin n → V) → Prop) (S : (Fin n → W) → Prop)
    [Defined R σ] [Defined R π] [Defined S σ] [Defined S π] (b : Fin n → V) :
    R b ↔ S (fun i ↦ j (b i)) := by
  constructor
  · intro hr
    exact (show σ.Evalb (fun i ↦ j (b i)) ↔ S (fun i ↦ j (b i)) from Defined.eval_iff _).mp
      (j.sigma_one_upward hσ b ((show σ.Evalb b ↔ R b from Defined.eval_iff _).mpr hr))
  · intro hs
    exact (show π.Evalb b ↔ R b from Defined.eval_iff _).mp
      (j.pi_one_downward hπ b ((show π.Evalb (fun i ↦ j (b i)) ↔ S (fun i ↦ j (b i))
        from Defined.eval_iff _).mpr hs))

end MembershipEndExtension
end ZFVP
