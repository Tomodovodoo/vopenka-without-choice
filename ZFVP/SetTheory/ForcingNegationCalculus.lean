import ZFVP.SetTheory.RegularSetAlgebra
import ZFVP.SetTheory.FormulaForcing
import ZFVP.SetTheory.ForcingFormulaWitnesses

/-! The forcing calculus for negation and implication: the set of conditions forcing `∼φ` is the
forcing negation of the set forcing `φ`, implications are joins with negations, and the resulting
modus ponens and universal instantiation rules for the ordinary forcing relation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingNegation_top {P R : V} (hR : IsForcingPreorder P R) : forcingNegation P R P = ∅ := by
  ext p
  simp only [mem_forcingNegation_iff, not_mem_empty, iff_false, not_and]
  intro hp h
  exact h p hp (hR.2.1 p hp) hp

theorem forcingNegation_empty (P R : V) : forcingNegation P R (∅ : V) = P := by
  ext p
  rw [mem_forcingNegation_iff]
  exact ⟨fun h ↦ h.1, fun hp ↦ ⟨hp, fun q _ _ hq ↦ not_mem_empty hq⟩⟩

theorem sUnion_pair_eq (A B : V) : ⋃ˢ ({A, B} : V) = A ∪ B := by
  rw [sUnion_insert, sUnion_singleton_eq]

/-- The conditions forcing `∼φ` are the forcing negation of those forcing `φ`. -/
theorem forcingFormula_neg {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    (φ : SetTheorySemisentence n) :
    ∀ b : V, forcingFormula P R (∼φ) b = forcingNegation P R (forcingFormula P R φ b) := by
  induction φ using Semiformula.rec' with
  | hverum =>
    intro b
    change forcingFormula P R (.falsum) b = forcingNegation P R (forcingFormula P R (.verum) b)
    rw [forcingFormula_falsum, forcingFormula_verum, forcingNegation_top hR]
  | hfalsum =>
    intro b
    change forcingFormula P R (.verum) b = forcingNegation P R (forcingFormula P R (.falsum) b)
    rw [forcingFormula_verum, forcingFormula_falsum, forcingNegation_empty]
  | hrel r ts =>
    intro b
    change forcingFormula P R (.nrel r ts) b = forcingNegation P R (forcingFormula P R (.rel r ts) b)
    rw [forcingFormula_nrel, forcingFormula_rel]
  | hnrel r ts =>
    intro b
    change forcingFormula P R (.rel r ts) b = forcingNegation P R (forcingFormula P R (.nrel r ts) b)
    rw [forcingFormula_rel, forcingFormula_nrel, forcingNegation_negation hR (forcingAtomic_regular hR r ts b)]
  | hand φ ψ ihφ ihψ =>
    intro b
    change forcingFormula P R (.or (∼φ) (∼ψ)) b = forcingNegation P R (forcingFormula P R (.and φ ψ) b)
    rw [forcingFormula_or, ihφ, ihψ, forcingFormula_and,
      forcingNegation_inter hR (forcingFormula_regular hR φ b) (forcingFormula_regular hR ψ b)]
    unfold regularJoin
    rw [sUnion_pair_eq]
  | hor φ ψ ihφ ihψ =>
    intro b
    change forcingFormula P R (.and (∼φ) (∼ψ)) b = forcingNegation P R (forcingFormula P R (.or φ ψ) b)
    rw [forcingFormula_and, ihφ, ihψ, forcingFormula_or]
    have hX : ∀ C ∈ ({forcingFormula P R φ b, forcingFormula P R ψ b} : V), IsForcingRegular P R C := by
      intro C hC
      rcases mem_insert.mp hC with rfl | hC
      · exact forcingFormula_regular hR φ b
      · rw [mem_singleton_iff.mp hC]
        exact forcingFormula_regular hR ψ b
    ext p
    have key := mem_forcingNegation_regularJoin_iff (p := p) hR hX
    unfold regularJoin at key
    rw [sUnion_pair_eq] at key
    rw [key, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨((mem_forcingNegation_iff _ _ _ _).mp h1).1, fun C hC ↦ ?_⟩
      rcases mem_insert.mp hC with rfl | hC
      · exact h1
      · rw [mem_singleton_iff.mp hC]
        exact h2
    · rintro ⟨_, hh⟩
      exact ⟨hh _ (mem_insert.mpr (Or.inl rfl)), hh _ (mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl)))⟩
  | hall φ ih =>
    intro b
    change forcingFormula P R (.exs (∼φ)) b = forcingNegation P R (forcingFormula P R (.all φ) b)
    rw [forcingFormula_exs, forcingFormula_all]
    ext p
    unfold forcingExistential
    rw [mem_forcingClosure_iff, mem_forcingNegation_iff]
    simp only [mem_forcingClassUnion_iff, mem_forcingClassIntersection_iff, ih]
    constructor
    · rintro ⟨hpP, hh⟩
      refine ⟨hpP, fun q hq hqp hqall ↦ ?_⟩
      obtain ⟨r, ⟨hrP, x, hx, hrn⟩, hrq⟩ := hh q hq hqp
      have hrF := (forcingFormula_regular hR φ _).2.1 q (hqall.2 x hx) r hrP hrq
      exact ((mem_forcingNegation_iff _ _ _ _).mp hrn).2 r hrP (hR.2.1 r hrP) hrF
    · rintro ⟨hpP, hh⟩
      refine ⟨hpP, fun q hq hqp ↦ ?_⟩
      have hq' := hh q hq hqp
      push Not at hq'
      obtain ⟨x, hx, hqF⟩ := hq' hq
      obtain ⟨r, hr, hrq⟩ := exists_forcingNegation_of_not_mem hq hqF (forcingFormula_regular hR φ _).2.2
      exact ⟨r, ⟨forcingNegation_subset _ _ _ r hr, x, hx, hr⟩, hrq⟩
  | hexs φ ih =>
    intro b
    change forcingFormula P R (.all (∼φ)) b = forcingNegation P R (forcingFormula P R (.exs φ) b)
    rw [forcingFormula_all, forcingFormula_exs]
    ext p
    rw [mem_forcingClassIntersection_iff, mem_forcingNegation_iff]
    simp only [ih]
    unfold forcingExistential
    constructor
    · rintro ⟨hpP, hh⟩
      refine ⟨hpP, fun q hq hqp hqc ↦ ?_⟩
      obtain ⟨_, hc⟩ := (mem_forcingClosure_iff _ _ _ _).mp hqc
      obtain ⟨r, hr, hrq⟩ := hc q hq (hR.2.1 q hq)
      obtain ⟨hrP, x, hx, hrF⟩ := (mem_forcingClassUnion_iff _ _ _ _ _ _).mp hr
      exact ((mem_forcingNegation_iff _ _ _ _).mp (hh x hx)).2 r hrP
        (hR.2.2 r hrP q hq p hpP hrq hqp) hrF
    · rintro ⟨hpP, hh⟩
      refine ⟨hpP, fun x hx ↦ (mem_forcingNegation_iff _ _ _ _).mpr ⟨hpP, fun q hq hqp hqF ↦ ?_⟩⟩
      apply hh q hq hqp
      refine subset_forcingClosure hR (fun r hr ↦ ((mem_forcingClassUnion_iff _ _ _ _ _ _).mp hr).1) ?_ q
        ((mem_forcingClassUnion_iff _ _ _ _ _ _).mpr ⟨hq, x, hx, hqF⟩)
      intro r hr s hs hsr
      obtain ⟨_, y, hy, hrF⟩ := (mem_forcingClassUnion_iff _ _ _ _ _ _).mp hr
      exact (mem_forcingClassUnion_iff _ _ _ _ _ _).mpr
        ⟨hs, y, hy, (forcingFormula_regular hR φ _).2.1 r hrF s hs hsr⟩

theorem mem_forcingFormula_neg_iff {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    (φ : SetTheorySemisentence n) (b p : V) :
    p ∈ forcingFormula P R (∼φ) b ↔ p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → q ∉ forcingFormula P R φ b := by
  rw [forcingFormula_neg hR, mem_forcingNegation_iff]

/-- The conditions forcing `φ 🡒 ψ` are the join of the negation of `‖φ‖` with `‖ψ‖`. -/
theorem forcingFormula_imp {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    (φ ψ : SetTheorySemisentence n) (b : V) :
    forcingFormula P R (φ 🡒 ψ) b =
      regularJoin P R ({forcingNegation P R (forcingFormula P R φ b), forcingFormula P R ψ b} : V) := by
  change forcingFormula P R (.or (∼φ) ψ) b = _
  rw [forcingFormula_or, forcingFormula_neg hR]
  unfold regularJoin
  rw [sUnion_pair_eq]

/-- Modus ponens for the forcing relation. -/
theorem forcingFormula_imp_mp {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ ψ : SetTheorySemisentence n} {b p : V} (himp : p ∈ forcingFormula P R (φ 🡒 ψ) b)
    (hφ : p ∈ forcingFormula P R φ b) : p ∈ forcingFormula P R ψ b := by
  rw [forcingFormula_imp hR] at himp
  exact inter_regularJoin_negation_subset hR (forcingFormula_regular hR φ b)
    (forcingFormula_regular hR ψ b) p (mem_inter_iff.mpr ⟨hφ, himp⟩)

/-- A condition forcing `φ 🡒 ψ` and `ψ 🡒 φ` forces `φ` exactly when it forces `ψ`. -/
theorem forcingFormula_iff_of_both {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ ψ : SetTheorySemisentence n} {b p : V} (h₁ : p ∈ forcingFormula P R (φ 🡒 ψ) b)
    (h₂ : p ∈ forcingFormula P R (ψ 🡒 φ) b) :
    p ∈ forcingFormula P R φ b ↔ p ∈ forcingFormula P R ψ b :=
  ⟨forcingFormula_imp_mp hR h₁, forcingFormula_imp_mp hR h₂⟩

/-- Universal instantiation for the forcing relation. -/
theorem forcingFormula_all_elim {P R : V} {n : ℕ} {φ : SetTheorySemisentence (n + 1)} {b p ν : V}
    (h : p ∈ forcingFormula P R (.all φ) b) (hν : IsForcingName P ν) :
    p ∈ forcingFormula P R φ (assignmentPrepend (n : V) b ν) := by
  rw [forcingFormula_all, mem_forcingClassIntersection_iff] at h
  exact h.2 ν hν

/-- Forcing sets are closed under strengthening the condition. -/
theorem forcingFormula_mono {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ : SetTheorySemisentence n} {b p q : V} (hp : p ∈ forcingFormula P R φ b) (hq : q ∈ P)
    (hqp : ⟨q, p⟩ₖ ∈ R) : q ∈ forcingFormula P R φ b :=
  (forcingFormula_regular hR φ b).2.1 p hp q hq hqp

end ZFVP
