import ZFVP.SetTheory.GenericName
import ZFVP.SetTheory.AtomicCheckNames
import ZFVP.SetTheory.BooleanCompletionValues
import ZFVP.SetTheory.RegularSetAlgebra
import ZFVP.SetTheory.ForcingNegationCalculus

/-! Separative preorders, separativity of the Boolean completion, and the basic forcing fact
`p ⊩ q̌ ∈ Γ̇ ↔ p ≤ q` for the canonical name of the generic. Intro rules for conjunction and
existential quantification in the forcing calculus. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A preorder is separative when a condition not below another has an extension incompatible
with it. -/
def IsSeparative (P R : V) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ⟨p, q⟩ₖ ∉ R → ∃ r ∈ P, ⟨r, p⟩ₖ ∈ R ∧ ¬ ForcingCompatible P R r q

/-- The Boolean completion is separative. -/
theorem booleanOrder_separative {P R : V} (hR : IsForcingPreorder P R) :
    IsSeparative (booleanConditions P R) (booleanOrder P R) := by
  intro A hA C hC hnot
  have hAr := booleanConditions_regular hA
  have hCr := booleanConditions_regular hC
  have hex : ∃ p ∈ A, p ∉ C := by
    by_contra h
    push Not at h
    exact hnot ((kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hA, hC, h⟩)
  obtain ⟨p, hpA, hpC⟩ := hex
  obtain ⟨q, hq, hqp⟩ := exists_forcingNegation_of_not_mem (hAr.1 p hpA) hpC hCr.2.2
  have hqA : q ∈ A := hAr.2.1 p hpA q (forcingNegation_subset _ _ _ q hq) hqp
  have hE : A ∩ forcingNegation P R C ∈ booleanConditions P R :=
    (mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingRegular_inter hAr (forcingNegation_regular hR hCr.2.1), q, mem_inter_iff.mpr ⟨hqA, hq⟩⟩
  refine ⟨_, hE, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hE, hA, fun x hx ↦ (mem_inter_iff.mp hx).1⟩, ?_⟩
  rintro ⟨F, hF, hFE, hFC⟩
  obtain ⟨_, _, hFE'⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hFE
  obtain ⟨_, _, hFC'⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hFC
  obtain ⟨r, hr⟩ := booleanConditions_nonempty hF
  have : r ∈ C ∩ forcingNegation P R C := mem_inter_iff.mpr ⟨hFC' r hr, (mem_inter_iff.mp (hFE' r hr)).2⟩
  rw [inter_forcingNegation_eq_empty hR hCr.1] at this
  exact not_mem_empty this

/-- In a separative preorder, `p` forces `q̌ ∈ Γ̇` exactly when `p ≤ q`. -/
theorem mem_atomicMembership_checkName_genericName_iff {P R one q p : V} (hR : IsForcingPreorder P R)
    (hone : IsForcingTop P R one) (hsep : IsSeparative P R) (hq : q ∈ P) :
    p ∈ atomicMembership P R (checkName one q) (genericName P one) ↔ p ∈ P ∧ ⟨p, q⟩ₖ ∈ R := by
  constructor
  · intro hp
    obtain ⟨hpP, hh⟩ := (mem_atomicMembership_iff _ _ _ _ _).mp hp
    refine ⟨hpP, ?_⟩
    by_contra hnot
    obtain ⟨r₀, hr₀, hr₀p, hinc⟩ := hsep p hpP q hq hnot
    obtain ⟨r, hr, hrr₀, ν, s, hνs, hrs, hrE⟩ := hh r₀ hr₀ hr₀p
    obtain ⟨s', hs', hz⟩ := (mem_genericName_iff P one _).mp hνs
    obtain ⟨h1, h2⟩ := kpair_iff.mp hz
    rw [h1] at hrE
    have hqs := atomicEquality_checkName_injective hR hone q s' r hrE
    rw [h2, ← hqs] at hrs
    exact hinc ⟨r, hr, hrr₀, hrs⟩
  · rintro ⟨hpP, hpq⟩
    have hpair : ⟨checkName one q, q⟩ₖ ∈ genericName P one :=
      (mem_genericName_iff P one _).mpr ⟨q, hq, rfl⟩
    exact atomicMembership_mono hR (atomicMembership_of_pair hR hq hpair) hpP hpq

/-- Conjunction introduction for the forcing relation. -/
theorem forcingFormula_and_intro {P R : V} {n : ℕ} {φ ψ : SetTheorySemisentence n} {b p : V}
    (hφ : p ∈ forcingFormula P R φ b) (hψ : p ∈ forcingFormula P R ψ b) :
    p ∈ forcingFormula P R (φ ⋏ ψ) b := by
  change p ∈ forcingFormula P R (.and φ ψ) b
  rw [forcingFormula_and]
  exact mem_inter_iff.mpr ⟨hφ, hψ⟩

theorem forcingFormula_and_elim {P R : V} {n : ℕ} {φ ψ : SetTheorySemisentence n} {b p : V}
    (h : p ∈ forcingFormula P R (φ ⋏ ψ) b) :
    p ∈ forcingFormula P R φ b ∧ p ∈ forcingFormula P R ψ b := by
  change p ∈ forcingFormula P R (.and φ ψ) b at h
  rw [forcingFormula_and] at h
  exact mem_inter_iff.mp h

/-- Existential introduction for the forcing relation. -/
theorem forcingFormula_exs_intro {P R : V} (hR : IsForcingPreorder P R) {n : ℕ}
    {φ : SetTheorySemisentence (n + 1)} {b p ν : V} (hν : IsForcingName P ν)
    (h : p ∈ forcingFormula P R φ (assignmentPrepend (n : V) b ν)) :
    p ∈ forcingFormula P R (.exs φ) b := by
  change p ∈ forcingFormula P R (.exs φ) b
  rw [forcingFormula_exs]
  unfold forcingExistential
  have hp : p ∈ P := (forcingFormula_regular hR φ _).1 p h
  refine subset_forcingClosure hR (forcingClassUnion_subset _ _ _ _ _) ?_ p
    ((mem_forcingClassUnion_iff _ _ _ _ _ _).mpr ⟨hp, ν, hν, h⟩)
  exact forcingClassUnion_downward _ _ _ _ (fun x _ ↦ (forcingFormula_regular hR φ _).2.1)

end ZFVP
