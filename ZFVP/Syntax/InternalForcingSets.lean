import ZFVP.Syntax.InternalAtomicForcingRegular
import ZFVP.SetTheory.ForcingQuantifiers

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def internalForcingSet (P R D n φ b : V) : V := {p ∈ P ; InternalForces P R D n φ b p}

theorem mem_internalForcingSet_raw (P R D n φ b p : V) :
    p ∈ internalForcingSet P R D n φ b ↔ p ∈ P ∧ InternalForces P R D n φ b p := mem_sep_iff

instance internalForcingSet_definable (P R D : V) : ℒₛₑₜ-function₃[V] (internalForcingSet P R D) := by
  have h : ℒₛₑₜ-relation₄[V] (fun S n φ b ↦ ∀ p, p ∈ S ↔ p ∈ P ∧ InternalForces P R D n φ b p) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = internalForcingSet P R D (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp [internalForcingSet]

theorem internalForcingSet_subset (P R D n φ b : V) : internalForcingSet P R D n φ b ⊆ P := sep_subset

theorem mem_internalForcingSet {P R D n φ b p : V} (hφ : IsMembershipFormulaCode n φ) :
    p ∈ internalForcingSet P R D n φ b ↔ InternalForces P R D n φ b p := by
  simp only [internalForcingSet, mem_sep_iff]
  exact and_iff_right_of_imp (internalForces_condition hφ.valid)

theorem internalForcingSet_truth {P R D n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n truthCode b = P := by
  apply mem_ext
  intro p
  simp [internalForcingSet, internalForces_truth hn, hb]

theorem internalForcingSet_falsity {P R D n b : V} (hn : n ∈ (ω : V)) :
    internalForcingSet P R D n falsityCode b = ∅ := by
  apply mem_ext
  intro p
  simp [internalForcingSet, not_internalForces_falsity hn]

theorem internalForcingSet_atom {P R D n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (atomCode r args) b = internalAtomicForcingSet P R n b r args := by
  apply mem_ext
  intro p
  rw [mem_internalAtomicForcingSet]
  rw [mem_internalForcingSet_raw]
  exact and_congr_right fun hp ↦ internalForces_atom hn ha hb hp

theorem internalForcingSet_negAtom {P R D n b r args : V} (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (negAtomCode r args) b = forcingNegation P R (internalAtomicForcingSet P R n b r args) := by
  apply mem_ext
  intro p
  simp only [internalForcingSet, mem_sep_iff, mem_forcingNegation_iff]
  apply and_congr_right
  intro hp
  rw [internalForces_negAtom hn ha hb hp]
  exact forall_congr' fun q ↦ imp_congr_right fun hq ↦ imp_congr_right fun _ ↦
    not_congr (by simp [mem_internalAtomicForcingSet, hq])

theorem internalForcingSet_and {P R D n b φ ψ : V}
    (hφ : IsMembershipFormulaCode n φ) (hψ : IsMembershipFormulaCode n ψ) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (andCode φ ψ) b = internalForcingSet P R D n φ b ∩ internalForcingSet P R D n ψ b := by
  apply mem_ext
  intro p
  simp only [internalForcingSet, mem_sep_iff, mem_inter_iff]
  by_cases hp : p ∈ P
  · simp only [hp, true_and, internalForces_and hφ.context hφ.valid hψ.valid hb hp]
  · simp [hp]

theorem internalForcingSet_or {P R D n b φ ψ : V}
    (hφ : IsMembershipFormulaCode n φ) (hψ : IsMembershipFormulaCode n ψ) (hb : b ∈ D ^ n) :
    internalForcingSet P R D n (orCode φ ψ) b = forcingClosure P R
      (internalForcingSet P R D n φ b ∪ internalForcingSet P R D n ψ b) := by
  apply mem_ext
  intro p
  rw [show p ∈ internalForcingSet P R D n (orCode φ ψ) b ↔ p ∈ P ∧ InternalForces P R D n (orCode φ ψ) b p from mem_sep_iff,
    mem_forcingClosure_iff]
  apply and_congr_right
  intro hp
  rw [internalForces_or hφ.context hφ.valid hψ.valid hb hp]
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  simp only [mem_union_iff, mem_internalForcingSet hφ, mem_internalForcingSet hψ]
  constructor
  · rintro ⟨r, _, hrq, hr⟩
    exact ⟨r, hr, hrq⟩
  · rintro ⟨r, hr, hrq⟩
    have hrP : r ∈ P := hr.elim (internalForces_condition hφ.valid) (internalForces_condition hψ.valid)
    exact ⟨r, hrP, hrq, hr⟩

end ZFVP
