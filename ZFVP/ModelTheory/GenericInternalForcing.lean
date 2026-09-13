import ZFVP.Syntax.InternalForcingRegular
import ZFVP.ModelTheory.GenericRegularForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R D n b φ ψ r args : V} {G : Set V}

theorem genericMeets_internalForcing_truth (hG : IsExternalForcingFilter P R G)
    (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n) :
    GenericMeets G (internalForcingSet P R D n truthCode b) := by
  rw [internalForcingSet_truth hn hb]
  obtain ⟨p, hp⟩ := hG.2.1
  exact ⟨p, hp, hG.1 p hp⟩

theorem genericMeets_internalForcing_falsity (hn : n ∈ (ω : V)) :
    ¬GenericMeets G (internalForcingSet P R D n falsityCode b) := by
  rw [internalForcingSet_falsity hn]
  rintro ⟨p, _, hp⟩
  exact not_mem_empty hp

theorem genericMeets_internalForcing_negAtom (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) (hb : b ∈ D ^ n) :
    GenericMeets G (internalForcingSet P R D n (negAtomCode r args) b) ↔
      ¬GenericMeets G (internalAtomicForcingSet P R n b r args) := by
  rw [internalForcingSet_negAtom hn ha hb]
  have hr := internalAtomicForcingSet_regular (b := b) hR ((membershipAtomicArguments_iff hn).mp ha)
  exact genericMeets_negation hR hG hr.1 hr.2.1

theorem genericMeets_internalForcing_and (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hφ : IsMembershipFormulaCode n φ)
    (hψ : IsMembershipFormulaCode n ψ) (hb : b ∈ D ^ n) :
    GenericMeets G (internalForcingSet P R D n (andCode φ ψ) b) ↔
      GenericMeets G (internalForcingSet P R D n φ b) ∧ GenericMeets G (internalForcingSet P R D n ψ b) := by
  rw [internalForcingSet_and hφ hψ hb]
  exact genericMeets_inter hG.1 (internalForcingSet_regular hR hφ hb).2.1 (internalForcingSet_regular hR hψ hb).2.1

theorem genericMeets_internalForcing_or (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hφ : IsMembershipFormulaCode n φ)
    (hψ : IsMembershipFormulaCode n ψ) (hb : b ∈ D ^ n) :
    GenericMeets G (internalForcingSet P R D n (orCode φ ψ) b) ↔
      GenericMeets G (internalForcingSet P R D n φ b) ∨ GenericMeets G (internalForcingSet P R D n ψ b) := by
  rw [internalForcingSet_or hφ hψ hb, genericMeets_closure hR hG]
  · exact genericMeets_union
  · intro p hp
    exact (mem_union_iff.mp hp).elim (internalForcingSet_subset P R D n φ b p) (internalForcingSet_subset P R D n ψ b p)
  · intro p hp q hq hqp
    exact mem_union_iff.mpr ((mem_union_iff.mp hp).elim
      (fun hp ↦ Or.inl ((internalForcingSet_regular hR hφ hb).2.1 p hp q hq hqp))
      (fun hp ↦ Or.inr ((internalForcingSet_regular hR hψ hb).2.1 p hp q hq hqp)))

theorem genericMeets_internalForcing_all (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (hb : b ∈ D ^ n) :
    GenericMeets G (internalForcingSet P R D n (allCode φ) b) ↔
      ∀ x ∈ D, GenericMeets G (internalForcingSet P R D (succ n) φ (assignmentPrepend n b x)) := by
  rw [internalForcingSet_all hn hφ hb]
  apply genericMeets_classIntersection hR hG
  intro x hx
  exact internalForcingSet_regular hR hφ (assignmentPrepend_mem_function hn hb hx)

theorem genericMeets_internalForcing_exists (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hn : n ∈ (ω : V))
    (hφ : IsMembershipFormulaCode (succ n) φ) (hb : b ∈ D ^ n) :
    GenericMeets G (internalForcingSet P R D n (existsCode φ) b) ↔
      ∃ x ∈ D, GenericMeets G (internalForcingSet P R D (succ n) φ (assignmentPrepend n b x)) := by
  rw [internalForcingSet_exists hn hφ hb]
  apply genericMeets_existential hR hG
  intro x hx
  exact (internalForcingSet_regular hR hφ (assignmentPrepend_mem_function hn hb hx)).2.1

end ZFVP
