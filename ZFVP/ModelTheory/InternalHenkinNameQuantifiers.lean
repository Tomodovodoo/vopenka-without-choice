import ZFVP.ModelTheory.InternalHenkinExistentialWitness

/-! Quantifiers in the actual Henkin name table range over the actual set ω. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem function_eq_prepend_tail {n U r : V} (hn : n ∈ (ω : V)) (hr : r ∈ U ^ (succ n)) :
    r = assignmentPrepend n (compose (successorIndices n) r) (r ‘ (0 : V)) := by
  have hs := successorIndices_function hn
  apply function_eq_of_values hr (assignmentPrepend_mem_function hn (compose_function hs hr)
    (function_value_mem hr (zero_mem_succ_natural hn)))
  intro i hi
  rcases internalBoundIndex_cases hn hi with rfl | ⟨j, hj, rfl⟩
  · rw [assignmentPrepend_zero hn]
  · rw [assignmentPrepend_succ hn hj, value_compose_of_mem_function hs hr hj,
      show (successorIndices n) ‘ j = succ j from value_definableGraph _ _ _ hj]

theorem IsCompleteHenkinSequence.name_exists_of_witness (hω : Schmerl.HasStandardOmega V)
    {T s n φ b x : V} (hs : IsCompleteHenkinSequence T s) (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ (ω : V) ^ n) (hx : x ∈ (ω : V))
    (ha : HenkinNameHolds T s (succ n) φ (assignmentPrepend n b x)) :
    HenkinNameHolds T s n (existsCode φ) b := by
  have htuple := assignmentPrepend_mem_function hn hb hx
  obtain ⟨m, hm, r, hr, he⟩ := exists_reverseNameAssignment (ω_succ_closed hn) htuple
  let t := compose (successorIndices n) r
  have ht : t ∈ m ^ n := compose_function (successorIndices_function hn) hr
  have hi : r ‘ (0 : V) ∈ m := function_value_mem hr (zero_mem_succ_natural hn)
  have hbnames : b = compose t (reverseIndices m) := by
    rw [← successorIndices_compose_prepend hn hb hx, he, ← graph_compose_assoc]
  have hac := (henkinNameHolds_iff_of_rep hω hs hφ hm hr he).mp ha
  let χ := renameMembershipFormula (succ n) (succ m) (liftMembershipIndices n t) φ
  have hχ : χ ∈ formulaSet membershipLanguageCode ∅ (succ m) :=
    renameMembershipFormula_mem (ω_succ_closed hn) (ω_succ_closed hm)
      (liftMembershipIndices_function hn hm ht) hφ
  have hinst : instantiateMembershipFormula m (r ‘ (0 : V)) χ = renameMembershipFormula (succ n) m r φ := by
    dsimp only [χ]
    rw [instantiateMembershipFormula,
      renameMembershipFormula_compose (ω_succ_closed hn) (ω_succ_closed hm) hm
        (liftMembershipIndices_function hn hm ht) (assignmentPrepend_mem_function hm (identity_mem_function m) hi) hφ,
      liftMembershipIndices_compose_instantiate hn hm ht hi, ← function_eq_prepend_tail hn hr]
  have himp := CodedFormulaImplies.instantiate_exists T hm hi hχ
  rw [hinst] at himp
  have hacc := hac.consequence hω himp
  rw [henkinNameHolds_iff_of_rep hω hs (formulaSet_quantifiers membershipLanguageCode_valid hn hφ).2 hm ht hbnames,
    renameMembershipFormula_exists hn hm ht hφ]
  exact hacc

theorem henkinStages_name_exists_iff (hω : Schmerl.HasStandardOmega V) {T e n φ b : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ (ω : V) ^ n) :
    HenkinNameHolds T (henkinStages T e) n (existsCode φ) b ↔
      ∃ x ∈ (ω : V), HenkinNameHolds T (henkinStages T e) (succ n) φ (assignmentPrepend n b x) := by
  have hs := henkinStages_complete hω hT he hrange
  constructor
  · intro ha
    obtain ⟨m, hm, r, hr, hnames⟩ := exists_reverseNameAssignment hn hb
    have hac := (henkinNameHolds_iff_of_rep hω hs (formulaSet_quantifiers membershipLanguageCode_valid hn hφ).2
      hm hr hnames).mp ha
    rw [renameMembershipFormula_exists hn hm hr hφ] at hac
    let χ := renameMembershipFormula (succ n) (succ m) (liftMembershipIndices n r) φ
    have hχ : χ ∈ formulaSet membershipLanguageCode ∅ (succ m) :=
      renameMembershipFormula_mem (ω_succ_closed hn) (ω_succ_closed hm) (liftMembershipIndices_function hn hm hr) hφ
    obtain ⟨a, haω, hw⟩ := henkinStages_exists_witness hω hT he hrange hm hχ hac
    have hN := ordinalAdd_natural hm haω
    have htail := tailShiftIndices_function hm haω
    have hrep : assignmentPrepend m (reverseIndices m) (ordinalAdd m a) =
        compose (liftMembershipIndices m (tailShiftIndices m a)) (reverseIndices (succ (ordinalAdd m a))) := by
      rw [liftMembershipIndices_compose_reverse hm hN htail, tailShiftIndices_compose_reverse hm haω]
    have hbody := (henkinNameHolds_iff_of_rep hω hs hχ (ω_succ_closed hN)
      (liftMembershipIndices_function hm hN htail) hrep).mpr hw
    have hnamer := (hs.name_rename_iff hω (ω_succ_closed hn) (ω_succ_closed hm)
      (liftMembershipIndices_function hn hm hr) hφ
      (assignmentPrepend_mem_function hm (reverseIndices_omega_function hm) hN)).mp hbody
    rw [liftMembershipIndices_compose_prepend hn hm hr (reverseIndices_omega_function hm) hN, ← hnames] at hnamer
    exact ⟨ordinalAdd m a, hN, hnamer⟩
  · rintro ⟨x, hx, ha⟩
    exact hs.name_exists_of_witness hω hn hφ hb hx ha

theorem henkinStages_name_all_iff (hω : Schmerl.HasStandardOmega V) {T e n φ b : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅)
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) (hb : b ∈ (ω : V) ^ n) :
    HenkinNameHolds T (henkinStages T e) n (allCode φ) b ↔
      ∀ x ∈ (ω : V), HenkinNameHolds T (henkinStages T e) (succ n) φ (assignmentPrepend n b x) := by
  have hs := henkinStages_complete hω hT he hrange
  have hall := (formulaSet_quantifiers membershipLanguageCode_valid hn hφ).1
  have hneg := hs.name_negate_iff hω hall hb
  rw [negateFormula_all membershipLanguageCode_valid hn hφ,
    henkinStages_name_exists_iff hω hT he hrange hn (negateFormula_mem membershipLanguageCode_valid hφ) hb] at hneg
  have hbody : (∃ x ∈ (ω : V), HenkinNameHolds T (henkinStages T e) (succ n)
      (negateFormula membershipLanguageCode ∅ (succ n) φ) (assignmentPrepend n b x)) ↔
      ¬∀ x ∈ (ω : V), HenkinNameHolds T (henkinStages T e) (succ n) φ (assignmentPrepend n b x) := by
    simp only [not_forall, exists_prop]
    exact exists_congr fun x ↦ and_congr_right fun hx ↦
      hs.name_negate_iff hω hφ (assignmentPrepend_mem_function hn hb hx)
  exact not_iff_not.mp (hneg.symm.trans hbody)

end ZFVP
