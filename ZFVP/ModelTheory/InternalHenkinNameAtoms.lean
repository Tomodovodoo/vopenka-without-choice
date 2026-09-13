import ZFVP.ModelTheory.InternalHenkinAcceptedAxioms
import ZFVP.Syntax.MembershipRenamingAtoms
import ZFVP.ModelTheory.InternalBinaryQuotientAtoms

/-! Atomic truth on names is an actual binary relation. The fixed bridge axiom
identifies the raw logical-equality token with the equality relation symbol. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableRel₅.comp

noncomputable def henkinNameRelation (T s a : V) : V :=
  {p ∈ (ω : V) ×ˢ (ω : V) ; HenkinNameHolds T s 2 (atomCode a (boundPairArguments 0 1))
    (standardTuple ![kpair.π₁ p, kpair.π₂ p])}

instance henkinNameRelation_definable : ℒₛₑₜ-function₃[V] henkinNameRelation := by
  have he : ℒₛₑₜ-relation₄[V] (fun A T s a ↦ ∀ p, p ∈ A ↔ p ∈ (ω : V) ×ˢ (ω : V) ∧
      HenkinNameHolds T s 2 (atomCode a (boundPairArguments 0 1)) (standardTuple ![kpair.π₁ p, kpair.π₂ p])) := by
    unfold standardTuple
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
    definability
  apply Language.Definable.of_iff he
  intro v
  change v 0 = henkinNameRelation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [henkinNameRelation, mem_sep_iff]

theorem henkinNameRelation_subset (T s a : V) : henkinNameRelation T s a ⊆ (ω : V) ×ˢ (ω : V) :=
  fun _ hp ↦ (mem_sep_iff.mp hp).1

theorem pair_mem_henkinNameRelation {T s a x y : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) :
    ⟨x, y⟩ₖ ∈ henkinNameRelation T s a ↔
      HenkinNameHolds T s 2 (atomCode a (boundPairArguments 0 1)) (standardTuple ![x, y]) := by
  simp only [henkinNameRelation, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  exact and_iff_right (mem_prod_iff.mpr ⟨x, hx, y, hy, rfl⟩)

theorem IsCompleteHenkinSequence.name_atom_pair_iff (hω : Schmerl.HasStandardOmega V)
    {T s n b a i j : V} (hs : IsCompleteHenkinSequence T s) (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n)
    (ha : a = equalityToken ∨ a = relationToken (0 : V) ∨ a = relationToken (1 : V)) (hi : i ∈ n) (hj : j ∈ n) :
    HenkinNameHolds T s n (atomCode a (boundPairArguments i j)) b ↔
      ⟨b ‘ i, b ‘ j⟩ₖ ∈ henkinNameRelation T s a := by
  let r : V := standardTuple ![i, j]
  have hr : r ∈ n ^ (2 : V) := standardTuple_mem_function _ (by
    intro k; exact Fin.cases hi (fun k ↦ Fin.cases hj (fun l ↦ Fin.elim0 l) k) k)
  have hzero : r ‘ (0 : V) = i := value_standardTuple _ (0 : Fin 2)
  have hone : r ‘ (1 : V) = j := value_standardTuple _ (1 : Fin 2)
  have hba : IsAtomicArguments membershipLanguageCode ∅ (2 : V) a (boundPairArguments 0 1) :=
    membershipPair_atomic (by simp) ha (by simp) (by simp)
  have hbase := (formulaSet_atoms membershipLanguageCode_valid (by simp) hba).1
  have hrename := hs.name_rename_iff hω (by simp) hn hr hbase hb
  rw [renameMembershipFormula_atom_pair (by simp) hn hr ha (by simp) (by simp), hzero, hone] at hrename
  have hcomp : compose r b = standardTuple ![b ‘ i, b ‘ j] := by
    have : IsFunction b := IsFunction.of_mem hb
    apply (compose_standardTuple ![i, j] b ?_).trans
    · rfl
    · intro k
      rw [domain_eq_of_mem_function hb]
      exact Fin.cases hi (fun k ↦ Fin.cases hj (fun l ↦ Fin.elim0 l) k) k
  rw [hcomp] at hrename
  exact hrename.trans (pair_mem_henkinNameRelation (function_value_mem hb hi) (function_value_mem hb hj)).symm

theorem IsCompleteHenkinSequence.name_logicalEquality_iff (hω : Schmerl.HasStandardOmega V)
    {T s b : V} (hs : IsCompleteHenkinSequence T s) (hb : b ∈ (ω : V) ^ (2 : V)) :
    HenkinNameHolds T s 2 (atomCode equalityToken (boundPairArguments 0 1)) b ↔
      HenkinNameHolds T s 2 (atomCode (relationToken 0) (boundPairArguments 0 1)) b := by
  have haL : IsAtomicArguments membershipLanguageCode ∅ (2 : V) equalityToken (boundPairArguments 0 1) :=
    membershipPair_atomic (by simp) (Or.inl rfl) (by simp) (by simp)
  have haR : IsAtomicArguments membershipLanguageCode ∅ (2 : V) (relationToken 0) (boundPairArguments 0 1) :=
    membershipPair_atomic (by simp) (Or.inr (Or.inl rfl)) (by simp) (by simp)
  have hL := formulaSet_atoms membershipLanguageCode_valid (by simp) haL
  have hR := formulaSet_atoms membershipLanguageCode_valid (by simp) haR
  have hbridge := hs.name_axiom hω (rawEqualityBridgeCode_valid (V := V))
    (mem_union_iff.mpr (Or.inr (by simp [canonicalEqualityOpenCodes]))) hb
  rw [rawEqualityBridgeCode,
    hs.name_and_iff hω (formulaSet_binary membershipLanguageCode_valid (by simp) hL.2 hR.1).2
      (formulaSet_binary membershipLanguageCode_valid (by simp) hR.2 hL.1).2 hb,
    hs.name_or_iff hω hL.2 hR.1 hb, hs.name_or_iff hω hR.2 hL.1 hb] at hbridge
  have hnegL := hs.name_negate_iff hω hL.1 hb
  have hnegR := hs.name_negate_iff hω hR.1 hb
  rw [negateFormula_atom membershipLanguageCode_valid (by simp) haL] at hnegL
  rw [negateFormula_atom membershipLanguageCode_valid (by simp) haR] at hnegR
  rw [hnegL, hnegR] at hbridge
  tauto

theorem IsCompleteHenkinSequence.nameRelations_equality (hω : Schmerl.HasStandardOmega V) {T s : V}
    (hs : IsCompleteHenkinSequence T s) :
    henkinNameRelation T s equalityToken = henkinNameRelation T s (relationToken 0) := by
  apply mem_ext
  intro p
  constructor <;> intro hp
  · obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (henkinNameRelation_subset _ _ _ _ hp)
    rw [pair_mem_henkinNameRelation hx hy] at hp ⊢
    exact (hs.name_logicalEquality_iff hω (standardTuple_mem_function _ (by
      intro k; exact Fin.cases hx (fun k ↦ Fin.cases hy (fun l ↦ Fin.elim0 l) k) k))).mp hp
  · obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (henkinNameRelation_subset _ _ _ _ hp)
    rw [pair_mem_henkinNameRelation hx hy] at hp ⊢
    exact (hs.name_logicalEquality_iff hω (standardTuple_mem_function _ (by
      intro k; exact Fin.cases hx (fun k ↦ Fin.cases hy (fun l ↦ Fin.elim0 l) k) k))).mpr hp

end ZFVP
