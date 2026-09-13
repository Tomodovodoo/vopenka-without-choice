import ZFVP.ModelTheory.InternalNamedCompleteTheory
import ZFVP.Syntax.MembershipRenamingAtoms
import ZFVP.ModelTheory.InternalBinaryQuotientAtoms

/-! Source-valid consequences and raw renaming in the completed named table. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCompleteNamedTheory

theorem mem_iff_of_source_equiv {L M j B T p q : V} (h : IsCompleteNamedTheory L M j B T)
    (hL : IsLanguageCode L) (hp : p ∈ namedFormulaSet L (ω : V)) (hq : q ∈ namedFormulaSet L (ω : V))
    (he : ∀ f, SourceNaming M j f → (NamedHolds L M f p ↔ NamedHolds L M f q)) : p ∈ T ↔ q ∈ T :=
  ⟨fun hpT ↦ h.consequence_one hL hpT hq (fun f hf ↦ (he f hf).mp),
    fun hqT ↦ h.consequence_one hL hqT hp (fun f hf ↦ (he f hf).mpr)⟩

theorem source_universal {L M j B T n φ b : V} (h : IsCompleteNamedTheory L M j B T)
    (hL : IsLanguageCode L) (hφ : φ ∈ formulaSet L ∅ n) (hb : b ∈ (ω : V) ^ n)
    (hs : ∀ c ∈ structureDomain M ^ n, Satisfies L ∅ M ∅ n φ c) : TableHolds T n φ b := by
  apply h.consequence hL internallyFinite_empty (fun _ hh ↦ False.elim (not_mem_empty hh))
    ((pair_mem_namedFormulaSet_iff hL).mpr ⟨hφ, hb⟩)
  intro f hf _
  exact (namedHolds_pair _ _ _ _ _ _).mpr (hs _ (compose_function hb hf.1))

theorem name_rename_iff {M j B T n m r φ b : V}
    (h : IsCompleteNamedTheory membershipLanguageCode M j B T)
    (hM : IsStructureCode membershipLanguageCode M)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ (ω : V) ^ m) :
    TableHolds T m (renameMembershipFormula n m r φ) b ↔ TableHolds T n φ (compose r b) := by
  apply h.mem_iff_of_source_equiv hM.language
    ((pair_mem_namedFormulaSet_iff hM.language).mpr ⟨renameMembershipFormula_mem hn hm hr hφ, hb⟩)
    ((pair_mem_namedFormulaSet_iff hM.language).mpr ⟨hφ, compose_function hr hb⟩)
  intro f hf
  rw [namedHolds_pair, namedHolds_pair,
    codedMembershipSatisfies_rename hM hn hm hr hφ (compose_function hb hf.1), graph_compose_assoc]

end IsCompleteNamedTheory

noncomputable def namedTableRelation (T a : V) : V :=
  {p ∈ (ω : V) ×ˢ (ω : V) ; TableHolds T 2 (atomCode a (boundPairArguments 0 1))
    (standardTuple ![kpair.π₁ p, kpair.π₂ p])}

instance namedTableRelation_definable : ℒₛₑₜ-function₂[V] namedTableRelation := by
  have h : ℒₛₑₜ-relation₃[V] (fun A T a ↦ ∀ p, p ∈ A ↔ p ∈ (ω : V) ×ˢ (ω : V) ∧
      TableHolds T 2 (atomCode a (boundPairArguments 0 1)) (standardTuple ![kpair.π₁ p, kpair.π₂ p])) := by
    unfold standardTuple
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedTableRelation, mem_sep_iff]
  rfl

theorem namedTableRelation_subset (T a : V) : namedTableRelation T a ⊆ (ω : V) ×ˢ (ω : V) :=
  fun _ hp ↦ (mem_sep_iff.mp hp).1

theorem pair_mem_namedTableRelation {T a x y : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) :
    ⟨x, y⟩ₖ ∈ namedTableRelation T a ↔
      TableHolds T 2 (atomCode a (boundPairArguments 0 1)) (standardTuple ![x, y]) := by
  simp only [namedTableRelation, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  exact and_iff_right (kpair_mem_iff.mpr ⟨hx, hy⟩)

theorem IsCompleteNamedTheory.name_atom_pair_iff {M j B T n b a i k : V}
    (h : IsCompleteNamedTheory membershipLanguageCode M j B T)
    (hM : IsStructureCode membershipLanguageCode M) (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n)
    (ha : a = equalityToken ∨ a = relationToken (0 : V) ∨ a = relationToken (1 : V))
    (hi : i ∈ n) (hk : k ∈ n) :
    TableHolds T n (atomCode a (boundPairArguments i k)) b ↔
      ⟨b ‘ i, b ‘ k⟩ₖ ∈ namedTableRelation T a := by
  let r : V := standardTuple ![i, k]
  have hr : r ∈ n ^ (2 : V) := standardTuple_mem_function _ (by
    intro z; exact Fin.cases hi (fun z ↦ Fin.cases hk (fun l ↦ Fin.elim0 l) z) z)
  have hr0 : r ‘ (0 : V) = i := value_standardTuple _ (0 : Fin 2)
  have hr1 : r ‘ (1 : V) = k := value_standardTuple _ (1 : Fin 2)
  have hba := membershipPair_atomic (V := V) (i := (0 : V)) (j := (1 : V))
    (by simp : (2 : V) ∈ (ω : V)) ha (by simp) (by simp)
  have hrename := h.name_rename_iff hM (by simp) hn hr
    (formulaSet_atoms membershipLanguageCode_valid (by simp) hba).1 hb
  rw [renameMembershipFormula_atom_pair (by simp) hn hr ha (by simp) (by simp), hr0, hr1] at hrename
  have hcomp : compose r b = standardTuple ![b ‘ i, b ‘ k] := by
    have : IsFunction b := IsFunction.of_mem hb
    apply (compose_standardTuple ![i, k] b ?_).trans
    · rfl
    · intro z
      rw [domain_eq_of_mem_function hb]
      exact Fin.cases hi (fun z ↦ Fin.cases hk (fun l ↦ Fin.elim0 l) z) z
  rw [hcomp] at hrename
  exact hrename.trans (pair_mem_namedTableRelation (function_value_mem hb hi) (function_value_mem hb hk)).symm

end ZFVP
