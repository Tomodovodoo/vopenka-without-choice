import ZFVP.ModelTheory.SchmerlCodedCofinalOrdinals
import ZFVP.SetTheory.FiniteSets

/-! The actual poset of finite subsets of a parameter in a coded model. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] codedSatisfies codedUnary codedBinary

noncomputable def codedParameterSet (M φ s : V) : V :=
  {x ∈ structureDomain M ; codedBinary M φ x s}

theorem mem_codedParameterSet (M φ s x : V) :
    x ∈ codedParameterSet M φ s ↔ x ∈ structureDomain M ∧ codedBinary M φ x s := mem_sep_iff

instance codedParameterSet_definable : ℒₛₑₜ-function₃[V] codedParameterSet := by
  have h : ℒₛₑₜ-relation₄[V] (fun A M φ s ↦ ∀ x,
      x ∈ A ↔ x ∈ structureDomain M ∧ codedBinary M φ x s) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedParameterSet]
  rfl

theorem codedParameterSet_isCodedDefinable (M : V) (φ : SetTheorySemisentence 2)
    {s : V} (hs : s ∈ structureDomain M) :
    IsCodedDefinableSet M (codedParameterSet M (encodeMembershipFormula φ) s) := by
  refine ⟨fun x hx ↦ ((mem_codedParameterSet _ _ _ _).mp hx).1,
    1, by simp, encodeMembershipFormula φ, ?_, standardTuple ![s], ?_, ?_⟩
  · exact encodeMembershipFormula_mem (V := V) φ
  · exact standardTuple_mem_function _ (by simpa using hs)
  · intro x hx
    rw [mem_codedParameterSet, and_iff_right hx]
    unfold codedBinary
    rfl

def finiteDomainFormula : SetTheorySemisentence 2 :=
  f“a s. !internallyFiniteFormula a ∧ a ⊆ s”

def finiteDomainOrderFormula : SetTheorySemisentence 3 :=
  f“a b s. !finiteDomainFormula a s ∧ !finiteDomainFormula b s ∧ a ⊆ b”

noncomputable def codedFiniteDomains (M s : V) : V :=
  codedParameterSet M (encodeMembershipFormula finiteDomainFormula) s

noncomputable def codedFiniteDomainOrder (M s : V) : V :=
  codedBinaryOn M (encodeMembershipFormula (“a b. a ⊆ b” : SetTheorySemisentence 2))
    (codedFiniteDomains M s) (codedFiniteDomains M s)

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp
attribute [local irreducible] codedParameterSet codedBinaryOn

instance codedFiniteDomains_definable : ℒₛₑₜ-function₂[V] codedFiniteDomains := by
  unfold codedFiniteDomains; definability

instance codedFiniteDomainOrder_definable : ℒₛₑₜ-function₂[V] codedFiniteDomainOrder := by
  unfold codedFiniteDomainOrder; definability

theorem codedFiniteDomains_isCodedDefinable {M s : V} (hs : s ∈ structureDomain M) :
    IsCodedDefinableSet M (codedFiniteDomains M s) :=
  codedParameterSet_isCodedDefinable M finiteDomainFormula hs

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] (R : BinaryRelationRepresentation (V := V) W)

theorem mem_parameterSet_iff (φ : SetTheorySemisentence 2) (s x : W) :
    (R.equiv x).val ∈ codedParameterSet R.code (encodeMembershipFormula φ) (R.equiv s).val ↔
      φ.Evalb ![x, s] := by
  rw [mem_codedParameterSet, R.codedBinary_iff]
  exact and_iff_right (by simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain]
    using (R.equiv x).property)

theorem parameter_relation_definable_of_formula {A : V} (φ : SetTheorySemisentence 3) (s : W)
    (hA : A ⊆ R.carrier ×ˢ R.carrier)
    (hφ : ∀ x y : W, ⟨(R.equiv x).val, (R.equiv y).val⟩ₖ ∈ A ↔ φ.Evalb ![x, y, s]) :
    IsCodedDefinableRelation R.code A := by
  refine ⟨by simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using hA,
    1, by simp, encodeMembershipFormula φ, ?_, standardTuple ![(R.equiv s).val], ?_, ?_⟩
  · exact encodeMembershipFormula_mem (V := V) φ
  · exact standardTuple_mem_function _ (by
      intro i
      fin_cases i
      simpa only [Matrix.cons_val_zero, BinaryRelationRepresentation.code, binaryRelationStructureCode_domain, Fin.mk_zero]
        using (R.equiv s).property)
  · intro x hx y hy
    have hxD : x ∈ R.carrier := by simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using hx
    have hyD : y ∈ R.carrier := by simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using hy
    let a : W := R.equiv.symm ⟨x, hxD⟩
    let b : W := R.equiv.symm ⟨y, hyD⟩
    have ha : (R.equiv a).val = x := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    have hb : (R.equiv b).val = y := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    have ht : (fun i ↦ (R.equiv ((![a, b, s] : Fin 3 → W) i)).val) =
        ![(R.equiv a).val, (R.equiv b).val, (R.equiv s).val] := by
      funext i
      fin_cases i <;> rfl
    have he := R.satisfies_iff φ ![a, b, s]
    rw [ht] at he
    have h := (hφ a b).trans he.symm
    rw [ha, hb] at h
    exact h

variable [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem finiteDomain_mem_iff (s a : W) :
    (R.equiv a).val ∈ codedFiniteDomains R.code (R.equiv s).val ↔
      IsInternallyFinite a ∧ a ⊆ s := by
  rw [codedFiniteDomains, R.mem_parameterSet_iff]
  simp [finiteDomainFormula]

theorem mem_finiteDomains_iff (s : W) (p : V) :
    p ∈ codedFiniteDomains R.code (R.equiv s).val ↔
      ∃ a : W, (R.equiv a).val = p ∧ IsInternallyFinite a ∧ a ⊆ s := by
  constructor
  · intro hp
    have hpD : p ∈ R.carrier := by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedParameterSet _ _ _ _).mp hp).1
    let a : W := R.equiv.symm ⟨p, hpD⟩
    have ha : (R.equiv a).val = p := congrArg Subtype.val (R.equiv.apply_symm_apply _)
    exact ⟨a, ha, (R.finiteDomain_mem_iff s a).mp (ha.symm ▸ hp)⟩
  · rintro ⟨a, rfl, ha⟩
    exact (R.finiteDomain_mem_iff s a).mpr ha

theorem finiteDomainOrder_iff (s a b : W) :
    ⟨(R.equiv a).val, (R.equiv b).val⟩ₖ ∈ codedFiniteDomainOrder R.code (R.equiv s).val ↔
      (IsInternallyFinite a ∧ a ⊆ s) ∧ (IsInternallyFinite b ∧ b ⊆ s) ∧ a ⊆ b := by
  rw [codedFiniteDomainOrder, pair_mem_codedBinaryOn, R.finiteDomain_mem_iff,
    R.finiteDomain_mem_iff, R.codedBinary_iff]
  simp

theorem finiteDomainOrder_isCodedDefinable (s : W) :
    IsCodedDefinableRelation R.code (codedFiniteDomainOrder R.code (R.equiv s).val) := by
  apply R.parameter_relation_definable_of_formula finiteDomainOrderFormula s
  · intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (codedBinaryOn_subset _ _ _ _ p hp)
    exact kpair_mem_iff.mpr ⟨by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedParameterSet _ _ _ _).mp ha).1, by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using
        ((mem_codedParameterSet _ _ _ _).mp hb).1⟩
  · intro a b
    rw [R.finiteDomainOrder_iff]
    simp [finiteDomainOrderFormula, finiteDomainFormula]

theorem finiteDomainOrder_poset (s : W) :
    IsForcingPoset (codedFiniteDomains R.code (R.equiv s).val)
      (codedFiniteDomainOrder R.code (R.equiv s).val) := by
  refine ⟨⟨codedBinaryOn_subset _ _ _ _, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨a, rfl, ha⟩ := (R.mem_finiteDomains_iff s p).mp hp
    exact (R.finiteDomainOrder_iff s a a).mpr ⟨ha, ha, subset_refl _⟩
  · intro p hp q hq r hr hpq hqr
    obtain ⟨a, rfl, ha⟩ := (R.mem_finiteDomains_iff s p).mp hp
    obtain ⟨b, rfl, _⟩ := (R.mem_finiteDomains_iff s q).mp hq
    obtain ⟨d, rfl, hd⟩ := (R.mem_finiteDomains_iff s r).mp hr
    exact (R.finiteDomainOrder_iff s a d).mpr ⟨ha, hd,
      subset_trans ((R.finiteDomainOrder_iff s a b).mp hpq).2.2
        ((R.finiteDomainOrder_iff s b d).mp hqr).2.2⟩
  · intro p hp q hq hpq hqp
    obtain ⟨a, rfl, _⟩ := (R.mem_finiteDomains_iff s p).mp hp
    obtain ⟨b, rfl, _⟩ := (R.mem_finiteDomains_iff s q).mp hq
    exact congrArg (fun a ↦ (R.equiv a).val) (SetTheory.subset_antisymm
      ((R.finiteDomainOrder_iff s a b).mp hpq).2.2
      ((R.finiteDomainOrder_iff s b a).mp hqp).2.2)

theorem finiteDomains_directedNoMax {s : W} (hs : IsInternallyInfinite s) :
    IsInternalDirectedNoMax (codedFiniteDomains R.code (R.equiv s).val)
      (codedFiniteDomainOrder R.code (R.equiv s).val) := by
  refine ⟨⟨(R.equiv (∅ : W)).val,
    (R.finiteDomain_mem_iff s ∅).mpr ⟨internallyFinite_empty, empty_subset _⟩⟩, ?_, ?_⟩
  · intro p hp q hq
    obtain ⟨a, rfl, ha⟩ := (R.mem_finiteDomains_iff s p).mp hp
    obtain ⟨b, rfl, hb⟩ := (R.mem_finiteDomains_iff s q).mp hq
    have hd : IsInternallyFinite (a ∪ b) ∧ a ∪ b ⊆ s :=
      ⟨internallyFinite_union ha.1 hb.1, fun x hx ↦ (mem_union_iff.mp hx).elim (ha.2 x) (hb.2 x)⟩
    exact ⟨(R.equiv (a ∪ b)).val, (R.finiteDomain_mem_iff s _).mpr hd,
      (R.finiteDomainOrder_iff s _ _).mpr ⟨ha, hd, subset_union_left _ _⟩,
      (R.finiteDomainOrder_iff s _ _).mpr ⟨hb, hd, subset_union_right _ _⟩⟩
  · rintro ⟨p, hp, hmax⟩
    obtain ⟨a, rfl, ha⟩ := (R.mem_finiteDomains_iff s p).mp hp
    apply hs
    apply internallyFinite_subset ha.1
    intro x hx
    have hxfin : IsInternallyFinite ({x} : W) := by
      simpa using internallyFinite_insert (internallyFinite_empty (V := W)) x
    have hxsub : ({x} : W) ⊆ s := by intro y hy; simpa only [mem_singleton_iff.mp hy] using hx
    have hle := ((R.finiteDomainOrder_iff s {x} a).mp
      (hmax _ ((R.finiteDomain_mem_iff s _).mpr ⟨hxfin, hxsub⟩))).2.2
    exact hle x (by simp)

theorem exists_cofinal_finiteDomain_chain {κ : V} (h : IsCodedRubin R.code κ)
    {s : W} (hs : IsInternallyInfinite s) :
    ∃ c, IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val)
      (codedFiniteDomainOrder R.code (R.equiv s).val) c :=
  h.1 _ _ (codedFiniteDomains_isCodedDefinable (by
      simpa only [BinaryRelationRepresentation.code, binaryRelationStructureCode_domain] using (R.equiv s).property))
    (R.finiteDomainOrder_isCodedDefinable s) (R.finiteDomainOrder_poset s) (R.finiteDomains_directedNoMax hs)

end ZFVP.BinaryRelationRepresentation
