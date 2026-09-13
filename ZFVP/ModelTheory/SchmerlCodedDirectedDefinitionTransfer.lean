import ZFVP.ModelTheory.SchmerlCodedDefinitionInclusion

/-! The finite first-order assertion that two predicates define a directed
poset without a maximum transfers with their raw parameter definitions. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def IsPredicateDirectedPoset {M : Type*} (P : M → Prop) (R : M → M → Prop) : Prop :=
  (∀ x y, R x y → P x ∧ P y) ∧
  (∀ x, P x → R x x) ∧
  (∀ x y z, P x → P y → P z → R x y → R y z → R x z) ∧
  (∀ x y, P x → P y → R x y → R y x → x = y) ∧
  (∃ x, P x) ∧
  (∀ x y, P x → P y → ∃ z, P z ∧ R x z ∧ R y z) ∧
  ¬∃ m, P m ∧ ∀ x, P x → R x m

def directedPosetDefinitionFormula {ξ : Type*}
    (δ : SetTheorySemiformula ξ 1) (ρ : SetTheorySemiformula ξ 2) : SetTheorySemiformula ξ 0 :=
  “(∀ x, ∀ y, !ρ x y → !δ x ∧ !δ y) ∧
    (∀ x, !δ x → !ρ x x) ∧
    (∀ x, ∀ y, ∀ z, !δ x → !δ y → !δ z → !ρ x y → !ρ y z → !ρ x z) ∧
    (∀ x, ∀ y, !δ x → !δ y → !ρ x y → !ρ y x → x = y) ∧
    (∃ x, !δ x) ∧
    (∀ x, ∀ y, !δ x → !δ y → ∃ z, !δ z ∧ !ρ x z ∧ !ρ y z) ∧
    ¬∃ m, !δ m ∧ ∀ x, !δ x → !ρ x m”

theorem eval_directedPosetDefinitionFormula {M ξ : Type*} [SetStructure M]
    (δ : SetTheorySemiformula ξ 1) (ρ : SetTheorySemiformula ξ 2) (a : ξ → M) :
    (directedPosetDefinitionFormula δ ρ).Eval ![] a ↔
      IsPredicateDirectedPoset (fun x ↦ δ.Eval ![x] a) (fun x y ↦ ρ.Eval ![x, y] a) := by
  classical
  simp [directedPosetDefinitionFormula, IsPredicateDirectedPoset, or_iff_not_imp_left]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binaryPredicateDirectedPoset_iff {D E P R : V}
    (hP : P ⊆ D) (hR : R ⊆ D ×ˢ D) :
    IsPredicateDirectedPoset (fun x : BinaryRelationDomain D E ↦ x.val ∈ P)
      (fun x y ↦ ⟨x.val, y.val⟩ₖ ∈ R) ↔ IsForcingPoset P R ∧ IsInternalDirectedNoMax P R := by
  constructor
  · rintro ⟨hsub, href, htrans, hanti, hne, hdir, hmax⟩
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (hR p hp)
      exact kpair_mem_iff.mpr (hsub ⟨x, hx⟩ ⟨y, hy⟩ hp)
    · intro x hx
      exact href ⟨x, hP x hx⟩ hx
    · intro x hx y hy z hz hxy hyz
      exact htrans ⟨x, hP x hx⟩ ⟨y, hP y hy⟩ ⟨z, hP z hz⟩ hx hy hz hxy hyz
    · intro x hx y hy hxy hyx
      exact congrArg Subtype.val (hanti ⟨x, hP x hx⟩ ⟨y, hP y hy⟩ hx hy hxy hyx)
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x.val, hx⟩
    · intro x hx y hy
      obtain ⟨z, hz, hxz, hyz⟩ := hdir ⟨x, hP x hx⟩ ⟨y, hP y hy⟩ hx hy
      exact ⟨z.val, hz, hxz, hyz⟩
    · rintro ⟨m, hm, htop⟩
      exact hmax ⟨⟨m, hP m hm⟩, hm, fun x hx ↦ htop x.val hx⟩
  · rintro ⟨hpos, hdir⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x y hxy
      exact kpair_mem_iff.mp (hpos.1.1 _ hxy)
    · intro x hx
      exact hpos.1.2.1 x.val hx
    · intro x y z hx hy hz hxy hyz
      exact hpos.1.2.2 x.val hx y.val hy z.val hz hxy hyz
    · intro x y hx hy hxy hyx
      exact Subtype.ext (hpos.2 x.val hx y.val hy hxy hyx)
    · obtain ⟨x, hx⟩ := hdir.1
      exact ⟨⟨x, hP x hx⟩, hx⟩
    · intro x y hx hy
      obtain ⟨z, hz, hxz, hyz⟩ := hdir.2.1 x.val hx y.val hy
      exact ⟨⟨z, hP z hz⟩, hz, hxz, hyz⟩
    · rintro ⟨m, hm, htop⟩
      exact hdir.2.2 ⟨m.val, hm, fun x hx ↦ htop ⟨x, hP x hx⟩ hx⟩

theorem binary_eval_directedPosetDefinitionFormula_iff {D E P R : V} {ξ : Type*}
    (δ : SetTheorySemiformula ξ 1) (ρ : SetTheorySemiformula ξ 2)
    (a : ξ → BinaryRelationDomain D E) (hP : P ⊆ D) (hR : R ⊆ D ×ˢ D)
    (hδ : ∀ x : BinaryRelationDomain D E, δ.Eval ![x] a ↔ x.val ∈ P)
    (hρ : ∀ x y : BinaryRelationDomain D E, ρ.Eval ![x, y] a ↔ ⟨x.val, y.val⟩ₖ ∈ R) :
    (directedPosetDefinitionFormula δ ρ).Eval ![] a ↔ IsForcingPoset P R ∧ IsInternalDirectedNoMax P R := by
  rw [eval_directedPosetDefinitionFormula]
  have hδ' : (fun x : BinaryRelationDomain D E ↦ δ.Eval ![x] a) = (fun x ↦ x.val ∈ P) :=
    funext (fun x ↦ propext (hδ x))
  have hρ' : (fun x y : BinaryRelationDomain D E ↦ ρ.Eval ![x, y] a) = (fun x y ↦ ⟨x.val, y.val⟩ₖ ∈ R) :=
    funext (fun x ↦ funext (fun y ↦ propext (hρ x y)))
  rw [hδ', hρ']
  exact binaryPredicateDirectedPoset_iff hP hR

theorem binaryInclusion_directedDefinitions_iff (hω : HasStandardOmega V) {D E B S u r : V}
    (he : IsCodedElementaryInclusion (binaryRelationStructureCode D E) (binaryRelationStructureCode B S))
    (hu : u ∈ unaryDefinitionParameters (binaryRelationStructureCode D E))
    (hr : r ∈ binaryDefinitionParameters (binaryRelationStructureCode D E)) :
    (IsForcingPoset (unaryDefinitionSet (binaryRelationStructureCode D E) u)
        (binaryDefinitionRelation (binaryRelationStructureCode D E) r) ∧
      IsInternalDirectedNoMax (unaryDefinitionSet (binaryRelationStructureCode D E) u)
        (binaryDefinitionRelation (binaryRelationStructureCode D E) r)) ↔
    (IsForcingPoset (unaryDefinitionSet (binaryRelationStructureCode B S) u)
        (binaryDefinitionRelation (binaryRelationStructureCode B S) r) ∧
      IsInternalDirectedNoMax (unaryDefinitionSet (binaryRelationStructureCode B S) u)
        (binaryDefinitionRelation (binaryRelationStructureCode B S) r)) := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using he.source.domain_nonempty
  have hB : IsNonempty B := by simpa only [binaryRelationStructureCode_domain] using he.target.domain_nonempty
  have hDB : D ⊆ B := by simpa only [binaryRelationStructureCode_domain] using he.subset
  obtain ⟨δ, hδ⟩ := exists_unaryDefinition_uniformFormula hω hu
  obtain ⟨ρ, hρ⟩ := exists_binaryDefinition_uniformFormula hω hr
  have hδD (x : BinaryRelationDomain D E) : δ.Eval ![x] id ↔ x.val ∈ unaryDefinitionSet (binaryRelationStructureCode D E) u := by
    exact hδ D E hD (subset_refl D) x
  have hρD (x y : BinaryRelationDomain D E) : ρ.Eval ![x, y] id ↔ ⟨x.val, y.val⟩ₖ ∈ binaryDefinitionRelation (binaryRelationStructureCode D E) r := by
    exact hρ D E hD (subset_refl D) x y
  have hs := binaryInclusion_eval he hDB (directedPosetDefinitionFormula δ ρ) (![] : Fin 0 → BinaryRelationDomain D E) id
  have hleft := binary_eval_directedPosetDefinitionFormula_iff δ ρ id
    (by simpa only [binaryRelationStructureCode_domain] using unaryDefinitionSet_subset (binaryRelationStructureCode D E) u)
    (by simpa only [binaryRelationStructureCode_domain] using binaryDefinitionRelation_subset (binaryRelationStructureCode D E) r) hδD hρD
  have hright := binary_eval_directedPosetDefinitionFormula_iff δ ρ (binaryCarrierInclusion hDB)
    (by simpa only [binaryRelationStructureCode_domain] using unaryDefinitionSet_subset (binaryRelationStructureCode B S) u)
    (by simpa only [binaryRelationStructureCode_domain] using binaryDefinitionRelation_subset (binaryRelationStructureCode B S) r)
    (hδ B S hB hDB) (hρ B S hB hDB)
  have heval : (directedPosetDefinitionFormula δ ρ).Eval ![] id ↔
      (directedPosetDefinitionFormula δ ρ).Eval ![] (binaryCarrierInclusion (S := S) hDB) := by
    simpa only [Matrix.empty_eq, Function.comp_id] using hs
  exact hleft.symm.trans (heval.trans hright)

theorem codedInclusion_directedDefinitions_iff (hω : HasStandardOmega V) {κ M N u r : V}
    (he : IsCodedElementaryInclusion M N) (hM : M ∈ boundedBinaryModelCodes κ)
    (hN : N ∈ boundedBinaryModelCodes κ)
    (hu : u ∈ unaryDefinitionParameters M) (hr : r ∈ binaryDefinitionParameters M) :
    (IsForcingPoset (unaryDefinitionSet M u) (binaryDefinitionRelation M r) ∧
      IsInternalDirectedNoMax (unaryDefinitionSet M u) (binaryDefinitionRelation M r)) ↔
    (IsForcingPoset (unaryDefinitionSet N u) (binaryDefinitionRelation N r) ∧
      IsInternalDirectedNoMax (unaryDefinitionSet N u) (binaryDefinitionRelation N r)) := by
  obtain ⟨D, E, _, _, rfl⟩ := mem_boundedBinaryModelCodes.mp hM
  obtain ⟨B, S, _, _, rfl⟩ := mem_boundedBinaryModelCodes.mp hN
  exact binaryInclusion_directedDefinitions_iff hω he hu hr

end ZFVP.Schmerl
