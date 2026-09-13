import ZFVP.ModelTheory.BinaryRelationStructure
import ZFVP.SetTheory.CountableSets

/-! Quotients of actual internal binary prestructures. The quotient carrier,
edge relation, and surjective projection are sets in the ambient ZF model. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure IsInternalSetoid (D E : V) : Prop where
  subset : E ⊆ D ×ˢ D
  refl : ∀ x ∈ D, ⟨x, x⟩ₖ ∈ E
  symm : ∀ x ∈ D, ∀ y ∈ D, ⟨x, y⟩ₖ ∈ E → ⟨y, x⟩ₖ ∈ E
  trans : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, ⟨x, y⟩ₖ ∈ E → ⟨y, z⟩ₖ ∈ E → ⟨x, z⟩ₖ ∈ E

def IsInternalRelationCongruence (D E R : V) : Prop :=
  R ⊆ D ×ˢ D ∧ ∀ x ∈ D, ∀ y ∈ D, ∀ x' ∈ D, ∀ y' ∈ D,
    ⟨x, x'⟩ₖ ∈ E → ⟨y, y'⟩ₖ ∈ E → (⟨x, y⟩ₖ ∈ R ↔ ⟨x', y'⟩ₖ ∈ R)

noncomputable def internalEquivalenceClass (D E x : V) : V := {y ∈ D ; ⟨x, y⟩ₖ ∈ E}

@[simp] theorem mem_internalEquivalenceClass (D E x y : V) :
    y ∈ internalEquivalenceClass D E x ↔ y ∈ D ∧ ⟨x, y⟩ₖ ∈ E := mem_sep_iff

instance internalEquivalenceClass_definable : ℒₛₑₜ-function₃[V] internalEquivalenceClass := by
  have hh : ℒₛₑₜ-relation₄[V] (fun Q D E x ↦ ∀ y, y ∈ Q ↔ y ∈ D ∧ ⟨x, y⟩ₖ ∈ E) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_internalEquivalenceClass]
  rfl

noncomputable def internalQuotientCarrier (D E : V) : V :=
  repl (internalEquivalenceClass D E) (by definability) D

@[simp] theorem mem_internalQuotientCarrier (D E q : V) :
    q ∈ internalQuotientCarrier D E ↔ ∃ x ∈ D, q = internalEquivalenceClass D E x := repl_spec _

instance internalQuotientCarrier_definable : ℒₛₑₜ-function₂[V] internalQuotientCarrier := by
  have hh : ℒₛₑₜ-relation₃[V] (fun Q D E ↦ ∀ q, q ∈ Q ↔ ∃ x ∈ D, q = internalEquivalenceClass D E x) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_internalQuotientCarrier]
  rfl

noncomputable def internalQuotientProjection (D E : V) : V :=
  definableGraph D (internalEquivalenceClass D E) (by definability)

instance internalQuotientProjection_function (D E : V) : IsFunction (internalQuotientProjection D E) := by
  unfold internalQuotientProjection
  infer_instance

@[simp] theorem internalQuotientProjection_domain (D E : V) : domain (internalQuotientProjection D E) = D :=
  domain_definableGraph _ _ _

@[simp] theorem internalQuotientProjection_range (D E : V) :
    range (internalQuotientProjection D E) = internalQuotientCarrier D E := range_definableGraph _ _ _

@[simp] theorem internalQuotientProjection_value {D E x : V} (hx : x ∈ D) :
    (internalQuotientProjection D E) ‘ x = internalEquivalenceClass D E x := value_definableGraph _ _ _ hx

theorem internalQuotientProjection_mem (D E : V) :
    internalQuotientProjection D E ∈ internalQuotientCarrier D E ^ D := definableGraph_mem_function _ _ _

theorem internalQuotientCarrier_countable {D E : V} (hD : IsInternallyCountable D) :
    IsInternallyCountable (internalQuotientCarrier D E) := internallyCountable_repl _ _ hD

theorem internalQuotientCarrier_nonempty {D : V} (hD : IsNonempty D) (E : V) :
    IsNonempty (internalQuotientCarrier D E) := by
  obtain ⟨x, hx⟩ := hD
  exact ⟨internalEquivalenceClass D E x, (mem_internalQuotientCarrier _ _ _).mpr ⟨x, hx, rfl⟩⟩

theorem IsInternalSetoid.classes_eq_iff {D E x y : V} (h : IsInternalSetoid D E)
    (hx : x ∈ D) (hy : y ∈ D) :
    internalEquivalenceClass D E x = internalEquivalenceClass D E y ↔ ⟨x, y⟩ₖ ∈ E := by
  constructor
  · intro he
    have hh : y ∈ internalEquivalenceClass D E y := (mem_internalEquivalenceClass _ _ _ _).mpr ⟨hy, h.refl y hy⟩
    rw [← he] at hh
    exact ((mem_internalEquivalenceClass _ _ _ _).mp hh).2
  · intro he
    apply mem_ext
    intro z
    simp only [mem_internalEquivalenceClass]
    constructor
    · rintro ⟨hz, hxz⟩
      exact ⟨hz, h.trans y hy x hx z hz (h.symm x hx y hy he) hxz⟩
    · rintro ⟨hz, hyz⟩
      exact ⟨hz, h.trans x hx y hy z hz he hyz⟩

noncomputable def internalQuotientEdges (D E R : V) : V :=
  repl (fun p ↦ ⟨internalEquivalenceClass D E (kpair.π₁ p), internalEquivalenceClass D E (kpair.π₂ p)⟩ₖ)
    (by definability) R

theorem mem_internalQuotientEdges (D E R q : V) : q ∈ internalQuotientEdges D E R ↔
    ∃ p ∈ R, q = ⟨internalEquivalenceClass D E (kpair.π₁ p), internalEquivalenceClass D E (kpair.π₂ p)⟩ₖ :=
  repl_spec _

theorem internalQuotientEdges_subset {D E R : V} (hR : R ⊆ D ×ˢ D) :
    internalQuotientEdges D E R ⊆ internalQuotientCarrier D E ×ˢ internalQuotientCarrier D E := by
  intro p hp
  obtain ⟨r, hr, rfl⟩ := (mem_internalQuotientEdges _ _ _ _).mp hp
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (hR r hr)
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, kpair_mem_iff, mem_internalQuotientCarrier]
  exact ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

theorem IsInternalSetoid.quotient_edge_iff {D E R x y : V} (h : IsInternalSetoid D E)
    (hR : IsInternalRelationCongruence D E R) (hx : x ∈ D) (hy : y ∈ D) :
    ⟨internalEquivalenceClass D E x, internalEquivalenceClass D E y⟩ₖ ∈ internalQuotientEdges D E R ↔
      ⟨x, y⟩ₖ ∈ R := by
  constructor
  · intro he
    obtain ⟨r, hr, he⟩ := (mem_internalQuotientEdges _ _ _ _).mp he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (hR.1 r hr)
    simp only [kpair.π₁_kpair, kpair.π₂_kpair, kpair_iff] at he
    have hxa := (h.classes_eq_iff hx ha).mp he.1
    have hyb := (h.classes_eq_iff hy hb).mp he.2
    exact (hR.2 x hx y hy a ha b hb hxa hyb).mpr hr
  · intro hr
    exact (mem_internalQuotientEdges _ _ _ _).mpr ⟨⟨x, y⟩ₖ, hr, by simp⟩

noncomputable def internalQuotientStructure (D E R : V) : V :=
  binaryRelationStructureCode (internalQuotientCarrier D E) (internalQuotientEdges D E R)

theorem internalQuotientStructure_valid {D E R : V} (hD : IsNonempty D) :
    IsStructureCode membershipLanguageCode (internalQuotientStructure D E R) :=
  binaryRelationStructureCode_valid (internalQuotientCarrier_nonempty hD E) _

@[simp] theorem internalQuotientStructure_domain (D E R : V) :
    structureDomain (internalQuotientStructure D E R) = internalQuotientCarrier D E := by
  simp only [internalQuotientStructure, binaryRelationStructureCode_domain]

theorem internalQuotientStructure_countable {D E R : V} (hD : IsInternallyCountable D) :
    IsInternallyCountable (structureDomain (internalQuotientStructure D E R)) := by
  rw [internalQuotientStructure_domain]
  exact internalQuotientCarrier_countable hD

end ZFVP

