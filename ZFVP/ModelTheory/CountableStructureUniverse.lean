import ZFVP.ModelTheory.BinaryRelationRepresentation
import ZFVP.SetTheory.CountableSets
import Foundation.FirstOrder.SetTheory.Universe
import Mathlib.Basic.Countable.Small

/-! Any countable set-language structure has an actual carrier and relation
inside the standard set universe. Only its nodes are encoded by naturals;
the represented relation may be externally ill founded. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable (M : Type*) [Countable M]

noncomputable def countableStructureNode (x : M) : Universe.{0} :=
  ((@Encodable.encode M (Encodable.ofCountable M) x : ℕ) : Universe.{0})

theorem countableStructureNode_injective : Function.Injective (countableStructureNode M) := by
  intro x y hxy
  apply @Encodable.encode_injective M (Encodable.ofCountable M)
  exact natCast_injective hxy

noncomputable def countableStructureCarrier : Universe.{0} :=
  Universe.mk (Set.range (countableStructureNode M))

theorem mem_countableStructureCarrier (z : Universe.{0}) :
    z ∈ countableStructureCarrier M ↔ ∃ x : M, countableStructureNode M x = z := by
  simp only [countableStructureCarrier, Universe.mem_mk, Set.mem_range]

theorem node_mem_countableStructureCarrier (x : M) :
    countableStructureNode M x ∈ countableStructureCarrier M :=
  (mem_countableStructureCarrier M _).mpr ⟨x, rfl⟩

theorem countableStructureCarrier_subset_omega : countableStructureCarrier M ⊆ (ω : Universe.{0}) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_countableStructureCarrier M z).mp hz
  simp [countableStructureNode]

theorem countableStructureCarrier_countable : IsInternallyCountable (countableStructureCarrier M) :=
  cardLE_of_subset (countableStructureCarrier_subset_omega M)

theorem countableStructureCarrier_nonempty [Nonempty M] :
    IsNonempty (countableStructureCarrier M) :=
  ⟨⟨countableStructureNode M (Classical.arbitrary M), node_mem_countableStructureCarrier M _⟩⟩

variable [SetStructure M]

noncomputable def countableStructureRelation : Universe.{0} :=
  Universe.mk (Set.range (fun p : {p : M × M // p.1 ∈ p.2} ↦
    ⟨countableStructureNode M p.val.1, countableStructureNode M p.val.2⟩ₖ))

theorem pair_mem_countableStructureRelation (x y : M) :
    ⟨countableStructureNode M x, countableStructureNode M y⟩ₖ ∈ countableStructureRelation M ↔ x ∈ y := by
  rw [countableStructureRelation, Universe.mem_mk]
  constructor
  · rintro ⟨⟨⟨u, v⟩, huv⟩, he⟩
    obtain ⟨hux, hvy⟩ := kpair_iff.mp he
    have hux' := countableStructureNode_injective M hux
    have hvy' := countableStructureNode_injective M hvy
    dsimp only at hux' hvy' huv
    subst u
    subst v
    exact huv
  · intro hxy
    exact ⟨⟨⟨x, y⟩, hxy⟩, rfl⟩

theorem countableStructureRelation_subset :
    countableStructureRelation M ⊆ countableStructureCarrier M ×ˢ countableStructureCarrier M := by
  intro z hz
  obtain ⟨⟨⟨x, y⟩, _⟩, rfl⟩ := Universe.mem_mk.mp hz
  exact kpair_mem_iff.mpr ⟨node_mem_countableStructureCarrier M x, node_mem_countableStructureCarrier M y⟩

noncomputable def countableStructureEquiv :
    M ≃ BinaryRelationDomain (countableStructureCarrier M) (countableStructureRelation M) :=
  Equiv.ofBijective (fun x ↦ ⟨countableStructureNode M x, node_mem_countableStructureCarrier M x⟩) (by
    constructor
    · intro x y he
      exact countableStructureNode_injective M (congrArg Subtype.val he)
    · intro z
      obtain ⟨x, hx⟩ := (mem_countableStructureCarrier M z.val).mp z.property
      exact ⟨x, Subtype.ext hx⟩)

theorem countableStructureEquiv_mem_iff (x y : M) :
    countableStructureEquiv M x ∈ countableStructureEquiv M y ↔ x ∈ y :=
  pair_mem_countableStructureRelation M x y

/-- No axioms, transitivity, or well-foundedness are required of the represented
structure. Nonemptiness supplies the usual nonempty first-order carrier. -/
noncomputable def countableStructureRepresentation [Nonempty M] :
    BinaryRelationRepresentation (V := Universe.{0}) M where
  carrier := countableStructureCarrier M
  relation := countableStructureRelation M
  carrier_nonempty := countableStructureCarrier_nonempty M
  relation_subset := countableStructureRelation_subset M
  equiv := countableStructureEquiv M
  mem_iff := fun x y ↦ (countableStructureEquiv_mem_iff M x y).symm

theorem countableStructure_satisfies_iff [Nonempty M] {n : ℕ}
    (φ : SetTheorySemisentence n) (b : Fin n → M) :
    Satisfies membershipLanguageCode ∅ (countableStructureRepresentation M).code ∅ (n : Universe.{0})
      (encodeMembershipFormula φ)
      (standardTuple (fun i ↦ countableStructureNode M (b i))) ↔ φ.Evalb b :=
  (countableStructureRepresentation M).satisfies_iff φ b

end ZFVP
