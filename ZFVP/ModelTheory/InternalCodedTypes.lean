import ZFVP.ModelTheory.InternalCountableTheories
import ZFVP.ModelTheory.CodedElementaryEmbedding

/-! Internal countable types and realization in arbitrary structure codes.
Elementarity preserves realization by old tuples; it does not prevent a larger
structure from realizing a type at a new tuple. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def countableCodedTypeFormula : SetTheorySemisentence 2 :=
  f“n p. n ∈ !isω ∧ !internallyCountableFormula p ∧
    ∀ φ ∈ p, φ ∈ !formulaSetFormula (!membershipLanguageCodeFormula) (!isEmpty) n”

def realizesCodedTypeFormula : SetTheorySemisentence 4 :=
  f“M n p b. b ∈ !function.dfn (!structureDomainFormula M) n ∧
    ∀ φ ∈ p, !satisfiesFormula (!membershipLanguageCodeFormula) (!isEmpty) M (!isEmpty) n φ b”

def omitsCodedTypeFormula : SetTheorySemisentence 3 :=
  f“M n p. ∀ b, ¬!realizesCodedTypeFormula M n p b”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A type is a set of formulas in one internal tuple context. No completeness
or consistency is included in the typing and countability predicate. -/
def IsCountableCodedType (n p : V) : Prop :=
  n ∈ (ω : V) ∧ IsInternallyCountable p ∧ p ⊆ formulaSet membershipLanguageCode ∅ n

def RealizesCodedType (M n p b : V) : Prop :=
  b ∈ structureDomain M ^ n ∧ ∀ φ ∈ p, Satisfies membershipLanguageCode ∅ M ∅ n φ b

def OmitsCodedType (M n p : V) : Prop := ∀ b, ¬RealizesCodedType M n p b

instance countableCodedTypeFormula_defined :
    ℒₛₑₜ-relation[V] IsCountableCodedType via countableCodedTypeFormula :=
  ⟨fun v ↦ by simp [countableCodedTypeFormula, IsCountableCodedType, subset_def]⟩

instance countableCodedType_definable : ℒₛₑₜ-relation[V] IsCountableCodedType :=
  countableCodedTypeFormula_defined.to_definable

instance realizesCodedTypeFormula_defined :
    ℒₛₑₜ-relation₄[V] RealizesCodedType via realizesCodedTypeFormula :=
  ⟨fun v ↦ by simp [realizesCodedTypeFormula, RealizesCodedType]⟩

instance realizesCodedType_definable : ℒₛₑₜ-relation₄[V] RealizesCodedType :=
  realizesCodedTypeFormula_defined.to_definable

instance omitsCodedTypeFormula_defined :
    ℒₛₑₜ-relation₃[V] OmitsCodedType via omitsCodedTypeFormula :=
  ⟨fun v ↦ by simp [omitsCodedTypeFormula, OmitsCodedType]⟩

instance omitsCodedType_definable : ℒₛₑₜ-relation₃[V] OmitsCodedType :=
  omitsCodedTypeFormula_defined.to_definable

theorem IsCountableCodedType.subtype {n p q : V} (hp : IsCountableCodedType n p) (hqp : q ⊆ p) :
    IsCountableCodedType n q :=
  ⟨hp.1, internallyCountable_subset hp.2.1 hqp, subset_trans hqp hp.2.2⟩

theorem IsCountableCodedType.union {n p q : V} (hp : IsCountableCodedType n p)
    (hq : IsCountableCodedType n q) : IsCountableCodedType n (p ∪ q) :=
  ⟨hp.1, internallyCountable_union hp.2.1 hq.2.1,
    fun _ h ↦ (mem_union_iff.mp h).elim (hp.2.2 _) (hq.2.2 _)⟩

theorem RealizesCodedType.subtype {M n p q b : V} (h : RealizesCodedType M n p b) (hqp : q ⊆ p) :
    RealizesCodedType M n q b := ⟨h.1, fun φ hφ ↦ h.2 φ (hqp _ hφ)⟩

theorem realizesCodedType_union_iff (M n p q b : V) :
    RealizesCodedType M n (p ∪ q) b ↔ RealizesCodedType M n p b ∧ RealizesCodedType M n q b := by
  constructor
  · intro h
    exact ⟨h.subtype (fun _ hφ ↦ mem_union_iff.mpr (Or.inl hφ)),
      h.subtype (fun _ hφ ↦ mem_union_iff.mpr (Or.inr hφ))⟩
  · rintro ⟨hp, hq⟩
    exact ⟨hp.1, fun φ hφ ↦ (mem_union_iff.mp hφ).elim (hp.2 φ) (hq.2 φ)⟩

theorem omitsCodedType_iff (M n p : V) : OmitsCodedType M n p ↔
    ∀ b ∈ structureDomain M ^ n, ∃ φ ∈ p, ¬Satisfies membershipLanguageCode ∅ M ∅ n φ b := by
  classical
  simp only [OmitsCodedType, RealizesCodedType]
  push Not
  rfl

theorem IsCodedElementaryEmbedding.realizesCodedType_iff {M N f n p b : V}
    (h : IsCodedElementaryEmbedding membershipLanguageCode M N f)
    (hp : IsCountableCodedType n p) (hb : b ∈ structureDomain M ^ n) :
    RealizesCodedType M n p b ↔ RealizesCodedType N n p (compose b f) := by
  have hbN := compose_function hb h.function
  simp only [RealizesCodedType, hb, hbN, true_and]
  exact forall_congr' fun φ ↦ imp_congr_right fun hφ ↦ h.satisfies_iff hp.1 (hp.2.2 φ hφ) hb

/-- Omission in the target implies omission in the source. The reverse
implication would need a separate omitting-types construction. -/
theorem IsCodedElementaryEmbedding.omitsCodedType_source {M N f n p : V}
    (h : IsCodedElementaryEmbedding membershipLanguageCode M N f)
    (hp : IsCountableCodedType n p) (hN : OmitsCodedType N n p) : OmitsCodedType M n p := by
  intro b hb
  exact hN (compose b f) ((h.realizesCodedType_iff hp hb.1).mp hb)

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_countableCodedType_iff (j : ElementaryMap V W) (n p : V) :
    IsCountableCodedType (j n) (j p) ↔ IsCountableCodedType n p :=
  (j.map_defined countableCodedTypeFormula
    (fun v ↦ IsCountableCodedType (v 0) (v 1))
    (fun v ↦ IsCountableCodedType (v 0) (v 1)) ![n, p]).symm

theorem map_realizesCodedType_iff (j : ElementaryMap V W) (M n p b : V) :
    RealizesCodedType (j M) (j n) (j p) (j b) ↔ RealizesCodedType M n p b :=
  (j.map_defined realizesCodedTypeFormula
    (fun v ↦ RealizesCodedType (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ RealizesCodedType (v 0) (v 1) (v 2) (v 3)) ![M, n, p, b]).symm

theorem map_omitsCodedType_iff (j : ElementaryMap V W) (M n p : V) :
    OmitsCodedType (j M) (j n) (j p) ↔ OmitsCodedType M n p :=
  (j.map_defined omitsCodedTypeFormula
    (fun v ↦ OmitsCodedType (v 0) (v 1) (v 2))
    (fun v ↦ OmitsCodedType (v 0) (v 1) (v 2)) ![M, n, p]).symm

end ElementaryMap

end ZFVP
