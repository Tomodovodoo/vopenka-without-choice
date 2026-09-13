import ZFVP.ModelTheory.LevyCollapseSubmodel

/-! Restricting a forcing context to a sub-poset containing the top condition, when the trace
of the generic on the sub-poset is generic: the intermediate extension `V[G ∩ Q]` is realized
inside `V[G]` by evaluating names over `Q` as names over `P`. This generalizes the Levy
subcollapse realization. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The order of `P` restricted to a subset `Q`. -/
noncomputable def restrictedOrder (R Q : V) : V := R ∩ (Q ×ˢ Q)

theorem kpair_mem_restrictedOrder_iff (R Q p q : V) :
    ⟨p, q⟩ₖ ∈ restrictedOrder R Q ↔ ⟨p, q⟩ₖ ∈ R ∧ p ∈ Q ∧ q ∈ Q := by
  unfold restrictedOrder
  rw [mem_inter_iff, kpair_mem_iff]

theorem restrictedOrder_preorder {P R Q : V} (hR : IsForcingPreorder P R) (hQ : Q ⊆ P) :
    IsForcingPreorder Q (restrictedOrder R Q) := by
  refine ⟨fun z hz ↦ (mem_inter_iff.mp hz).2, fun p hp ↦ ?_, ?_⟩
  · exact (kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨hR.2.1 p (hQ p hp), hp, hp⟩
  · intro p hp q hq r hr hpq hqr
    obtain ⟨hpq', _, _⟩ := (kpair_mem_restrictedOrder_iff _ _ _ _).mp hpq
    obtain ⟨hqr', _, _⟩ := (kpair_mem_restrictedOrder_iff _ _ _ _).mp hqr
    exact (kpair_mem_restrictedOrder_iff _ _ _ _).mpr
      ⟨hR.2.2 p (hQ p hp) q (hQ q hq) r (hQ r hr) hpq' hqr', hp, hr⟩

/-- The trace of a generic on a subset. -/
def traceGeneric (G : Set V) (Q : V) : Set V := {p | p ∈ G ∧ p ∈ Q}

namespace ForcingContext

variable (A : ForcingContext V) {Q : V} (hQ : Q ⊆ A.P) (hone : A.one ∈ Q)
  (hgen : IsExternalForcingGeneric Q (restrictedOrder A.R Q) (traceGeneric A.G Q))

/-- The restriction of a forcing context to a sub-poset with generic trace. -/
noncomputable def restrict : ForcingContext V where
  P := Q
  R := restrictedOrder A.R Q
  one := A.one
  G := traceGeneric A.G Q
  order := restrictedOrder_preorder A.order hQ
  top := ⟨hone, fun p hp ↦
    (kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨A.top.2 p (hQ p hp), hp, hone⟩⟩
  generic := hgen

theorem restrict_P : (A.restrict hQ hone hgen).P = Q := rfl

theorem restrict_G : (A.restrict hQ hone hgen).G = traceGeneric A.G Q := rfl

/-- `V[G ∩ Q]` realized inside `V[G]`. -/
noncomputable def restrictRealization : ForcingRealization (A.restrict hQ hone hgen) A.Model where
  ground := A.checkEmbedding
  genericSet := A.genericSet ∩ A.check Q
  generic_subset := fun x hx ↦ (mem_inter_iff.mp hx).2
  generic_mem := fun p ↦ by
    change A.check p ∈ _ ↔ p ∈ traceGeneric A.G Q
    rw [mem_inter_iff, A.check_mem_genericSet_iff, A.check_mem_iff]
    exact Iff.rfl

theorem restrictRealization_genericSet :
    (A.restrictRealization hQ hone hgen).genericSet = A.genericSet ∩ A.check Q := rfl

theorem restrictRealization_ground (x : V) :
    (A.restrictRealization hQ hone hgen).ground x = A.check x := rfl

/-- A name over the sub-poset is a name over the whole poset. -/
def liftName (τ : ForcingName (A.restrict hQ hone hgen).P) : ForcingName A.P :=
  ⟨τ.val, τ.property.mono hQ⟩

theorem liftName_val (τ : ForcingName (A.restrict hQ hone hgen).P) :
    (A.liftName hQ hone hgen τ).val = τ.val := rfl

/-- The value of a name over the sub-poset in the intermediate extension is its value as a
name over the whole poset. -/
theorem restrictRealization_value_ofName (τ : ForcingName (A.restrict hQ hone hgen).P) :
    (A.restrictRealization hQ hone hgen).value ((A.restrict hQ hone hgen).ofName τ) =
      A.ofName (A.liftName hQ hone hgen τ) := by
  rw [ForcingRealization.value_ofName, restrictRealization_genericSet, restrictRealization_ground]
  have hn : IsForcingName (A.check Q) (A.check τ.val) :=
    A.checkEmbedding.map_forcingName τ.property
  rw [nameValue_inter_of_name hn]
  exact A.nameValue_genericSet_check (A.liftName hQ hone hgen τ)

/-- Membership in the intermediate extension `V[G ∩ Q]`. -/
def InRestrictedModel (x : A.Model) : Prop := ∃ y, (A.restrictRealization hQ hone hgen).value y = x

theorem inRestrictedModel_ofName (τ : ForcingName (A.restrict hQ hone hgen).P) :
    A.InRestrictedModel hQ hone hgen (A.ofName (A.liftName hQ hone hgen τ)) :=
  ⟨_, A.restrictRealization_value_ofName hQ hone hgen τ⟩

theorem inRestrictedModel_iff (x : A.Model) :
    A.InRestrictedModel hQ hone hgen x ↔ ∃ τ : ForcingName (A.restrict hQ hone hgen).P,
      x = A.ofName (A.liftName hQ hone hgen τ) := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨τ, rfl⟩ := (A.restrict hQ hone hgen).ofName_surjective y
    exact ⟨τ, A.restrictRealization_value_ofName hQ hone hgen τ⟩
  · rintro ⟨τ, rfl⟩
    exact A.inRestrictedModel_ofName hQ hone hgen τ

theorem inRestrictedModel_check (x : V) : A.InRestrictedModel hQ hone hgen (A.check x) :=
  ⟨(A.restrict hQ hone hgen).check x, (A.restrictRealization hQ hone hgen).value_check x⟩

/-- The intermediate extension is closed under membership: elements of a set of the intermediate
extension lie in it. -/
theorem inRestrictedModel_of_mem {x y : A.Model} (hx : A.InRestrictedModel hQ hone hgen x)
    (hy : y ∈ x) : A.InRestrictedModel hQ hone hgen y := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', _, rfl⟩ := (A.restrictRealization hQ hone hgen).value_endExtension x' hy
  exact ⟨y', rfl⟩

end ForcingContext

end ZFVP
