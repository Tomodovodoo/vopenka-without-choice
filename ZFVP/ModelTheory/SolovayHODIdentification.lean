import ZFVP.ModelTheory.SolovayModel
import ZFVP.ModelTheory.SolovayHODBridge

/-! The two descriptions of the Solovay model agree.

`SolovayHOD κ hG` is the class `HOD` of the extension computed from the parameter class named by
`solovayPf` at `solovayParam κ hG`; `(levyContext κ hG).SolovayModel` is the class of sets that are
hereditarily definable in the extension from ground sets, reals and ordinals. Over the Levy
collapse the two predicates on the extension are equivalent, so the two class models are the same
subtype of the extension up to an equivalence that preserves and reflects membership.

The file also records the tool later modules use to enter `SolovayModel`: a transitive set (or a
definable transitive class) all of whose members are definable from ground sets, reals and
ordinals consists of hereditarily so definable sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The transitive closure of a singleton is the point together with the transitive closure of the
point. Only the inclusion used below is stated. -/
theorem transitiveClosure_singleton_subset_insert (x : V) :
    transitiveClosure ({x} : V) ⊆ insert x (transitiveClosure x) := by
  refine transitiveClosure_minimal _ _ ?_ ⟨fun y hy z hz ↦ ?_⟩
  · rw [singleton_subset_iff_mem]
    exact mem_insert.mpr (Or.inl rfl)
  · rcases mem_insert.mp hy with rfl | hy
    · exact mem_insert.mpr (Or.inr (subset_transitiveClosure y z hz))
    · exact mem_insert.mpr (Or.inr ((transitiveClosure_transitive x).mem_trans hz hy))

namespace ForcingContext

/-- Everything in a transitive set of sets definable from ground sets, reals and ordinals is
hereditarily definable from those parameters. -/
theorem hereditarilyGroundRealDefinable_of_transitive (A : ForcingContext V) (T : A.Model)
    (hT : IsTransitive T) (hdef : ∀ y ∈ T, A.IsGroundRealDefinable y)
    {x : A.Model} (hx : x ∈ T) : A.IsHereditarilyGroundRealDefinable x := by
  intro y hy
  refine hdef y (transitiveClosure_minimal _ _ ?_ hT y hy)
  rw [singleton_subset_iff_mem]
  exact hx

/-- The same statement for a definable class `W` closed under members: the sets in `W` are
hereditarily definable from ground sets, reals and ordinals. -/
theorem hereditarilyGroundRealDefinable_of_definable_transitive (A : ForcingContext V)
    (W : A.Model → Prop) (hW : ℒₛₑₜ-predicate W)
    (htr : ∀ x, W x → ∀ y ∈ x, W y) (hdef : ∀ x, W x → A.IsGroundRealDefinable x)
    {x : A.Model} (hx : W x) : A.IsHereditarilyGroundRealDefinable x := by
  set T : A.Model := sep (transitiveClosure ({x} : A.Model)) W hW with hTdef
  have hmemT : ∀ y : A.Model, y ∈ T ↔ y ∈ transitiveClosure ({x} : A.Model) ∧ W y := fun y ↦
    mem_sep_iff
  have hTtr : IsTransitive T := by
    refine ⟨fun y hy z hz ↦ ?_⟩
    obtain ⟨hy₁, hy₂⟩ := (hmemT y).mp hy
    exact (hmemT z).mpr
      ⟨(transitiveClosure_transitive ({x} : A.Model)).mem_trans hz hy₁, htr y hy₂ z hz⟩
  have hxT : x ∈ T :=
    (hmemT x).mpr ⟨self_mem_transitiveClosure_singleton x, hx⟩
  exact hereditarilyGroundRealDefinable_of_transitive A T hTtr
    (fun y hy ↦ hdef y ((hmemT y).mp hy).2) hxT

end ForcingContext

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The two descriptions of the Solovay model define the same sets: a set of the Levy extension is
hereditarily ordinal definable from the class named by `solovayPf` exactly when it is hereditarily
definable from ground sets, reals and ordinals. -/
theorem solovay_isHOD_iff (x : (levyContext κ hG).Model) :
    IsHOD solovayPf x (solovayParam κ hG) ↔
      (levyContext κ hG).IsHereditarilyGroundRealDefinable x := by
  constructor
  · intro hx y hy
    refine solovayPf_groundRealDefinable hAC hU hc hω hκ hG y ?_
    rcases mem_insert.mp (transitiveClosure_singleton_subset_insert x y hy) with rfl | hy'
    · exact hx.1
    · exact hx.2 y hy'
  · intro hx
    exact ForcingContext.isHOD_of_hereditarilyGroundRealDefinable (levyContext κ hG) solovayPf
      (solovayPf_check hAC hU hc hω hκ hG) (solovayPf_real hG) hx

include hAC hU hc hω hκ in
/-- The two class models are the same collection of sets of the extension. -/
noncomputable def solovayHODEquiv : SolovayHOD κ hG ≃ (levyContext κ hG).SolovayModel where
  toFun x := ⟨x.val, (solovay_isHOD_iff hAC hU hc hω hκ hG x.val).mp
    (hod_val_isHOD solovayPf (solovayParam κ hG) x)⟩
  invFun y := toHOD solovayPf (solovayParam κ hG)
    ((solovay_isHOD_iff hAC hU hc hω hκ hG y.val).mpr y.property)
  left_inv _ := rfl
  right_inv _ := rfl

theorem solovayHODEquiv_val (x : SolovayHOD κ hG) :
    ((solovayHODEquiv hAC hU hc hω hκ hG x).val : (levyContext κ hG).Model) = x.val := rfl

theorem solovayHODEquiv_symm_val (y : (levyContext κ hG).SolovayModel) :
    (((solovayHODEquiv hAC hU hc hω hκ hG).symm y).val : (levyContext κ hG).Model) = y.val := rfl

/-- The equivalence preserves and reflects membership: both sides carry the membership of the
extension. -/
theorem solovayHODEquiv_mem_iff (x y : SolovayHOD κ hG) :
    solovayHODEquiv hAC hU hc hω hκ hG x ∈ solovayHODEquiv hAC hU hc hω hκ hG y ↔ x ∈ y :=
  Iff.rfl

end

end ZFVP
