import ZFVP.ModelTheory.InfinitaryAdequateOmegaOneLimits

namespace ZFVP.Infinitary
open LO LO.FirstOrder
open WeakDirectedChain
universe u v w

noncomputable def omegaOneZero : OmegaOne :=
  Ordinal.enum (α := OmegaOne) (· < ·) ⟨0, by
    rw [Ordinal.type_toType]
    exact Ordinal.omega_pos 1⟩

theorem omegaOneZero_le (i : OmegaOne) : omegaOneZero ≤ i := by
  apply (Ordinal.typein_le_typein' (Ordinal.omega.{0} 1)).mp
  exact (Ordinal.typein_enum (α := OmegaOne) (· < ·) _).le.trans zero_le

theorem not_lt_omegaOneZero (i : OmegaOne) : ¬i < omegaOneZero := not_lt.mpr (omegaOneZero_le i)

instance countable_omegaOne_predecessors (j : OmegaOne) : Countable {i : OmegaOne // i < j} := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [← Ordinal.card_typein j]
  apply Cardinal.lt_aleph_one_iff.mp
  apply Cardinal.lt_omega_iff_card_lt.mp
  exact lt_of_lt_of_eq (Ordinal.typein_lt_type (α := OmegaOne) (· < ·) j) (Ordinal.type_toType _)

theorem omegaOneSucc_injective : Function.Injective omegaOneSucc := by
  intro i j h
  apply le_antisymm
  · exact (lt_omegaOneSucc_iff j i).mp (h ▸ lt_omegaOneSucc i)
  · exact (lt_omegaOneSucc_iff i j).mp (h.symm ▸ lt_omegaOneSucc j)

theorem weakElementaryMap_eq_of_apply
    {L : Language.{u}} [L.Eq] {T : Set (TaggedFormula L)}
    {M N : WeakModel.{u,v} L} {e f : WeakElementaryMap T M N}
    (h : ∀ x, e x = f x) : e = f := by
  have hfun : e.toFun = f.toFun := funext h
  cases e
  cases f
  cases hfun
  rfl

/-- All recursion nodes use one fixed code type. Incoming maps are stored only
for matching earlier codes, so the recursion has a fixed codomain. -/
structure AdequateOmegaOneNode {L : Language.{u}} [L.Eq] [L.Encodable]
    {Code : Type w} (realize : Code → WeakModel.{u,v} L) (S : Set (TaggedFormula L)) where
  code : Code
  adequate : (realize code).Adequate S
  incoming : ∀ (_i : OmegaOne) (c : Code),
    Option (WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) (realize c) (realize code))

namespace AdequateOmegaOneNode
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  {Code : Type w} {realize : Code → WeakModel.{u,v} L}

abbrev model (N : AdequateOmegaOneNode realize S) := realize N.code

abbrev Map (M N : WeakModel.{u,v} L) :=
  WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M N

def Grows {M N : WeakModel.{u,v} L} (e : Map (S := S) M N) : Prop :=
  ∀ {n} (φ : Formula L (n + 1)),
    ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
      ∀ b : Fin n → M.Domain, M.Q {x | Formula.WeakEval M.Q φ (x :> b)} →
        ∃ a : N.Domain, a ∉ Set.range e ∧ Formula.WeakEval N.Q φ (a :> e ∘ b)

structure Fits (base : Code) (j : OmegaOne)
    (H : ∀ i, i < j → AdequateOmegaOneNode realize S) (N : AdequateOmegaOneNode realize S) : Prop where
  maps : ∀ i (hi : i < j), ∃ e : Map (S := S) (H i hi).model N.model,
    N.incoming i (H i hi).code = some e ∧ e.FreezesSmallFibers
  composition : ∀ i k (hik : i < k) (hkj : k < j)
    (eik : Map (S := S) (H i (hik.trans hkj)).model (H k hkj).model)
    (ekj : Map (S := S) (H k hkj).model N.model)
    (eij : Map (S := S) (H i (hik.trans hkj)).model N.model),
    (H k hkj).incoming i (H i (hik.trans hkj)).code = some eik →
    N.incoming k (H k hkj).code = some ekj →
    N.incoming i (H i (hik.trans hkj)).code = some eij →
    ∀ x, ekj (eik x) = eij x
  grows : ∀ p (hp : p < j), omegaOneSucc p = j →
    ∀ e : Map (S := S) (H p hp).model N.model,
      N.incoming p (H p hp).code = some e → Grows e
  continuous : NonzeroLimitIndex j → ∀ x : N.model.Domain,
    ∃ i, ∃ hi : i < j, ∃ e : Map (S := S) (H i hi).model N.model,
      N.incoming i (H i hi).code = some e ∧ ∃ y, e y = x
  initial : (∀ i, ¬i < j) → N.code = base

structure History (base : Code) (j : OmegaOne) where
  node : ∀ i, i < j → AdequateOmegaOneNode realize S
  fits : ∀ i (hi : i < j), Fits base i (fun k hk ↦ node k (hk.trans hi)) (node i hi)

namespace History
variable {base : Code} {j : OmegaOne} (H : History (realize := realize) (S := S) base j)

noncomputable def strictMap (i k : {i : OmegaOne // i < j}) (h : i < k) :
    Map (S := S) (H.node i i.property).model (H.node k k.property).model :=
  ((H.fits k k.property).maps i h).choose

theorem strictMap_spec (i k : {i : OmegaOne // i < j}) (h : i < k) :
    (H.node k k.property).incoming i (H.node i i.property).code = some (H.strictMap i k h) ∧
      (H.strictMap i k h).FreezesSmallFibers :=
  ((H.fits k k.property).maps i h).choose_spec

noncomputable def map {i k : {i : OmegaOne // i < j}} (h : i ≤ k) :
    Map (S := S) (H.node i i.property).model (H.node k k.property).model :=
  if he : i = k then he ▸ WeakElementaryMap.id (H.node i i.property).model
  else H.strictMap i k (lt_of_le_of_ne h he)

@[simp] theorem map_self (i : {i : OmegaOne // i < j}) (h : i ≤ i) :
    H.map h = WeakElementaryMap.id (H.node i i.property).model := by
  simp [map]

theorem map_eq_of_incoming {i k : {i : OmegaOne // i < j}} (h : i < k)
    (e : Map (S := S) (H.node i i.property).model (H.node k k.property).model)
    (he : (H.node k k.property).incoming i (H.node i i.property).code = some e) :
    H.map h.le = e := by
  rw [map, dite_eq_right (ne_of_lt h)]
  exact Option.some.inj ((H.strictMap_spec i k h).1.symm.trans he)

theorem map_freezes {i k : {i : OmegaOne // i < j}} (h : i ≤ k) : (H.map h).FreezesSmallFibers := by
  by_cases he : i = k
  · subst k
    rw [H.map_self]
    exact WeakElementaryMap.id_freezes _
  · rw [map, dite_eq_right he]
    exact (H.strictMap_spec i k (lt_of_le_of_ne h he)).2

theorem map_composition {i k l : {i : OmegaOne // i < j}} (hik : i ≤ k) (hkl : k ≤ l)
    (x : (H.node i i.property).model.Domain) : H.map hkl (H.map hik x) = H.map (hik.trans hkl) x := by
  by_cases he : i = k
  · subst k
    rw [H.map_self]
    rfl
  by_cases he' : k = l
  · subst l
    rw [H.map_self]
    rfl
  have hik' := lt_of_le_of_ne hik he
  have hkl' := lt_of_le_of_ne hkl he'
  have hil' := hik'.trans hkl'
  simp only [map, dite_eq_right he, dite_eq_right he', dite_eq_right (ne_of_lt hil')]
  exact (H.fits l l.property).composition i k hik' hkl'
    (H.strictMap i k hik') (H.strictMap k l hkl') (H.strictMap i l hil')
    (H.strictMap_spec i k hik').1 (H.strictMap_spec k l hkl').1 (H.strictMap_spec i l hil').1 x

noncomputable def diagram : CountableWeakDiagram.{u,v} {i : OmegaOne // i < j} (SequenceClosure.carrier S) where
  model := fun i ↦ (H.node i i.property).model
  map := H.map
  identity := fun i h x ↦ by rw [H.map_self]; rfl
  composition := H.map_composition

end History
end AdequateOmegaOneNode
end ZFVP.Infinitary

