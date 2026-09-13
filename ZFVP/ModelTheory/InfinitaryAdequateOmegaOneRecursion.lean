import ZFVP.ModelTheory.InfinitaryAdequateOmegaOneExtension

namespace ZFVP.Infinitary
open LO LO.FirstOrder
open WeakDirectedChain
universe u v w
namespace AdequateOmegaOneNode
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  {Code : Type w} {realize : Code → WeakModel.{u,v} L}
  (base : Code) (hbase : (realize base).Adequate S)
  (grow : ∀ c : Code, (realize c).Adequate S →
    ∃ d : Code, ∃ e : Map (S := S) (realize c) (realize d),
      (realize d).Adequate S ∧ e.FreezesSmallFibers ∧ Grows e)
  (recode : ∀ N : WeakModel.{u,v} L, N.Adequate S →
    ∃ c : Code, ∃ e : Map (S := S) N (realize c),
      (realize c).Adequate S ∧ e.FreezesSmallFibers ∧ Function.Surjective e)

private noncomputable def nextNode (j : OmegaOne)
    (H : ∀ i, i < j → AdequateOmegaOneNode realize S) : AdequateOmegaOneNode realize S := by
  classical
  exact if h : ∀ i (hi : i < j), Fits base i (fun k hk ↦ H k (hk.trans hi)) (H i hi) then
    (exists_fit base hbase grow recode j ⟨H, h⟩).choose
  else ⟨base, hbase, fun _ _ ↦ none⟩

/-- Well-founded recursion into one fixed type of code records. The fallback
branch is never used on the recursively constructed history. -/
noncomputable def construction : OmegaOne → AdequateOmegaOneNode realize S :=
  (IsWellFounded.wf (α := OmegaOne) (r := (· < ·))).fix (nextNode base hbase grow recode)

private theorem construction_eq (j : OmegaOne) :
    construction base hbase grow recode j = nextNode base hbase grow recode j
      (fun i _ ↦ construction base hbase grow recode i) :=
  (IsWellFounded.wf (α := OmegaOne) (r := (· < ·))).fix_eq _ j

theorem construction_fits (j : OmegaOne) :
    Fits base j (fun i _ ↦ construction base hbase grow recode i)
      (construction base hbase grow recode j) := by
  classical
  induction j using (IsWellFounded.wf (α := OmegaOne) (r := (· < ·))).induction with
  | h j ih =>
    rw [construction_eq base hbase grow recode j]
    have hh : ∀ i (hi : i < j), Fits base i
        (fun k _ ↦ construction base hbase grow recode k) (construction base hbase grow recode i) := ih
    simp only [nextNode, dite_eq_left hh]
    exact (exists_fit base hbase grow recode j
      ⟨fun i _ ↦ construction base hbase grow recode i, hh⟩).choose_spec

noncomputable def strictMap (i j : OmegaOne) (h : i < j) :
    Map (S := S) (construction base hbase grow recode i).model
      (construction base hbase grow recode j).model :=
  ((construction_fits base hbase grow recode j).maps i h).choose

theorem strictMap_spec (i j : OmegaOne) (h : i < j) :
    (construction base hbase grow recode j).incoming i (construction base hbase grow recode i).code =
      some (strictMap base hbase grow recode i j h) ∧
      (strictMap base hbase grow recode i j h).FreezesSmallFibers :=
  ((construction_fits base hbase grow recode j).maps i h).choose_spec

noncomputable def map {i j : OmegaOne} (h : i ≤ j) :
    Map (S := S) (construction base hbase grow recode i).model
      (construction base hbase grow recode j).model :=
  if he : i = j then he ▸ WeakElementaryMap.id (construction base hbase grow recode i).model
  else strictMap base hbase grow recode i j (lt_of_le_of_ne h he)

@[simp] theorem map_self (i : OmegaOne) (h : i ≤ i) :
    map base hbase grow recode h = WeakElementaryMap.id (construction base hbase grow recode i).model := by
  simp [map]

theorem map_eq_of_incoming {i j : OmegaOne} (h : i < j)
    (e : Map (S := S) (construction base hbase grow recode i).model
      (construction base hbase grow recode j).model)
    (he : (construction base hbase grow recode j).incoming i
      (construction base hbase grow recode i).code = some e) :
    map base hbase grow recode h.le = e := by
  rw [map, dite_eq_right (ne_of_lt h)]
  exact Option.some.inj ((strictMap_spec base hbase grow recode i j h).1.symm.trans he)

theorem map_freezes {i j : OmegaOne} (h : i ≤ j) :
    (map base hbase grow recode h).FreezesSmallFibers := by
  by_cases he : i = j
  · subst j
    rw [map_self]
    exact WeakElementaryMap.id_freezes _
  · rw [map, dite_eq_right he]
    exact (strictMap_spec base hbase grow recode i j (lt_of_le_of_ne h he)).2

theorem map_composition {i j k : OmegaOne} (hij : i ≤ j) (hjk : j ≤ k)
    (x : (construction base hbase grow recode i).model.Domain) :
    map base hbase grow recode hjk (map base hbase grow recode hij x) =
      map base hbase grow recode (hij.trans hjk) x := by
  by_cases he : i = j
  · subst j
    rw [map_self]
    rfl
  by_cases he' : j = k
  · subst k
    rw [map_self]
    rfl
  have hij' := lt_of_le_of_ne hij he
  have hjk' := lt_of_le_of_ne hjk he'
  have hik' := hij'.trans hjk'
  simp only [map, dite_eq_right he, dite_eq_right he', dite_eq_right (ne_of_lt hik')]
  exact (construction_fits base hbase grow recode k).composition i j hij' hjk'
    (strictMap base hbase grow recode i j hij') (strictMap base hbase grow recode j k hjk')
    (strictMap base hbase grow recode i k hik')
    (strictMap_spec base hbase grow recode i j hij').1
    (strictMap_spec base hbase grow recode j k hjk').1
    (strictMap_spec base hbase grow recode i k hik').1 x

noncomputable def chain : WeakDirectedChain.{u,0,v} OmegaOne (SequenceClosure.carrier S) :=
  WeakDirectedChain.ofOmegaOne (fun i ↦ (construction base hbase grow recode i).model)
    (map base hbase grow recode) (fun i h x ↦ by rw [map_self]; rfl)
    (map_composition base hbase grow recode)

theorem chain_adequate (i : OmegaOne) : ((chain base hbase grow recode).model i).Adequate S :=
  (construction base hbase grow recode i).adequate

theorem chain_initial : (chain base hbase grow recode).model omegaOneZero = realize base := by
  change realize (construction base hbase grow recode omegaOneZero).code = realize base
  rw [(construction_fits base hbase grow recode omegaOneZero).initial not_lt_omegaOneZero]

theorem chain_freezes (i j : OmegaOne) (h : i ≤ j) :
    ((chain base hbase grow recode).map h).FreezesSmallFibers := map_freezes base hbase grow recode h

theorem chain_successor_grows (i : OmegaOne) :
    Grows ((chain base hbase grow recode).map (le_omegaOneSucc i)) := by
  have hf := construction_fits base hbase grow recode (omegaOneSucc i)
  have hs := strictMap_spec base hbase grow recode i (omegaOneSucc i) (lt_omegaOneSucc i)
  have he := map_eq_of_incoming base hbase grow recode (lt_omegaOneSucc i) _ hs.1
  change Grows (map base hbase grow recode (le_omegaOneSucc i))
  rw [he]
  intro n φ hφ b hb
  exact hf.grows i (lt_omegaOneSucc i) rfl _ hs.1 φ hφ b hb

theorem chain_growth : (chain base hbase grow recode).LargeFiberSuccessorGrowth := by
  let C := chain base hbase grow recode
  intro n φ hφ i b hb j hij
  have hbj : (C.model j).Q {x | Formula.WeakEval (C.model j).Q φ (x :> C.map hij ∘ b)} :=
    ((C.map hij).elementary (.q φ) (FragmentClosure.q_closed hφ) b).mpr hb
  obtain ⟨a, hfresh, ha⟩ := chain_successor_grows base hbase grow recode j φ hφ (C.map hij ∘ b) hbj
  refine ⟨a, ?_, hfresh⟩
  have he : C.map (le_omegaOneSucc j) ∘ (C.map hij ∘ b) = C.map (hij.trans (le_omegaOneSucc j)) ∘ b := by
    funext k
    exact C.composition hij (le_omegaOneSucc j) (b k)
  exact he ▸ ha

theorem chain_successor_freezes : (chain base hbase grow recode).FreezesSmallFibersAtSuccessors := by
  let C := chain base hbase grow recode
  intro n φ hφ i b hs x hx
  have he := chain_freezes base hbase grow recode i (omegaOneSucc i) (le_omegaOneSucc i) φ hφ b hs
  have hm : x ∈ C.map (le_omegaOneSucc i) '' {y | Formula.WeakEval (C.model i).Q φ (y :> b)} := he ▸ hx
  obtain ⟨y, _, hy⟩ := hm
  exact ⟨y, hy⟩

theorem chain_continuous : (chain base hbase grow recode).ContinuousAtLimits := by
  intro j hj x
  obtain ⟨i, hi, e, he, y, hy⟩ := (construction_fits base hbase grow recode j).continuous hj x
  refine ⟨i, hi, y, ?_⟩
  change map base hbase grow recode hi.le y = x
  rw [map_eq_of_incoming base hbase grow recode hi e he]
  exact hy

end AdequateOmegaOneNode
end ZFVP.Infinitary

