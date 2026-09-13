import ZFVP.ModelTheory.InfinitaryAdequateOmegaOneHistory

namespace ZFVP.Infinitary
open LO LO.FirstOrder
open WeakDirectedChain
universe u v w
namespace AdequateOmegaOneNode
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  {Code : Type w} {realize : Code → WeakModel.{u,v} L}

noncomputable def withIncoming {j : OmegaOne}
    (H : ∀ i, i < j → AdequateOmegaOneNode realize S)
    (c : Code) (ha : (realize c).Adequate S)
    (e : ∀ i (hi : i < j), Map (S := S) (H i hi).model (realize c)) : AdequateOmegaOneNode realize S := by
  classical
  exact ⟨c, ha, fun i P ↦ if hi : i < j then
    if hP : P = (H i hi).code then some (hP.symm ▸ e i hi) else none else none⟩

@[simp] theorem withIncoming_at {j : OmegaOne}
    (H : ∀ i, i < j → AdequateOmegaOneNode realize S)
    (c : Code) (ha : (realize c).Adequate S)
    (e : ∀ i (hi : i < j), Map (S := S) (H i hi).model (realize c)) (i : OmegaOne) (hi : i < j) :
    (withIncoming H c ha e).incoming i (H i hi).code = some (e i hi) := by
  simp [withIncoming, hi]

namespace History
variable {base : Code} {j : OmegaOne} (H : History (realize := realize) (S := S) base j)

theorem fits_withIncoming (c : Code) (ha : (realize c).Adequate S)
    (e : ∀ i : {i : OmegaOne // i < j}, Map (S := S) (H.node i i.property).model (realize c))
    (hf : ∀ i, (e i).FreezesSmallFibers)
    (hc : ∀ i k (h : i ≤ k) x, e k (H.map h x) = e i x)
    (hg : ∀ p (hp : p < j), omegaOneSucc p = j → Grows (e ⟨p, hp⟩))
    (hl : NonzeroLimitIndex j → ∀ x : (realize c).Domain, ∃ i, ∃ y, e i y = x)
    (hzero : (∀ i, ¬i < j) → c = base) :
    Fits base j H.node (withIncoming H.node c ha (fun i hi ↦ e ⟨i, hi⟩)) := by
  refine ⟨?_, ?_, ?_, ?_, hzero⟩
  · intro i hi
    exact ⟨e ⟨i, hi⟩, withIncoming_at _ _ _ _ i hi, hf ⟨i, hi⟩⟩
  · intro i k hik hkj eik ekj eij heik hekj heij x
    have hek : e ⟨k, hkj⟩ = ekj := Option.some.inj
      ((withIncoming_at H.node c ha _ k hkj).symm.trans hekj)
    have hei : e ⟨i, hik.trans hkj⟩ = eij := Option.some.inj
      ((withIncoming_at H.node c ha _ i (hik.trans hkj)).symm.trans heij)
    rw [← hek, ← hei, ← H.map_eq_of_incoming (i := ⟨i, hik.trans hkj⟩) (k := ⟨k, hkj⟩) hik eik heik]
    exact hc ⟨i, hik.trans hkj⟩ ⟨k, hkj⟩ hik.le x
  · intro p hp hsucc e' he'
    have he : e ⟨p, hp⟩ = e' := Option.some.inj
      ((withIncoming_at H.node c ha _ p hp).symm.trans he')
    rw [← he]
    intro n φ hφ b hb
    exact hg p hp hsucc φ hφ b hb
  · intro hlim x
    obtain ⟨i, y, hy⟩ := hl hlim x
    exact ⟨i, i.property, e i, withIncoming_at _ _ _ _ i i.property, y, hy⟩

end History

/-- Successor and countable-limit operations on one fixed code type suffice
for the next recursion node. The concrete code operations are supplied below. -/
theorem exists_fit
    (base : Code) (hbase : (realize base).Adequate S)
    (grow : ∀ c : Code, (realize c).Adequate S →
      ∃ d : Code, ∃ e : Map (S := S) (realize c) (realize d),
        (realize d).Adequate S ∧ e.FreezesSmallFibers ∧ Grows e)
    (recode : ∀ N : WeakModel.{u,v} L, N.Adequate S →
      ∃ c : Code, ∃ e : Map (S := S) N (realize c),
        (realize c).Adequate S ∧ e.FreezesSmallFibers ∧ Function.Surjective e)
    (j : OmegaOne) (H : History (realize := realize) (S := S) base j) :
    ∃ N : AdequateOmegaOneNode realize S, Fits base j H.node N := by
  classical
  by_cases hpred : ∃ i, i < j
  · by_cases hsucc : ∃ p, omegaOneSucc p = j
    · obtain ⟨p, rfl⟩ := hsucc
      let q : {i : OmegaOne // i < omegaOneSucc p} := ⟨p, lt_omegaOneSucc p⟩
      have hto (i : {i : OmegaOne // i < omegaOneSucc p}) : i ≤ q :=
        (lt_omegaOneSucc_iff p i).mp i.property
      obtain ⟨c, f, ha, hf, hg⟩ := grow (H.node p (lt_omegaOneSucc p)).code
        (H.node p (lt_omegaOneSucc p)).adequate
      let e := fun i : {i : OmegaOne // i < omegaOneSucc p} ↦ f.comp (H.map (hto i))
      refine ⟨withIncoming H.node c ha (fun i hi ↦ e ⟨i, hi⟩), H.fits_withIncoming c ha e ?_ ?_ ?_ ?_ ?_⟩
      · intro i
        exact WeakElementaryMap.comp_freezes (H.map (hto i)) f (H.map_freezes _) hf
      · intro i k hik x
        change f (H.map (hto k) (H.map hik x)) = f (H.map (hto i) x)
        rw [H.map_composition]
      · intro r hr her
        have he : r = p := omegaOneSucc_injective her
        subst r
        dsimp only [e]
        rw [H.map_self]
        intro n φ hφ b hb
        exact hg φ hφ b hb
      · intro hlim
        obtain ⟨k, hpk, hk⟩ := hlim.2 p (lt_omegaOneSucc p)
        exact False.elim ((not_lt_of_ge ((lt_omegaOneSucc_iff p k).mp hk)) hpk)
      · intro hz
        exact False.elim (hz p (lt_omegaOneSucc p))
    · let : Nonempty {i : OmegaOne // i < j} :=
        hpred.elim (fun i hi ↦ ⟨⟨i, hi⟩⟩)
      obtain ⟨N, e, ha, hf, hc, hcover⟩ := H.diagram.exists_adequate_limit
        (fun i ↦ (H.node i i.property).adequate) (fun _ _ h ↦ H.map_freezes h)
      obtain ⟨c, f, hac, hfc, hsurj⟩ := recode N ha
      let e' := fun i ↦ f.comp (e i)
      refine ⟨withIncoming H.node c hac (fun i hi ↦ e' ⟨i, hi⟩),
        H.fits_withIncoming c hac e' ?_ ?_ ?_ ?_ ?_⟩
      · intro i
        exact WeakElementaryMap.comp_freezes (e i) f (hf i) hfc
      · intro i k hik x
        change f (e k (H.map hik x)) = f (e i x)
        exact congrArg f (hc i k hik x)
      · intro p hp hsp
        exact False.elim (hsucc ⟨p, hsp⟩)
      · intro _ x
        obtain ⟨y, rfl⟩ := hsurj x
        obtain ⟨i, a, hea⟩ := hcover y
        exact ⟨i, a, congrArg f hea⟩
      · intro hz
        exact False.elim (hpred.elim (fun i hi ↦ hz i hi))
  · let N : AdequateOmegaOneNode realize S := ⟨base, hbase, fun _ _ ↦ none⟩
    refine ⟨N, ?_⟩
    have hn : ∀ i, ¬i < j := fun i hi ↦ hpred ⟨i, hi⟩
    refine ⟨?_, ?_, ?_, ?_, fun _ ↦ rfl⟩
    · intro i hi
      exact False.elim (hn i hi)
    · intro i k hik hkj
      exact False.elim (hn k hkj)
    · intro p hp
      exact False.elim (hn p hp)
    · intro hlim
      exact False.elim (hpred hlim.1)

end AdequateOmegaOneNode
end ZFVP.Infinitary

