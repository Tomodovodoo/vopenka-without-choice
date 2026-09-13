import ZFVP.ModelTheory.InfinitaryOmegaOneStandardTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakDirectedChain
open FragmentClosure

theorem omegaOneSucc_le_iff (i j : OmegaOne) : omegaOneSucc i ≤ j ↔ i < j := by
  constructor
  · exact fun h ↦ (lt_omegaOneSucc i).trans_le h
  · intro h
    apply le_of_not_gt
    intro hj
    exact (not_le.mpr h) ((lt_omegaOneSucc_iff i j).mp hj)

/-- A nonzero limit index has earlier indices but has no greatest earlier index. -/
def NonzeroLimitIndex (j : OmegaOne) : Prop :=
  (∃ i, i < j) ∧ ∀ i, i < j → ∃ k, i < k ∧ k < j

variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}
  (C : WeakDirectedChain.{u,0,v} OmegaOne S)

/-- At a successor, a small fiber has no points outside the preceding stage. -/
def FreezesSmallFibersAtSuccessors : Prop :=
  ∀ {n} (φ : Formula L (n + 1)), ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S →
    ∀ i (b : Fin n → (C.model i).Domain), ¬Formula.WeakEval (C.model i).Q (.q φ) b →
      ∀ x : (C.model (omegaOneSucc i)).Domain,
        Formula.WeakEval (C.model (omegaOneSucc i)).Q φ
          (x :> C.map (le_omegaOneSucc i) ∘ b) →
        ∃ y : (C.model i).Domain, C.map (le_omegaOneSucc i) y = x

/-- Continuity is stated only as coverage by the actual earlier-stage maps. -/
def ContinuousAtLimits : Prop :=
  ∀ j, NonzeroLimitIndex j → ∀ x : (C.model j).Domain,
    ∃ i, ∃ hij : i < j, ∃ y : (C.model i).Domain, C.map hij.le y = x

theorem stage_fiber_pullback {n} {φ : Formula L (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier S) {i k j}
    (hik : i ≤ k) (hkj : k ≤ j) (b : Fin n → (C.model i).Domain)
    (y : (C.model k).Domain) (x : (C.model j).Domain) (he : C.map hkj y = x)
    (hx : Formula.WeakEval (C.model j).Q φ (x :> C.map (hik.trans hkj) ∘ b)) :
    Formula.WeakEval (C.model k).Q φ (y :> C.map hik ∘ b) := by
  apply (C.map hkj).elementary φ hφ (y :> C.map hik ∘ b) |>.mp
  have hb : C.map hkj ∘ (y :> C.map hik ∘ b) = x :> C.map (hik.trans hkj) ∘ b := by
    rw [C.map_cons, he]
    congr 1
    funext t
    exact C.composition hik hkj (b t)
  rwa [hb]

/-- Successor freezing and continuity imply freezing above every original
parameter stage. No global preservation hypothesis is used in the induction. -/
theorem preservesSmallFibers_of_successors_and_continuity
    (hstep : C.FreezesSmallFibersAtSuccessors) (hcont : C.ContinuousAtLimits) :
    C.PreservesSmallFibers := by
  intro n φ hφ i b hsmall
  have main : ∀ j (hij : i ≤ j) (x : (C.model j).Domain),
      Formula.WeakEval (C.model j).Q φ (x :> C.map hij ∘ b) →
        ∃ y : (C.model i).Domain, C.map hij y = x := by
    intro j
    induction j using (IsWellFounded.wf (α := OmegaOne) (r := (· < ·))).induction with
    | h j ih =>
      intro hij x hx
      by_cases he : i = j
      · subst j
        exact ⟨x, C.identity i hij x⟩
      have hij' : i < j := lt_of_le_of_ne hij he
      by_cases hsucc : ∃ p, omegaOneSucc p = j
      · obtain ⟨p, rfl⟩ := hsucc
        have hip : i ≤ p := (lt_omegaOneSucc_iff p i).mp hij'
        have hsmallp : ¬Formula.WeakEval (C.model p).Q (.q φ) (C.map hip ∘ b) :=
          fun hp ↦ hsmall ((C.map hip).elementary (.q φ) (q_closed hφ) b |>.mp hp)
        have hxs : Formula.WeakEval (C.model (omegaOneSucc p)).Q φ
            (x :> C.map (le_omegaOneSucc p) ∘ (C.map hip ∘ b)) := by
          simpa only [Function.comp_def, C.composition] using hx
        obtain ⟨y, hy⟩ := hstep φ hφ p (C.map hip ∘ b) hsmallp x hxs
        have hyp := C.stage_fiber_pullback hφ hip (le_omegaOneSucc p) b y x hy hx
        obtain ⟨z, hz⟩ := ih p (lt_omegaOneSucc p) hip y hyp
        refine ⟨z, ?_⟩
        calc
          C.map hij z = C.map (le_omegaOneSucc p) (C.map hip z) :=
            (C.composition hip (le_omegaOneSucc p) z).symm
          _ = x := by rw [hz, hy]
      · have hlim : NonzeroLimitIndex j := by
          refine ⟨⟨i, hij'⟩, ?_⟩
          intro k hk
          refine ⟨omegaOneSucc k, lt_omegaOneSucc k, ?_⟩
          exact lt_of_le_of_ne ((omegaOneSucc_le_iff k j).mpr hk) (fun h ↦ hsucc ⟨k, h⟩)
        obtain ⟨k, hkj, y, hy⟩ := hcont j hlim x
        by_cases hik : i ≤ k
        · have hyk := C.stage_fiber_pullback hφ hik hkj.le b y x hy hx
          obtain ⟨z, hz⟩ := ih k hkj hik y hyk
          refine ⟨z, ?_⟩
          calc
            C.map hij z = C.map hkj.le (C.map hik z) := (C.composition hik hkj.le z).symm
            _ = x := by rw [hz, hy]
        · have hki : k ≤ i := (lt_of_not_ge hik).le
          refine ⟨C.map hki y, ?_⟩
          exact (C.composition hki hij y).trans hy
  exact main

theorem standardEval_fromStage_of_successors_and_continuity
    (hgrowth : C.LargeFiberSuccessorGrowth) (hstep : C.FreezesSmallFibersAtSuccessors)
    (hcont : C.ContinuousAtLimits) {n i} (φ : Formula L n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (b : Fin n → (C.model i).Domain) :
    Formula.Eval φ (C.fromStage i ∘ b) ↔ Formula.WeakEval (C.model i).Q φ b :=
  C.standardEval_fromStage hgrowth
    (C.preservesSmallFibers_of_successors_and_continuity hstep hcont) φ hφ b

end WeakDirectedChain
end ZFVP.Infinitary
