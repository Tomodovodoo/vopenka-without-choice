import ZFVP.ModelTheory.InfinitaryWeakModelRelabel
import ZFVP.ModelTheory.InfinitaryAdequateGrowthBlock

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v

/-- Countable models encoded on subsets of one fixed set. Unlike WeakModel,
this record does not quantify over domain types. -/
structure CountableWeakModelCode (L : Language.{u}) [L.Eq] where
  carrier : Set ℕ
  str : Structure L carrier
  eq : @Structure.Eq L carrier str _
  nonempty : Nonempty carrier
  Q : Set carrier → Prop
  mono : Monotone Q

namespace CountableWeakModelCode
variable {L : Language.{u}} [L.Eq]

def asWeakModel (C : CountableWeakModelCode L) : WeakModel.{u,0} L where
  Domain := C.carrier
  str := C.str
  eq := C.eq
  nonempty := C.nonempty
  countable := inferInstance
  Q := C.Q
  mono := C.mono

/-- Every countable weak model has an actual bijective recoding on a subset of
the naturals, preserving every requested fragment and its small fibers. -/
theorem exists_code (M : WeakModel.{u,v} L) (T : Set (TaggedFormula L)) :
    ∃ C : CountableWeakModelCode L, ∃ e : WeakElementaryMap T M C.asWeakModel,
      Function.Bijective e ∧ e.FreezesSmallFibers := by
  classical
  let : Encodable M.Domain := Encodable.ofCountable M.Domain
  let f : M.Domain → ℕ := Encodable.encode
  let e : M.Domain ≃ Set.range f := Equiv.ofInjective f Encodable.encode_injective
  let N := M.relabel e
  let C : CountableWeakModelCode L := ⟨Set.range f, N.str, N.eq, N.nonempty, N.Q, N.mono⟩
  exact ⟨C, M.relabelEmbedding e T, e.bijective, M.relabelEmbedding_freezes e T⟩

theorem exists_adequate_code [L.Encodable] {S : Set (TaggedFormula L)}
    (M : WeakModel.{u,v} L) (hM : M.Adequate S) :
    ∃ C : CountableWeakModelCode L,
      ∃ e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M C.asWeakModel,
        C.asWeakModel.Adequate S ∧ Function.Bijective e ∧ e.FreezesSmallFibers := by
  obtain ⟨C, e, he, hf⟩ := exists_code M _
  exact ⟨C, e, hM.of_elementary e, he, hf⟩

/-- The growth-block choice can be made entirely within the fixed type of
natural-carrier codes. -/
theorem exists_adequate_growth_block [L.Encodable] {S : Set (TaggedFormula L)}
    (C : CountableWeakModelCode L) (hC : C.asWeakModel.Adequate S) (hS : S.Countable) :
    ∃ D : CountableWeakModelCode L,
      ∃ e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) C.asWeakModel D.asWeakModel,
        D.asWeakModel.Adequate S ∧ e.FreezesSmallFibers ∧
          ∀ {n} (φ : Formula L (n + 1)),
            ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) →
              ∀ b : Fin n → C.asWeakModel.Domain,
                C.asWeakModel.Q {x | Formula.WeakEval C.asWeakModel.Q φ (x :> b)} →
                  ∃ a : D.asWeakModel.Domain, a ∉ Set.range e ∧
                    Formula.WeakEval D.asWeakModel.Q φ (a :> e ∘ b) := by
  obtain ⟨N, e, hN, he, hg⟩ := WeakModel.exists_adequate_growth_block hC hS
  obtain ⟨D, f, hD, hfbij, hf⟩ := exists_adequate_code N hN
  refine ⟨D, f.comp e, hD, e.comp_freezes f he hf, ?_⟩
  intro n φ hφ b hq
  obtain ⟨a, ha, ht⟩ := hg φ hφ b hq
  refine ⟨f a, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact ha ⟨x, f.injective hx⟩
  · have h := (f.elementary φ hφ (a :> e ∘ b)).mpr ht
    have hb : f ∘ (a :> e ∘ b) = f a :> (f.comp e) ∘ b := by
      funext i
      cases i using Fin.cases <;> rfl
    exact hb ▸ h

end CountableWeakModelCode
end ZFVP.Infinitary
