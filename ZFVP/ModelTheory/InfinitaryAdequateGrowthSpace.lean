import ZFVP.ModelTheory.InfinitaryAdequateUniformSuccessor
import ZFVP.ModelTheory.InfinitaryDenseRequirementChain

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]

/-- A countable adequate extension together with its map from a fixed base. -/
structure AdequateExtension (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L)) where
  model : WeakModel.{u,v} L
  embedding : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) M model
  adequate : model.Adequate S
  freezes : embedding.FreezesSmallFibers

namespace AdequateExtension
variable {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

def initial (hM : M.Adequate S) : AdequateExtension M S :=
  ⟨M, WeakElementaryMap.id M, hM, WeakElementaryMap.id_freezes M⟩

def Refines (E F : AdequateExtension M S) : Prop :=
  ∃ e : WeakElementaryMap (FragmentClosure.carrier (SequenceClosure.carrier S)) E.model F.model,
    e.FreezesSmallFibers ∧ ∀ x, e (E.embedding x) = F.embedding x

theorem refines_refl (E : AdequateExtension M S) : Refines E E :=
  ⟨WeakElementaryMap.id _, WeakElementaryMap.id_freezes _, fun _ ↦ rfl⟩

theorem refines_trans {E F G : AdequateExtension M S}
    (hEF : Refines E F) (hFG : Refines F G) : Refines E G := by
  obtain ⟨e, he, hc⟩ := hEF
  obtain ⟨f, hf, hd⟩ := hFG
  exact ⟨f.comp e, e.comp_freezes f he hf, fun x ↦ (congrArg f (hc x)).trans (hd x)⟩

def Requirement (M : WeakModel.{u,v} L) (S : Set (TaggedFormula L)) :=
  Σ n : ℕ, {φ : Formula L (n + 1) //
    ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)} × (Fin n → M.Domain)

theorem requirement_countable (hS : S.Countable) : Countable (Requirement M S) := by
  have hT := FragmentClosure.carrier_countable (SequenceClosure.carrier_countable hS)
  have : Countable (FragmentClosure.carrier (SequenceClosure.carrier S)) := hT.to_subtype
  have (n : ℕ) : Countable {φ : Formula L (n + 1) //
      ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S)} :=
    Function.Injective.countable (f := fun φ ↦ (⟨⟨n + 1, φ.1⟩, φ.2⟩ :
      FragmentClosure.carrier (SequenceClosure.carrier S))) (by
        intro a b h
        apply Subtype.ext
        simpa using congrArg Subtype.val h)
  unfold Requirement
  infer_instance

def Meets (r : Requirement M S) (E : AdequateExtension M S) : Prop :=
  M.Q {x | Formula.WeakEval M.Q r.2.1.1 (x :> r.2.2)} →
    ∃ a : E.model.Domain, a ∉ Set.range E.embedding ∧
      Formula.WeakEval E.model.Q r.2.1.1 (a :> E.embedding ∘ r.2.2)

theorem meets_persistent (r : Requirement M S) {E F : AdequateExtension M S}
    (hEF : Refines E F) (hE : Meets r E) : Meets r F := by
  obtain ⟨e, he, hc⟩ := hEF
  intro hq
  obtain ⟨a, ha, ht⟩ := hE hq
  refine ⟨e a, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact ha ⟨x, e.injective ((hc x).trans hx)⟩
  · have h := (e.elementary r.2.1.1 r.2.1.2 (a :> E.embedding ∘ r.2.2)).mpr ht
    have hb : e ∘ (a :> E.embedding ∘ r.2.2) = e a :> F.embedding ∘ r.2.2 := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact hc (r.2.2 i)
    exact hb ▸ h

theorem meets_dense (hS : S.Countable) (r : Requirement M S) (E : AdequateExtension M S) :
    ∃ F, Refines E F ∧ Meets r F := by
  classical
  by_cases hq : M.Q {x | Formula.WeakEval M.Q r.2.1.1 (x :> r.2.2)}
  · have hqE : E.model.Q {x | Formula.WeakEval E.model.Q r.2.1.1
        (x :> E.embedding ∘ r.2.2)} :=
      (E.embedding.elementary (.q r.2.1.1) (FragmentClosure.q_closed r.2.1.2) r.2.2).mpr hq
    obtain ⟨N, e, hN, he, a, ha, ht⟩ := exists_adequate_successor E.adequate hS
      r.2.1.1 r.2.1.2 (E.embedding ∘ r.2.2) hqE
    let F : AdequateExtension M S :=
      ⟨N, e.comp E.embedding, hN, E.embedding.comp_freezes e E.freezes he⟩
    refine ⟨F, ⟨e, he, fun _ ↦ rfl⟩, fun _ ↦ ⟨a, ?_, ht⟩⟩
    rintro ⟨x, hx⟩
    exact ha ⟨E.embedding x, hx⟩
  · exact ⟨E, refines_refl E, fun h ↦ (hq h).elim⟩

theorem exists_growth_chain (hM : M.Adequate S) (hS : S.Countable) :
    Nonempty (DenseRequirementChain Refines Meets (initial hM)) := by
  have := requirement_countable (M := M) hS
  exact exists_denseRequirementChain Refines Meets refines_refl
    (fun h₁ h₂ ↦ refines_trans h₁ h₂) meets_persistent (meets_dense hS) (initial hM)

end AdequateExtension
end WeakModel
end ZFVP.Infinitary
