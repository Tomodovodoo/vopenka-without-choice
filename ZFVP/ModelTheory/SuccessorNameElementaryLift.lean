import ZFVP.ModelTheory.SuccessorLowNameForcing
import ZFVP.ModelTheory.ClassForcingQuotientTruth
import ZFVP.ModelTheory.ElementaryMapFromRepresentatives

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

abbrev SuccessorNameModel (A : ForcingContext V) (η : V) :=
  ClassForcingQuotient A.P A.R A.G A.order A.generic.1
    (fun τ ↦ τ ∈ successorLowNameSet A.P η) (fun _ h ↦ successorLowNameSet_isName h)

def successorNameValue (A : ForcingContext V) (η : V)
    (τ : {x : V // x ∈ successorLowNameSet A.P η}) : A.SuccessorNameModel η :=
  ClassForcingQuotient.ofName A.P A.R A.G A.order A.generic.1
    (fun x ↦ x ∈ successorLowNameSet A.P η) (fun _ h ↦ successorLowNameSet_isName h) τ

theorem successorNameValue_surjective (A : ForcingContext V) (η : V) :
    Function.Surjective (A.successorNameValue η) := ClassForcingQuotient.ofName_surjective _ _ _ _ _ _ _

instance successorNameModel_nonempty (A : ForcingContext V) (η : V) : Nonempty (A.SuccessorNameModel η) :=
  ⟨A.successorNameValue η ⟨∅, mem_successorLowNameSet.mpr (by simp)⟩⟩

theorem successorNameValue_formula_truth (A : ForcingContext V) (η : V)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → {x : V // x ∈ successorLowNameSet A.P η}) :
    φ.Evalb (A.successorNameValue η ∘ v) ↔
      GenericMeets A.G (classForcingFormula A.P A.R (fun x ↦ x ∈ successorLowNameSet A.P η)
        (by definability) φ (standardTuple (fun i ↦ (v i).val))) :=
  ClassForcingQuotient.formula_truth _ _ _ _ A.generic _ (by definability) _ φ v

end ForcingContext

theorem finiteRankEmbedding_successorNameLift {η ζ f : V} [IsOrdinal η] [IsOrdinal ζ]
    (A B : ForcingContext V)
    (hη : ∀ β ∈ η, succ β ∈ η) (hζ : ∀ β ∈ ζ, succ β ∈ ζ)
    (hP : A.P ⊆ hierarchy η) (hQ : B.P ⊆ hierarchy ζ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V)))
      (hierarchy (ordinalAdd ζ (ω : V))) f)
    (hfP : f ‘ A.P = B.P) (hfR : f ‘ A.R = B.R) (hfη : f ‘ η = ζ)
    (hG : ∀ p ∈ A.G, f ‘ p ∈ B.G) :
    ∃ j : ElementaryMap (A.SuccessorNameModel η) (B.SuccessorNameModel ζ),
      ∀ τ : {x : V // x ∈ successorLowNameSet A.P η}, ∃ τ' : ForcingName B.P,
        τ'.val = f ‘ τ.val ∧ (j (A.successorNameValue η τ)).val = B.ofName τ' := by
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  let := hierarchy_transitive (ordinalAdd ζ (ω : V))
  have hD := successorLowNameSet_mem_finite_rank hη hP
  have hfD := finiteRankEmbedding_value_successorLowNameSet hη hζ hP hQ he hfP hfη
  have himg (τ : {x : V // x ∈ successorLowNameSet A.P η}) :
      f ‘ τ.val ∈ successorLowNameSet B.P ζ := by
    rw [← hfD]
    exact (he.value_mem_iff ((hierarchy_transitive _).mem_trans τ.property hD) hD).mpr τ.property
  let m : {x : V // x ∈ successorLowNameSet A.P η} → {x : V // x ∈ successorLowNameSet B.P ζ} :=
    fun τ ↦ ⟨f ‘ τ.val, himg τ⟩
  have hforward : ∀ {n : ℕ} (φ : SetTheorySemisentence n)
      (v : Fin n → {x : V // x ∈ successorLowNameSet A.P η}),
      φ.Evalb (A.successorNameValue η ∘ v) → φ.Evalb (B.successorNameValue ζ ∘ (m ∘ v)) := by
    intro n φ v h
    obtain ⟨p, hpG, hpφ⟩ := (A.successorNameValue_formula_truth η φ v).mp h
    apply (B.successorNameValue_formula_truth ζ φ (m ∘ v)).mpr
    exact ⟨f ‘ p, hG p hpG,
      (finiteRankEmbedding_successorNameForcing_iff hη hζ hP hQ A.order.1 he hfP hfR hfη
        (A.generic.1.1 p hpG) φ (fun i ↦ (v i).val) (fun i ↦ (v i).property)).mp hpφ⟩
  have hiff : ∀ {n : ℕ} (φ : SetTheorySemisentence n)
      (v : Fin n → {x : V // x ∈ successorLowNameSet A.P η}),
      φ.Evalb (A.successorNameValue η ∘ v) ↔ φ.Evalb (B.successorNameValue ζ ∘ (m ∘ v)) := by
    intro n φ v
    constructor
    · exact hforward φ v
    · intro ht
      by_contra hs
      have hn := hforward (∼φ) v (by simpa using hs)
      exact (show ¬φ.Evalb (B.successorNameValue ζ ∘ (m ∘ v)) from by simpa using hn) ht
  obtain ⟨j, hj⟩ := elementaryMap_from_representatives (A.successorNameValue η)
    (B.successorNameValue ζ ∘ m) (A.successorNameValue_surjective η) hiff
  refine ⟨j, fun τ ↦ ⟨⟨f ‘ τ.val, successorLowNameSet_isName (himg τ)⟩, rfl, ?_⟩⟩
  exact congrArg Subtype.val (hj τ)

end ZFVP
