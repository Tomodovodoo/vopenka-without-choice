import ZFVP.ModelTheory.InfinitaryCountablyDirectedWeakLimit
import ZFVP.ModelTheory.OmegaOneChainColimit

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakDirectedChain
variable {L : Language.{u}} [L.Eq] [L.Encodable] {S : Set (TaggedFormula L)}

/-- The regularity of omega-one supplies the required countable upper bounds. -/
def ofOmegaOne (model : OmegaOne → WeakModel.{u,v} L)
    (map : ∀ {i j}, i ≤ j →
      WeakElementaryMap (FragmentClosure.carrier S) (model i) (model j))
    (identity : ∀ i (h : i ≤ i) x, map h x = x)
    (composition : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) x,
      map hjk (map hij x) = map (hij.trans hjk) x) :
    WeakDirectedChain.{u,0,v} OmegaOne S where
  bounded := fun f ↦ exists_upper_bound_of_countable f
  model := model
  map := map
  identity := identity
  composition := composition

/-- An omega-one chain has a constructed weak limit with coherent elementary
embeddings covering its domain. Q is still the constructed weak quantifier. -/
theorem exists_omegaOne_weak_limit (model : OmegaOne → WeakModel.{u,v} L)
    (map : ∀ {i j}, i ≤ j →
      WeakElementaryMap (FragmentClosure.carrier S) (model i) (model j))
    (identity : ∀ i (h : i ≤ i) x, map h x = x)
    (composition : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) x,
      map hjk (map hij x) = map (hij.trans hjk) x) :
    ∃ N : WeakLimitStructure.{u,v} L,
      ∃ e : ∀ i, WeakLimitEmbedding (FragmentClosure.carrier S) (model i) N,
        (∀ i j (h : i ≤ j) x, e j (map h x) = e i x) ∧
        ∀ x : N.Domain, ∃ i, ∃ a : (model i).Domain, e i a = x :=
  (ofOmegaOne model map identity composition).exists_weak_limit

end WeakDirectedChain
end ZFVP.Infinitary
