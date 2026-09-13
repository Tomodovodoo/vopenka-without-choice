import ZFVP.ModelTheory.RankForcingMeaning
import ZFVP.ModelTheory.SuccessorRankForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_rankForcing_iff {δ ε e P R p : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (he : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (hp : p ∈ hierarchy δ)
    (hord : IsForcingPreorder P R) (hord' : IsForcingPreorder (e ‘ P) (e ‘ R))
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V)
    (hv : ∀ i, v i ∈ hierarchy δ) (hn : ∀ i, IsForcingName P (v i)) :
    p ∈ classForcingFormula P R (IsLowRankForcingName P δ) (by definability) φ (standardTuple v) ↔
      e ‘ p ∈ classForcingFormula (e ‘ P) (e ‘ R) (IsLowRankForcingName (e ‘ P) ε)
        (by definability) φ (standardTuple (fun i ↦ e ‘ (v i))) := by
  let := hδ.ordinal
  let := hε.ordinal
  let j := successorRankElementaryMap he
  let a : SetDomain (hierarchy δ) := ⟨P, hP⟩
  let b : SetDomain (hierarchy δ) := ⟨R, hR⟩
  let c : SetDomain (hierarchy δ) := ⟨p, hp⟩
  let w : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨v i, hv i⟩
  have ht := j.elementary (rankForcingTranslation φ) (a :> b :> a :> a :> c :> w) Empty.elim
  have hz : j ∘ (Empty.elim : Empty → SetDomain (hierarchy δ)) = Empty.elim := by
    funext i
    exact Empty.elim i
  rw [hz] at ht
  have hw : j ∘ (a :> b :> a :> a :> c :> w) =
      (j a :> j b :> j a :> j a :> j c :> (j ∘ w)) := by
    funext i
    exact Fin.cases rfl (fun k ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl
      (fun m ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun _ ↦ rfl) t) m) l) k) i
  rw [hw] at ht
  exact (rankForcingTranslation_meaning hδ a b a a hord φ w hn c).symm.trans
    (ht.trans (rankForcingTranslation_meaning hε (j a) (j b) (j a) (j a) hord' φ (j ∘ w)
      (fun i ↦ (successorRankEmbedding_forcingName_iff hδ hε he hP (hv i)).mp (hn i)) (j c)))

end ZFVP
