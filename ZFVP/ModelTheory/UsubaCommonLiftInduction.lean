import ZFVP.ModelTheory.UsubaCommonLiftLimit
import ZFVP.ModelTheory.UsubaCommonLiftSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaCommonLiftBoundAt_all [Countable V] {θ η i p c d : V}
    [IsOrdinal θ] [IsOrdinal η]
    (hηθ : η ⊆ θ) (hi : i ∈ η)
    (f : ForcingName ((T).P i)) (hc : c ∈ (T).P θ) (hd : d ∈ (T).P i)
    (hdc : ⟨d, ((T).projection i θ) ‘ c⟩ₖ ∈ (T).R i)
    (hmem : ∀ k ∈ succ η, usubaQuotientBoundRec θ i p f.val k ∈ (T).P k)
    (hnorm : ∀ k ∈ succ η, IsUsubaBoundNormalizationAt θ i p f.val k)
    (hselected : IsUsubaSelectedDecision θ i f.val c d) :
    ∀ k ∈ succ η, IsUsubaCommonLiftBoundAt θ i p f.val c d k := by
  let := IsOrdinal.of_mem hi
  have hiθ : i ⊆ θ := subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hηθ
  have hall := transfinite_induction
    (fun k : V ↦ k ∈ succ η → IsUsubaCommonLiftBoundAt θ i p f.val c d k) (by definability) ?_
  · intro k hk
    let := IsOrdinal.of_mem hk
    exact hall (IsOrdinal.toOrdinal k) hk
  intro k ih hk
  have hkθ : (k : V) ⊆ θ := subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hk)) hηθ
  rcases IsOrdinal.mem_trichotomy (k : V) i with hki | he | hik
  · exact usubaCommonLiftBoundAt_before hki
  · subst i
    exact usubaCommonLiftBoundAt_base hiθ hc hd hdc
  have hprev : ∀ l ∈ (k : V), IsUsubaCommonLiftBoundAt θ i p f.val c d l := by
    intro l hl
    let := IsOrdinal.of_mem hl
    exact ih (IsOrdinal.toOrdinal l) hl (IsOrdinal.toIsTransitive.mem_trans hl hk)
  by_cases hsucc : (k : V) = succ (⋃ˢ (k : V))
  · have hkm : ⋃ˢ (k : V) ∈ (k : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (k : V)) ∈ x) hsucc).mpr (mem_succ_self _)
    let := IsOrdinal.of_mem hkm
    have hh := usubaCommonLiftBoundAt_successor (hsucc ▸ hkθ) (hsucc ▸ hik) f hc hd hdc
      (hsucc ▸ hmem k hk) (hsucc ▸ hnorm k hk) hselected (hprev _ hkm)
    rwa [← hsucc] at hh
  · exact usubaCommonLiftBoundAt_limit hkθ hik hsucc hc hd hdc (hmem k hk) hprev

end ZFVP
