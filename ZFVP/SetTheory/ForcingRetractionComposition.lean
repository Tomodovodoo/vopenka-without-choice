import ZFVP.SetTheory.ForcingRetraction
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.comp {P R N T K L m n : V}
    (hm : IsForcingRetraction N T P R m) (hn : IsForcingRetraction K L N T n) :
    IsForcingRetraction K L P R (compose m n) := by
  have hv (p : V) (hp : p ∈ P) := value_compose_of_mem_function hm.maps hn.maps hp
  refine ⟨compose_function hm.maps hn.maps, fun p hp ↦ hm.inclusion p (hn.inclusion p hp), ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hv p (hm.inclusion p (hn.inclusion p hp)), hm.fixes p (hn.inclusion p hp), hn.fixes p hp]
  · intro p hp q hq hpq
    rw [hv p hp, hv q hq]
    exact hn.monotone _ (function_value_mem hm.maps hp) _ (function_value_mem hm.maps hq)
      (hm.monotone p hp q hq hpq)
  · intro p hp q hq
    rw [hv p hp]
    exact (hm.below p hp q (hn.inclusion q hq)).trans (hn.below _ (function_value_mem hm.maps hp) q hq)
  · intro p hp q hq hqp
    rw [hv p hp] at hqp
    obtain ⟨a, ha, hap, haq⟩ := hn.lift _ (function_value_mem hm.maps hp) q hq hqp
    obtain ⟨b, hb, hbp, hba⟩ := hm.lift p hp a ha hap
    exact ⟨b, hb, hbp, by rw [hv b hb, hba, haq]⟩

theorem IsForcingRetraction.top_of_mem {P R N T m one : V}
    (hr : IsForcingRetraction N T P R m) (ht : IsForcingTop P R one) (hone : one ∈ N) :
    IsForcingTop N T one := by
  refine ⟨hone, ?_⟩
  intro p hp
  have hh := (hr.below p (hr.inclusion p hp) one hone).mp (ht.2 p (hr.inclusion p hp))
  rwa [hr.fixes p hp] at hh

theorem IsForcingRetraction.comp_below {P R N T K L m n : V}
    (hm : IsForcingRetraction N T P R m) (hn : IsForcingRetraction K L N T n)
    (hR : IsForcingPreorder P R)
    (hmb : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R) (hnb : ∀ p ∈ N, ⟨n ‘ p, p⟩ₖ ∈ T) :
    ∀ p ∈ P, ⟨(compose m n) ‘ p, p⟩ₖ ∈ R := by
  intro p hp
  have hmp := function_value_mem hm.maps hp
  have hnp := hn.inclusion _ (function_value_mem hn.maps hmp)
  have hnm : ⟨n ‘ (m ‘ p), m ‘ p⟩ₖ ∈ R :=
    (hm.below _ (hm.inclusion _ hnp) _ hmp).mpr (by rw [hm.fixes _ hnp]; exact hnb _ hmp)
  rw [value_compose_of_mem_function hm.maps hn.maps hp]
  exact hR.2.2 _ (hm.inclusion _ hnp) _ (hm.inclusion _ hmp) p hp hnm (hmb p hp)

end ZFVP
