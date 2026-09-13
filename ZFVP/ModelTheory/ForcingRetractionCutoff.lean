import ZFVP.SetTheory.EquivalentRetractionForcing
import ZFVP.SetTheory.WoodinPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.prefix_cutoff_iff {P R N T m one : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (ho : one ∈ N) (κ δ : V) :
    IsWoodinPrefixCutoff P R one κ δ ↔ IsWoodinPrefixCutoff N T one κ δ := by
  have htup : (fun i : Fin 2 ↦ checkName one (![κ, δ] i)) = ![checkName one κ, checkName one δ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  have hh {p : V} (hp : p ∈ P) :=
    hr.forcingFormula_check_iff hR hT he ho woodinLocalRestorationFormula ![κ, δ] hp
  simp only [htup] at hh
  unfold IsWoodinPrefixCutoff
  apply and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h n hn
    have hq := (hh (hr.inclusion n hn)).mp (h n (hr.inclusion n hn))
    rwa [hr.fixes n hn] at hq
  · intro h p hp
    exact (hh hp).mpr (h _ (function_value_mem hr.maps hp))

theorem IsForcingRetraction.prefix_cutoff {P R N T m one : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (ho : one ∈ N) (κ : V) :
    woodinPrefixCutoff P R one κ = woodinPrefixCutoff N T one κ := by
  have hh : IsWoodinPrefixCutoff P R one = IsWoodinPrefixCutoff N T one := by
    funext a b
    exact propext (hr.prefix_cutoff_iff hR hT he ho a b)
  unfold woodinPrefixCutoff
  congr 1

end ZFVP
