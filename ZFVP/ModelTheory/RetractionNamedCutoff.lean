import ZFVP.ModelTheory.RetractionHartogsNames
import ZFVP.SetTheory.WoodinNamedPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFormula_retraction_congr_iff {P R N T m p : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName P) (w : Fin n → ForcingName N)
    (hp : p ∈ P) (heq : ∀ i, m ‘ p ∈ atomicEquality N T (nameAction m (v i).val) (w i).val) :
    p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val)) ↔
      m ‘ p ∈ forcingFormula N T φ (standardTuple (fun i ↦ (w i).val)) :=
  (hr.forcingFormula_nameAction_iff hR hT he φ _ (fun i ↦ (v i).property) hp).trans
    (classForcingFormula_congr hT (IsForcingName N) (by definability) φ _ _
      (function_value_mem hr.maps hp) heq)

theorem IsForcingRetraction.named_prefix_cutoff_iff {P R N T m one : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (τ : ForcingName P) (υ : ForcingName N)
    (hτυ : ∀ p ∈ P, m ‘ p ∈ atomicEquality N T (nameAction m τ.val) υ.val) (γ δ : V) :
    IsWoodinNamedPrefixCutoff P R one γ τ.val δ ↔ IsWoodinNamedPrefixCutoff N T one γ υ.val δ := by
  have hh (p : V) (hp : p ∈ P) :
      p ∈ forcingFormula P R woodinLocalRestorationFormula (standardTuple ![τ.val, checkName one δ]) ↔
        m ‘ p ∈ forcingFormula N T woodinLocalRestorationFormula (standardTuple ![υ.val, checkName one δ]) := by
    apply forcingFormula_retraction_congr_iff hr hR hT he woodinLocalRestorationFormula
      ![τ, ⟨checkName one δ, checkName_isName ht.1 δ⟩]
      ![υ, ⟨checkName one δ, checkName_isName ho δ⟩] hp
    intro i
    refine Fin.cases (hτυ p hp) (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) i
    change m ‘ p ∈ atomicEquality N T (nameAction m (checkName one δ)) (checkName one δ)
    rw [nameAction_checkName ht.1 (hr.fixes one ho), atomicEquality_refl hT]
    exact function_value_mem hr.maps hp
  unfold IsWoodinNamedPrefixCutoff
  apply and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h p hp
    have hq := (hh p (hr.inclusion p hp)).mp (h p (hr.inclusion p hp))
    rwa [hr.fixes p hp] at hq
  · intro h p hp
    exact (hh p hp).mpr (h _ (function_value_mem hr.maps hp))

theorem IsForcingRetraction.named_prefix_cutoff {P R N T m one : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (τ : ForcingName P) (υ : ForcingName N)
    (hτυ : ∀ p ∈ P, m ‘ p ∈ atomicEquality N T (nameAction m τ.val) υ.val) (γ : V) :
    woodinNamedPrefixCutoff P R one γ τ.val = woodinNamedPrefixCutoff N T one γ υ.val := by
  have hh : (fun a b ↦ IsWoodinNamedPrefixCutoff P R one a τ.val b) =
      (fun a b ↦ IsWoodinNamedPrefixCutoff N T one a υ.val b) := by
    funext a b
    exact propext (hr.named_prefix_cutoff_iff hR hT he ht ho τ υ hτυ a b)
  unfold woodinNamedPrefixCutoff
  congr 1

theorem IsForcingRetraction.hartogs_prefix_cutoff {P R N T m one : V}
    (hr : IsForcingRetraction N T P R m)
    (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N) (γ : V) :
    woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ)) =
      woodinNamedPrefixCutoff N T one γ (hartogsNumberName N T (checkName one γ)) := by
  apply hr.named_prefix_cutoff hR hT he ht ho
    ⟨_, hartogsNumberName_isName _ _ _⟩ ⟨_, hartogsNumberName_isName _ _ _⟩
  intro p hp
  apply hr.hartogs_name_equality hR hT he ht ho hp
    ⟨_, checkName_isName ht.1 γ⟩ ⟨_, checkName_isName ho γ⟩
  change m ‘ p ∈ atomicEquality N T (nameAction m (checkName one γ)) (checkName one γ)
  rw [nameAction_checkName ht.1 (hr.fixes one ho), atomicEquality_refl hT]
  exact function_value_mem hr.maps hp

end ZFVP
