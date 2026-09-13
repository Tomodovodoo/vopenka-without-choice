import ZFVP.ModelTheory.RetractionHartogsNames
import ZFVP.ModelTheory.ForcingIsomorphismCanonicalNames
import ZFVP.ModelTheory.WoodinSourceCutoff
import ZFVP.ModelTheory.RetractionIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.hartogs_forcing_iff {P R N T n one p γ : V}
    (hr : IsForcingRetraction N T P R n) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨n ‘ q, q⟩ₖ ∈ R ∧ ⟨q, n ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N) (hp : p ∈ P) (φ : SetTheorySemisentence 1) :
    p ∈ forcingFormula P R φ (standardTuple ![hartogsNumberName P R (checkName one γ)]) ↔
      n ‘ p ∈ forcingFormula N T φ (standardTuple ![hartogsNumberName N T (checkName one γ)]) := by
  have hc : n ‘ p ∈ atomicEquality N T (nameAction n (checkName one γ)) (checkName one γ) := by
    rw [nameAction_checkName ht.1 (hr.fixes one ho), atomicEquality_refl hT]
    exact function_value_mem hr.maps hp
  have hh := hr.hartogs_name_equality hR hT he ht ho hp
    ⟨checkName one γ, checkName_isName ht.1 γ⟩ ⟨checkName one γ, checkName_isName ho γ⟩ hc
  have hnames : ∀ i : Fin 1, IsForcingName P ((![hartogsNumberName P R (checkName one γ)] : Fin 1 → V) i) := by
    intro i
    exact Fin.cases (hartogsNumberName_isName _ _ _) (fun j ↦ Fin.elim0 j) i
  have haction := hr.forcingFormula_nameAction_iff hR hT he φ _ hnames hp
  have hcongr := classForcingFormula_congr hT (IsForcingName N) (by definability) φ
    (fun i : Fin 1 ↦ nameAction n ((![hartogsNumberName P R (checkName one γ)] : Fin 1 → V) i))
    (![hartogsNumberName N T (checkName one γ)]) (function_value_mem hr.maps hp)
    (fun i ↦ Fin.cases hh (fun j ↦ Fin.elim0 j) i)
  exact haction.trans hcongr

theorem IsForcingIsomorphism.hartogs_forcing_iff {P R Q S f one t p γ : V}
    (hf : IsForcingIsomorphism P R Q S f) (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (hft : f ‘ one = t) (hp : p ∈ P) (φ : SetTheorySemisentence 1) :
    p ∈ forcingFormula P R φ (standardTuple ![hartogsNumberName P R (checkName one γ)]) ↔
      f ‘ p ∈ forcingFormula Q S φ (standardTuple ![hartogsNumberName Q S (checkName t γ)]) := by
  have ht' : IsForcingTop Q S t := hft ▸ hf.map_top ht
  have hc : f ‘ p ∈ atomicEquality Q S (nameAction f (checkName one γ)) (checkName t γ) := by
    rw [nameAction_checkName_map ht.1, hft, atomicEquality_refl hS]
    exact function_value_mem hf.1 hp
  have hh := hf.hartogs_name_equality hR hS ht ht' hp
    ⟨checkName one γ, checkName_isName ht.1 γ⟩ ⟨checkName t γ, checkName_isName ht'.1 γ⟩ hc
  exact (forcingFormula_isomorphism_congr_iff hR hS hf φ
    ![⟨hartogsNumberName P R (checkName one γ), hartogsNumberName_isName _ _ _⟩]
    ![⟨hartogsNumberName Q S (checkName t γ), hartogsNumberName_isName _ _ _⟩] hp
    (fun i ↦ Fin.cases hh (fun j ↦ Fin.elim0 j) i)).symm

theorem IsForcingRetraction.isomorphism_all_hartogs_forcing_iff {P R N T n Q S f one t γ : V}
    (hr : IsForcingRetraction N T P R n) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨n ‘ q, q⟩ₖ ∈ R ∧ ⟨q, n ‘ q⟩ₖ ∈ R)
    (ht : IsForcingTop P R one) (ho : one ∈ N)
    (hf : IsForcingIsomorphism N T Q S f) (hS : IsForcingPreorder Q S)
    (hft : f ‘ one = t) (φ : SetTheorySemisentence 1) :
    (∀ p ∈ P, p ∈ forcingFormula P R φ (standardTuple ![hartogsNumberName P R (checkName one γ)])) ↔
      ∀ q ∈ Q, q ∈ forcingFormula Q S φ (standardTuple ![hartogsNumberName Q S (checkName t γ)]) := by
  have hh (p : V) (hp : p ∈ P) :
      p ∈ forcingFormula P R φ (standardTuple ![hartogsNumberName P R (checkName one γ)]) ↔
      (compose n f) ‘ p ∈ forcingFormula Q S φ (standardTuple ![hartogsNumberName Q S (checkName t γ)]) := by
    rw [value_compose_of_mem_function hr.maps hf.1 hp]
    exact (hr.hartogs_forcing_iff hR hT he ht ho hp φ).trans
      (hf.hartogs_forcing_iff hT hS (hr.top_of_mem ht ho) hft (function_value_mem hr.maps hp) φ)
  constructor
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := hr.isomorphism_surjective hf q hq
    exact (hh p hp).mp (h p hp)
  · intro h p hp
    exact (hh p hp).mpr (h _ (function_value_mem (compose_function hr.maps hf.1) hp))

end ZFVP

