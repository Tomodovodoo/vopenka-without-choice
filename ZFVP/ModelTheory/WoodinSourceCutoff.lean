import ZFVP.ModelTheory.ForcingIsomorphismCanonicalNames
import ZFVP.SetTheory.WoodinNamedPrefixCutoff
import ZFVP.ModelTheory.WoodinSourceLimits
import ZFVP.ModelTheory.InverseSourceCollapseCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFormula_isomorphism_congr_iff {P R Q S f p : V}
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (hf : IsForcingIsomorphism P R Q S f) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → ForcingName P) (w : Fin n → ForcingName Q) (hp : p ∈ P)
    (he : ∀ i, f ‘ p ∈ atomicEquality Q S (nameAction f (v i).val) (w i).val) :
    f ‘ p ∈ forcingFormula Q S φ (standardTuple (fun i ↦ (w i).val)) ↔
      p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val)) := by
  have hh := classForcingFormula_congr hS (IsForcingName Q) (by definability) φ
    (fun i ↦ nameAction f (v i).val) (fun i ↦ (w i).val) (function_value_mem hf.1 hp) he
  exact hh.symm.trans (forcingFormula_isomorphism_iff hR hS hf φ _ (fun i ↦ (v i).property) hp)

theorem IsForcingIsomorphism.named_prefix_cutoff_iff {P R Q S f one top : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (τ : ForcingName P) (υ : ForcingName Q)
    (he : ∀ p ∈ P, f ‘ p ∈ atomicEquality Q S (nameAction f τ.val) υ.val) (γ δ : V) :
    IsWoodinNamedPrefixCutoff P R one γ τ.val δ ↔
      IsWoodinNamedPrefixCutoff Q S top γ υ.val δ := by
  have hh (p : V) (hp : p ∈ P) := forcingFormula_isomorphism_congr_iff hR hS hf
    woodinLocalRestorationFormula ![τ, ⟨checkName one δ, checkName_isName ht.1 _⟩]
    ![υ, ⟨checkName top δ, checkName_isName ht'.1 _⟩] hp (by
      intro i
      refine Fin.cases (he p hp) (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) i
      change f ‘ p ∈ atomicEquality Q S (nameAction f (checkName one δ)) (checkName top δ)
      rw [nameAction_checkName_map ht.1, hft, atomicEquality_refl hS]
      exact function_value_mem hf.1 hp)
  unfold IsWoodinNamedPrefixCutoff
  apply and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h q hq
    have hx := (hh _ (function_value_mem hf.inverse_maps hq)).mpr
      (h _ (function_value_mem hf.inverse_maps hq))
    have hw : (fun i : Fin 2 ↦ ((![υ, ⟨checkName top δ, checkName_isName ht'.1 _⟩] :
        Fin 2 → ForcingName Q) i).val) = ![υ.val, checkName top δ] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    simpa only [hf.value_inverse hq, hw] using hx
  · intro h p hp
    exact (hh p hp).mp (h _ (function_value_mem hf.1 hp))

theorem IsForcingIsomorphism.named_prefix_cutoff {P R Q S f one top : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (τ : ForcingName P) (υ : ForcingName Q)
    (he : ∀ p ∈ P, f ‘ p ∈ atomicEquality Q S (nameAction f τ.val) υ.val) (γ : V) :
    woodinNamedPrefixCutoff P R one γ τ.val = woodinNamedPrefixCutoff Q S top γ υ.val := by
  have hh : (fun a b ↦ IsWoodinNamedPrefixCutoff P R one a τ.val b) =
      (fun a b ↦ IsWoodinNamedPrefixCutoff Q S top a υ.val b) := by
    funext a b
    exact propext (hf.named_prefix_cutoff_iff hR hS ht ht' hft τ υ he a b)
  unfold woodinNamedPrefixCutoff
  congr 1

theorem IsForcingIsomorphism.hartogs_prefix_cutoff {P R Q S f one top : V}
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (hft : f ‘ one = top) (γ : V) :
    woodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ)) =
      woodinNamedPrefixCutoff Q S top γ (hartogsNumberName Q S (checkName top γ)) := by
  apply hf.named_prefix_cutoff hR hS ht ht' hft
    ⟨_, hartogsNumberName_isName _ _ _⟩ ⟨_, hartogsNumberName_isName _ _ _⟩
  intro p hp
  apply hf.hartogs_name_equality hR hS ht ht' hp
    ⟨_, checkName_isName ht.1 γ⟩ ⟨_, checkName_isName ht'.1 γ⟩
  change f ‘ p ∈ atomicEquality Q S (nameAction f (checkName one γ)) (checkName top γ)
  rw [nameAction_checkName_map ht.1, hft, atomicEquality_refl hS]
  exact function_value_mem hf.1 hp

theorem woodinSourceCode_inverse_top_value {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hzero : (∅ : V) ∈ θ) :
    (woodinSeedThreadMap θ (forcingInverseCodePoset θ s)) ‘ (forcingInverseCodeTop θ s) =
      forcingInverseCodeTop (woodinSourceIndex θ) (woodinSourceCode θ s) := by
  have hc := hs.system.inverseColumn hzero hs.subset_universe
  have hp : forcingInverseCodeTop θ s ∈ forcingInverseCodePoset θ s := hc.tops.top.1
  rw [woodinSeedThreadMap, value_definableGraph _ _ _ hp,
    woodinSourceCode_inverse_top hs hzero]

theorem woodinSourceCode_inverse_cutoff {θ s : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (hzero : (∅ : V) ∈ θ) (γ : V) :
    forcingInverseSourceCutoff θ s γ =
      forcingInverseSourceCutoff (woodinSourceIndex θ) (woodinSourceCode θ s) γ := by
  have hc := hs.system.inverseColumn hzero hs.subset_universe
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  have hs' := woodinSourceCode_valid hs
  have hc' := hs'.system.inverseColumn hz hs'.subset_universe
  exact (woodinSourceCode_inverse_isomorphism hs).hartogs_prefix_cutoff
    hc.order.preorder hc'.order.preorder hc.tops.top hc'.tops.top
    (woodinSourceCode_inverse_top_value hs hzero) γ

end ZFVP
