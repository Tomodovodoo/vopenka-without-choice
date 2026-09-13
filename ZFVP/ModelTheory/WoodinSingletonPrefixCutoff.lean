import ZFVP.ModelTheory.SingletonForcingTruth
import ZFVP.ModelTheory.WoodinLeastRestorationRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem singleton_woodinPrefixCutoff_iff (u κ δ : V) :
    IsWoodinPrefixCutoff {u} (({u} : V) ×ˢ {u}) u κ δ ↔
      IsWoodinRestorationCutoff κ δ := by
  rw [woodinRestorationCutoff_iff_local]
  unfold IsWoodinPrefixCutoff
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  have ht := singletonForcing_checked_parameters_truth u ![κ, δ] woodinLocalRestorationFormula
  have hv : (fun i ↦ checkName u (![κ, δ] i)) = ![checkName u κ, checkName u δ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [hv] at ht
  simpa only [mem_singleton_iff, forall_eq, Defined.eval_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one] using ht

theorem woodinPrefixCutoff_singleton (u κ : V) :
    woodinPrefixCutoff {u} (({u} : V) ×ˢ {u}) u κ = woodinRestorationCutoff κ := by
  have he : IsWoodinPrefixCutoff {u} (({u} : V) ×ˢ {u}) u =
      (IsWoodinRestorationCutoff : V → V → Prop) := by
    funext a b
    exact propext (singleton_woodinPrefixCutoff_iff u a b)
  unfold woodinPrefixCutoff woodinRestorationCutoff
  congr 1

end ZFVP
