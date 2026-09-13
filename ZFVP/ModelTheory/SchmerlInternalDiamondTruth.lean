import ZFVP.ModelTheory.SchmerlInternalDiamondModel
import ZFVP.ModelTheory.SchmerlInternalClosedPreservation
import ZFVP.ModelTheory.ForcingChoice
import ZFVP.SetTheory.HartogsDictionary

set_option autoImplicit false

/-! Diamond in the actual forcing quotient. The stationary guessing
property ranges over every subset and every club in that quotient. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace Schmerl

def IsInternalDiamondSequence (A κ : V) : Prop :=
  IsFunction A ∧ domain A = κ ∧ (∀ α ∈ κ, (A ‘ α) ⊆ α) ∧
    ∀ X, X ⊆ κ → IsStationaryIn {α ∈ κ ; A ‘ α = X ∩ α} κ

def internalDiamondSequenceFormula : SetTheorySemisentence 2 :=
  f“A k. !IsFunction.dfn A ∧ !domain.dfn A = k ∧
    (∀ a ∈ k, !value.dfn A a ⊆ a) ∧
    (∀ X, X ⊆ k → ∀ C, !clubInFormula C k →
      ∃ a ∈ k, !value.dfn A a = !inter.dfn X a ∧ a ∈ C)”

theorem eval_internalDiamondSequenceFormula (v : Fin 2 → V) :
    internalDiamondSequenceFormula.Evalb v ↔ IsInternalDiamondSequence (v 0) (v 1) := by
  simp +contextual [internalDiamondSequenceFormula, IsInternalDiamondSequence, IsStationaryIn,
    SetTheory.subset_def, mem_sep_iff, and_assoc]

instance internalDiamondSequenceFormula_defined :
    ℒₛₑₜ-relation[V] IsInternalDiamondSequence via internalDiamondSequenceFormula :=
  ⟨eval_internalDiamondSequenceFormula⟩

def InternalDiamond (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∃ A : V, IsInternalDiamondSequence A (hartogsNumber (ω : V))

def internalDiamondSentence : SetTheorySemisentence 0 :=
  f“∃ A, !internalDiamondSequenceFormula A (!hartogsNumberFormula (!isω))”

theorem eval_internalDiamondSentence :
    internalDiamondSentence.Evalb (M := V) ![] ↔ InternalDiamond V := by
  simp [internalDiamondSentence, InternalDiamond]

end Schmerl

namespace ForcingContext

open Schmerl

theorem check_eq_named_inter_of_forcesMembershipPattern (F : ForcingContext V)
    (τ : ForcingName F.P) {p X B : V} (hp : p ∈ F.G) (hB : B ⊆ X)
    (h : ForcesMembershipPattern F.P F.R F.one τ.val p X B) :
    F.check B = F.ofName τ ∩ F.check X := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (F.mem_check_iff B y).mp hy
    exact mem_inter_iff.mpr
      ⟨(show F.check x ∈ F.ofName τ from ⟨p, hp, (h x (hB x hx)).1 hx⟩),
        (F.check_mem_iff x X).mpr (hB x hx)⟩
  · intro hy
    obtain ⟨hyτ, hyX⟩ := mem_inter_iff.mp hy
    obtain ⟨x, hx, rfl⟩ := (F.mem_check_iff X y).mp hyX
    apply (F.check_mem_iff x B).mpr
    by_contra hnot
    have hn := (genericMeets_negation F.order F.generic
      (atomicMembership_subset F.P F.R (checkName F.one x) τ.val)
      (fun _ ha _ hq hqp ↦ atomicMembership_mono F.order ha hq hqp)).mp
      ⟨p, hp, (h x hx).2 hnot⟩
    exact hn hyτ

end ForcingContext

namespace Schmerl.DiamondModel

variable [Countable V] {κ : V} (hzero : (∅ : V) ∈ κ) {G : Set V}
  (hG : IsExternalForcingGeneric (diamondConditions κ) (diamondOrder κ) G)

theorem genericSequence_stationary (hAC : InternalChoice V)
    (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hcount : ∀ α ∈ κ, IsInternallyCountable α)
    (X : (diamondContext κ hzero G hG).Model) :
    IsStationaryIn {α ∈ (diamondContext κ hzero G hG).check κ ;
      (genericSequence hzero hG) ‘ α = X ∩ α} ((diamondContext κ hzero G hG).check κ) := by
  let F := diamondContext κ hzero G hG
  let : IsOrdinal κ := hκ.1.1
  refine ⟨sep_subset, ?_⟩
  intro C hC
  obtain ⟨τ, rfl⟩ := F.ofName_surjective X
  obtain ⟨σ, rfl⟩ := F.ofName_surjective C
  obtain ⟨base, hbaseG, hbase⟩ := (F.clubName_truth σ κ).mp hC
  obtain ⟨p, hpG, hpg⟩ := externalForcingGeneric_meets_denseBelow F.order F.generic hbaseG
    (diamond_guesses_denseBelow hAC hκ hω hcount σ.property hbase)
  obtain ⟨α, hαp, hpclub, hpattern⟩ := (mem_sep_iff.mp hpg).2
  have hp := hG.1.1 p hpG
  have hα : α ∈ κ := IsOrdinal.toIsTransitive.mem_trans hαp ((mem_diamondConditions κ p).mp hp).1
  have he : (genericSequence hzero hG) ‘ (F.check α) = F.ofName τ ∩ F.check α := by
    rw [genericSequence_value hzero hG hpG hαp]
    exact F.check_eq_named_inter_of_forcesMembershipPattern τ hpG
      (((mem_diamondConditions κ p).mp hp).2.2 α hαp) hpattern
  exact ⟨F.check α, mem_sep_iff.mpr ⟨(F.check_mem_iff α κ).mpr hα, he⟩,
    (show F.check α ∈ F.ofName σ from ⟨p, hpG, hpclub⟩)⟩

theorem genericSequence_diamond (hAC : InternalChoice V)
    (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    (hcount : ∀ α ∈ κ, IsInternallyCountable α) :
    IsInternalDiamondSequence (genericSequence hzero hG) ((diamondContext κ hzero G hG).check κ) := by
  refine ⟨inferInstance, domain_eq_of_mem_function (genericSequence_mem_function hzero hG hκ hω),
    fun _ hα ↦ genericSequence_subset hzero hG hκ hω hα, ?_⟩
  exact fun X _ ↦ genericSequence_stationary hzero hG hAC hκ hω hcount X

end Schmerl.DiamondModel

namespace Schmerl

theorem diamond_hartogs_zero : (∅ : V) ∈ hartogsNumber (ω : V) :=
  IsOrdinal.toIsTransitive.mem_trans empty_mem_ω omega_mem_hartogs_omega

variable [Countable V]

theorem diamondContext_internalDiamond (hAC : InternalChoice V)
    {G : Set V} (hG : IsExternalForcingGeneric
      (diamondConditions (hartogsNumber (ω : V))) (diamondOrder (hartogsNumber (ω : V))) G) :
    InternalDiamond (diamondContext (hartogsNumber (ω : V)) diamond_hartogs_zero G hG).Model := by
  let F := diamondContext (hartogsNumber (ω : V)) diamond_hartogs_zero G hG
  have hκ := hartogsNumber_regular hAC (CardLE.refl (ω : V))
  have he := F.check_hartogs_omega_of_internalOmegaClosed_choice hAC
    (diamond_closedAt_omega hκ omega_mem_hartogs_omega)
  refine ⟨DiamondModel.genericSequence diamond_hartogs_zero hG, ?_⟩
  rw [← he]
  exact DiamondModel.genericSequence_diamond diamond_hartogs_zero hG hAC hκ
    omega_mem_hartogs_omega (fun _ hα ↦ countable_of_mem_hartogs_omega hα)

theorem exists_diamondContext_internalDiamond (hAC : InternalChoice V) :
    ∃ G : Set V, ∃ hG : IsExternalForcingGeneric
      (diamondConditions (hartogsNumber (ω : V))) (diamondOrder (hartogsNumber (ω : V))) G,
      InternalDiamond (diamondContext (hartogsNumber (ω : V)) diamond_hartogs_zero G hG).Model := by
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric (diamond_poset (hartogsNumber (ω : V))).1
    (empty_mem_diamondConditions diamond_hartogs_zero)
  exact ⟨G, hG, diamondContext_internalDiamond hAC hG⟩

theorem exists_internalDiamond_forcingExtension (hAC : InternalChoice V) :
    ∃ F : ForcingContext V, InternalChoice F.Model ∧
      F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) ∧
      internalDiamondSentence.Evalb (M := F.Model) ![] := by
  obtain ⟨G, hG, hd⟩ := exists_diamondContext_internalDiamond hAC
  let F := diamondContext (hartogsNumber (ω : V)) diamond_hartogs_zero G hG
  exact ⟨F, F.internalChoice_of_ground hAC,
    F.check_hartogs_omega_of_internalOmegaClosed_choice hAC
      (diamond_closedAt_omega (hartogsNumber_regular hAC (CardLE.refl (ω : V))) omega_mem_hartogs_omega),
    eval_internalDiamondSentence.mpr hd⟩

end Schmerl
end ZFVP
