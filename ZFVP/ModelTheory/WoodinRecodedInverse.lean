import ZFVP.ModelTheory.WoodinNormalizedInverseBase
import ZFVP.ModelTheory.WoodinRecodedDirect
import ZFVP.ModelTheory.ForcingRecodedInverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodedInverseBaseMap (θ m : V) : V :=
  forcingThreadActionMap θ m (woodinNormalizedInverseBase θ)

instance woodinRecodedInverseBaseMap_definable : ℒₛₑₜ-function₂[V] woodinRecodedInverseBaseMap := by
  unfold woodinRecodedInverseBaseMap
  apply Language.DefinableFunction₃.comp <;> definability

variable {Ω θ Q T m : V} [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "D" => woodinNormalizedInverseBase θ
local notation "R" => woodinNormalizedInverseOrder θ
local notation "c" => forcingRecodedCode θ N Q T m
local notation "A" => forcingInverseCodePoset θ c
local notation "B" => forcingInverseCodeOrder θ c
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i)
  (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)

include hΩ hAC hθ hm hT hQt hTt in
theorem woodinRecodedInverseBaseMap_isomorphism :
    IsForcingIsomorphism D R A B (woodinRecodedInverseBaseMap θ m) := by
  exact forcingRecoded_inverseCode_isomorphism (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    hm hT hQt hTt (woodinNormalizedPrefix_subset_universe hΩ hAC hθ)

omit [IsOrdinal θ] in
theorem woodinRecodedInverseBaseMap_coordinate {f i : V} (hf : f ∈ D) (hi : i ∈ θ) :
    ((woodinRecodedInverseBaseMap θ m) ‘ f) ‘ i = (m ‘ i) ‘ (f ‘ i) := by
  rw [woodinRecodedInverseBaseMap, forcingThreadActionMap_value hf, forcingThreadAction_value hi]

include hΩ hAC hθ hm hT hQt hTt in
theorem woodinRecodedInverseBaseMap_top (h0 : ∅ ∈ θ) :
    (woodinRecodedInverseBaseMap θ m) ‘ (forcingInverseCodeTop θ (woodinIterationPrefix θ)) =
      forcingInverseCodeTop θ c := by
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  have hc := forcingRecoded_code (s := N) (Q := Q) (T := T) (m := m) hs hm hT hQt hTt
  have hx := woodinIterationExit hΩ hAC
  have hr := woodinIterationPrefix_of_stages (fun i hi ↦ (hx.2.1 i (hθ i hi)).1)
  have ht := (woodinNormalized_inverse_base_laws hΩ hAC hθ h0).2
  have hfun : IsFunction (forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) ∅ ((forcingCodet c) ‘ ∅)) := by
    unfold forcingSectionThread
    infer_instance
  let := hfun
  rw [woodinRecodedInverseBaseMap, forcingThreadActionMap_value ht.1]
  unfold forcingThreadAction forcingInverseCodeTop
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, forcingSectionThread, domain_definableGraph]
  · intro i hi
    rw [domain_definableGraph] at hi
    rw [value_definableGraph _ _ _ hi, forcingSectionThread_top_value hr.code.system.tops h0 hi,
      forcingSectionThread_top_value hc.system.tops h0 hi]
    simp only [forcingRecodedCode, forcingCodet_code, forcingRecodedTops_value hi,
      woodinNormalizedPrefixCode, forcingNormalizedCode]

end ZFVP
