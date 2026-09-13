import ZFVP.SetTheory.BitTrees
import ZFVP.ModelTheory.RandomReals
import ZFVP.ModelTheory.FilterDecision
import ZFVP.ModelTheory.StageCountability

/-! The name of the random real: the nice name pairing the check name of `(n, i)` with the bit
tree `bitTree n i`. Its value under the filter of a random real `x` is `x`, so a formula with ground
parameters is decided at `x` by the ground decision set of the lifted random name. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem bitPredicate_definable (n i : V) : ℒₛₑₜ-predicate (fun s : V ↦ n ∈ domain s → s ‘ n = i) := by
  definability

instance bitTree_definable : ℒₛₑₜ-function₂[V] bitTree := by
  have h : ℒₛₑₜ-relation₃ (fun T n i : V ↦ ∀ s, s ∈ T ↔ s ∈ binarySequences V ∧ (n ∈ domain s → s ‘ n = i)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = bitTree (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_bitTree_iff]

namespace ForcingContext

variable (S : ForcingContext V)

/-- Values of checked nice names under a filter containing the checked top. -/
theorem mem_nameValue_check_nice_iff {one Q P σ : V} (hσ : σ ⊆ checkNames one Q ×ˢ P) {H : S.Model}
    (hone : S.check one ∈ H) (y : S.Model) :
    y ∈ nameValue H (S.check σ) ↔ ∃ q z, S.check q ∈ H ∧ ⟨checkName one z, q⟩ₖ ∈ σ ∧ y = S.check z := by
  rw [mem_nameValue_iff]
  constructor
  · rintro ⟨ν, p, hpH, hνp, rfl⟩
    obtain ⟨w, hw, hwe⟩ := (S.mem_check_iff _ _).mp hνp
    obtain ⟨ν₀, hν₀, q, -, rfl⟩ := mem_prod_iff.mp (hσ w hw)
    obtain ⟨z, -, rfl⟩ := (mem_checkNames_iff _ _ _).mp hν₀
    rw [S.check_kpair] at hwe
    obtain ⟨rfl, rfl⟩ := kpair_inj hwe
    exact ⟨q, z, hpH, hw, S.nameValue_check_checkName hone z⟩
  · rintro ⟨q, z, hqH, hw, rfl⟩
    refine ⟨S.check (checkName one z), S.check q, hqH, ?_, (S.nameValue_check_checkName hone z).symm⟩
    rw [← S.check_kpair, S.check_mem_iff]
    exact hw

theorem check_bitTree (n i : V) : S.check (bitTree n i) = bitTree (S.check n) (S.check i) := by
  unfold bitTree
  have h := S.checkEmbedding.map_separation (binarySequences V) (fun s ↦ n ∈ domain s → s ‘ n = i)
    (fun s ↦ S.check n ∈ domain s → s ‘ (S.check n) = S.check i) (bitPredicate_definable n i)
    (bitPredicate_definable (S.check n) (S.check i)) (by
      intro s hs
      have hsf : IsFunction s := binarySequence_isFunction hs
      change (n ∈ domain s → s ‘ n = i) ↔ (S.check n ∈ domain (S.check s) → (S.check s) ‘ (S.check n) = S.check i)
      constructor
      · intro h1 h2
        rw [S.check_domain, S.check_mem_iff] at h2
        rw [S.check_value h2, h1 h2]
      · intro h1 h2
        have h3 : S.check n ∈ domain (S.check s) := by rw [S.check_domain, S.check_mem_iff]; exact h2
        have := h1 h3
        rw [S.check_value h2, S.check_eq_iff] at this
        exact this)
  change S.check (sep (binarySequences V) (fun s ↦ n ∈ domain s → s ‘ n = i) (bitPredicate_definable n i)) =
    sep (S.check (binarySequences V)) (fun s ↦ S.check n ∈ domain s → s ‘ (S.check n) = S.check i)
      (bitPredicate_definable (S.check n) (S.check i)) at h
  rw [h, S.check_binarySequences]

end ForcingContext

theorem randomNameMap_definable :
    ℒₛₑₜ-function₁ (fun p : V ↦ ⟨checkName (binarySequences V) p, bitTree (kpair.π₁ p) (kpair.π₂ p)⟩ₖ) := by
  definability

/-- The random real name. -/
noncomputable def randomName (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  repl (fun p ↦ ⟨checkName (binarySequences V) p, bitTree (kpair.π₁ p) (kpair.π₂ p)⟩ₖ) randomNameMap_definable
    ((ω : V) ×ˢ ((2 : ℕ) : V))

theorem mem_randomName_iff (w : V) : w ∈ randomName V ↔
    ∃ n ∈ (ω : V), ∃ i ∈ ((2 : ℕ) : V), w = ⟨checkName (binarySequences V) ⟨n, i⟩ₖ, bitTree n i⟩ₖ := by
  unfold randomName
  rw [repl_spec randomNameMap_definable]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨n, hn, i, hi, rfl⟩ := mem_prod_iff.mp hp
    exact ⟨n, hn, i, hi, by rw [kpair.π₁_kpair, kpair.π₂_kpair]⟩
  · rintro ⟨n, hn, i, hi, rfl⟩
    exact ⟨⟨n, i⟩ₖ, kpair_mem_iff.mpr ⟨hn, hi⟩, by rw [kpair.π₁_kpair, kpair.π₂_kpair]⟩

theorem randomName_subset :
    randomName V ⊆ checkNames (binarySequences V) ((ω : V) ×ˢ ((2 : ℕ) : V)) ×ˢ randomConditions V := by
  intro w hw
  obtain ⟨n, hn, i, hi, rfl⟩ := (mem_randomName_iff w).mp hw
  exact kpair_mem_iff.mpr ⟨(mem_checkNames_iff _ _ _).mpr ⟨_, kpair_mem_iff.mpr ⟨hn, hi⟩, rfl⟩,
    (mem_randomConditions_iff _).mpr (bitTree_positive hn hi)⟩

theorem randomName_isName : IsForcingName (randomConditions V) (randomName V) :=
  subsetNames_isName ((mem_randomConditions_iff _).mpr fullTree_positive) (mem_power_iff.mpr randomName_subset)

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

theorem fullTree_mem_randomFilter {x : (levyContext κ hG).Model} (hx : x ∈ cantorSpace (levyContext κ hG).Model) :
    (levyContext κ hG).check (binarySequences V) ∈ randomFilter hG x := by
  refine (check_mem_randomFilter_iff hG x _).mpr ⟨fullTree_positive, ?_⟩
  rw [(levyContext κ hG).check_binarySequences]
  exact (mem_treeBody_iff _ _).mpr ⟨hx, fun n hn ↦ restrict_mem_binarySequences hx hn⟩

/-- The value of the random name under the filter of a real is the real itself. -/
theorem randomFilter_value {x : (levyContext κ hG).Model} (hx : x ∈ cantorSpace (levyContext κ hG).Model) :
    nameValue (randomFilter hG x) ((levyContext κ hG).check (randomName V)) = x := by
  let W := levyContext κ hG
  have hxc : x ∈ ((2 : ℕ) : W.Model) ^ (ω : W.Model) := (mem_cantorSpace_iff x).mp hx
  have hxf : IsFunction x := IsFunction.of_mem hxc
  have hxdom : domain x = (ω : W.Model) := domain_eq_of_mem_function hxc
  have h2 : W.check ((2 : ℕ) : V) = ((2 : ℕ) : W.Model) := W.checkEmbedding.map_numeral 2
  have hcheckω : ∀ n ∈ (ω : V), W.check n ∈ (ω : W.Model) := fun n hn ↦ by
    rw [← W.check_omega_eq]; exact (W.check_mem_iff _ _).mpr hn
  apply mem_ext
  intro y
  rw [W.mem_nameValue_check_nice_iff randomName_subset (fullTree_mem_randomFilter hG hx)]
  constructor
  · rintro ⟨q, z, hqH, hw, rfl⟩
    obtain ⟨n, hn, i, hi, he⟩ := (mem_randomName_iff _).mp hw
    obtain ⟨hz, rfl⟩ := kpair_inj he
    have hzeq : z = ⟨n, i⟩ₖ := checkName_injective _ hz
    rw [hzeq]
    obtain ⟨-, hxT⟩ := (check_mem_randomFilter_iff hG x _).mp hqH
    rw [W.check_bitTree] at hxT
    obtain ⟨-, hxn⟩ := (mem_treeBody_bitTree_iff (hcheckω n hn)).mp hxT
    rw [W.check_kpair, ← hxn]
    exact kpair_value_mem (by rw [hxdom]; exact hcheckω n hn)
  · intro hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hxc).1 y hy)
    rw [← W.check_omega_eq] at ha
    rw [← h2] at hb
    obtain ⟨n, hn, rfl⟩ := (W.mem_check_iff _ _).mp ha
    obtain ⟨i, hi, rfl⟩ := (W.mem_check_iff _ _).mp hb
    have hxn : x ‘ (W.check n) = W.check i := value_eq_of_kpair_mem hy
    refine ⟨bitTree n i, ⟨n, i⟩ₖ, ?_, (mem_randomName_iff _).mpr ⟨n, hn, i, hi, rfl⟩, (W.check_kpair n i).symm⟩
    refine (check_mem_randomFilter_iff hG x _).mpr ⟨bitTree_positive hn hi, ?_⟩
    rw [W.check_bitTree]
    exact (mem_treeBody_bitTree_iff (hcheckω n hn)).mpr ⟨hx, hxn⟩

include hAC hU hc hω hκ in
/-- Random reals: a formula with ground parameters is decided by the ground decision set of the
random name. -/
theorem random_decision {x : (levyContext κ hG).Model} (hx : IsRandomOver hG x)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (a : Fin n → V) :
    φ.Evalb (x :> fun i ↦ (levyContext κ hG).check (a i)) ↔
      ∃ T, (levyContext κ hG).check T ∈ randomFilter hG x ∧
        T ∈ filterDecisionSet κ (randomConditions V) (inclusionOrder (randomConditions V))
          (binarySequences V) (randomName V) φ a := by
  have h := filter_decision hAC hU hc hω hκ hG (inclusionOrder_preorder (randomConditions V)) randomConditions_top
    (randomFilter_subset hG x) (randomFilter_filter hAC hG hx) (fun D hD ↦ randomFilter_meets hAC hG hx hD.1 hD)
    (randomFilter_localized hAC hU hc hω hκ hG x) randomName_isName φ a
  rw [randomFilter_value hG hx.1] at h
  exact h

end

end ZFVP
