import ZFVP.SetTheory.NaturalAddition
import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.InverseFunction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def triangularStep (p : V) : V :=
  ⟨succ (kpair.π₁ p), ordinalAdd (kpair.π₂ p) (succ (kpair.π₁ p))⟩ₖ

instance triangularStep_definable : ℒₛₑₜ-function₁[V] triangularStep := by
  unfold triangularStep
  definability

noncomputable def triangularState (n : V) : V :=
  naturalIteration triangularStep (by definability) ⟨0, 0⟩ₖ n

instance triangularState_definable : ℒₛₑₜ-function₁[V] triangularState := by
  unfold triangularState
  definability

noncomputable def triangular (n : V) : V := kpair.π₂ (triangularState n)

instance triangular_definable : ℒₛₑₜ-function₁[V] triangular := by
  unfold triangular
  definability

theorem triangularState_index {n : V} (hn : n ∈ (ω : V)) : kpair.π₁ (triangularState n) = n := by
  apply naturalNumber_induction (fun n ↦ kpair.π₁ (triangularState n) = n) (by definability) ?_ ?_ n hn
  · simp [triangularState, naturalIteration_zero]
  · intro n hn ih
    simp only [triangularState, naturalIteration_succ _ _ _ hn, triangularStep, kpair.π₁_kpair]
    exact congrArg succ ih

theorem triangular_zero : triangular (0 : V) = 0 := by
  simp [triangular, triangularState, naturalIteration_zero]

theorem triangular_succ {n : V} (hn : n ∈ (ω : V)) :
    triangular (succ n) = ordinalAdd (triangular n) (succ n) := by
  change kpair.π₂ (naturalIteration triangularStep _ ⟨0, 0⟩ₖ (succ n)) = _
  rw [naturalIteration_succ _ _ _ hn]
  simp only [triangularStep, kpair.π₂_kpair]
  change ordinalAdd (triangular n) (succ (kpair.π₁ (triangularState n))) = _
  rw [triangularState_index hn]

theorem triangular_natural {n : V} (hn : n ∈ (ω : V)) : triangular n ∈ (ω : V) := by
  apply naturalNumber_induction (fun n ↦ triangular n ∈ (ω : V)) (by definability) ?_ ?_ n hn
  · rw [triangular_zero]
    simp
  · intro n hn ih
    rw [triangular_succ hn]
    exact ordinalAdd_natural ih (ω_succ_closed hn)

theorem triangular_step_lt {n : V} (hn : n ∈ (ω : V)) : triangular n ∈ triangular (succ n) := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  rw [triangular_succ hn]
  have h := ordinalAdd_mem (α := triangular n) (zero_mem_succ_natural hn)
  simpa only [zero_def, ordinalAdd_zero] using h

theorem triangular_mono {n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (h : n ⊆ m) : triangular n ⊆ triangular m := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have hlt : ∀ m ∈ (ω : V), ∀ n ∈ m, triangular n ⊆ triangular m := by
    apply naturalNumber_induction (fun m : V ↦ ∀ n ∈ m, triangular n ⊆ triangular m) (by definability)
    · intro n hn
      simp [zero_def] at hn
    · intro m hm ih n hn
      have : IsOrdinal (triangular (succ m)) := IsOrdinal.of_mem (triangular_natural (ω_succ_closed hm))
      have hs : triangular m ⊆ triangular (succ m) := IsOrdinal.toIsTransitive.transitive _ (triangular_step_lt hm)
      rcases mem_succ_iff.mp hn with heq | hn
      · exact heq.symm ▸ hs
      · exact subset_trans (ih n hn) hs
  rcases IsOrdinal.subset_iff.mp h with heq | hmem
  · exact heq ▸ subset_refl _
  · exact hlt m hm n hmem

noncomputable def naturalPairCode (x y : V) : V := ordinalAdd (triangular (ordinalAdd x y)) x

instance naturalPairCode_definable : ℒₛₑₜ-function₂[V] naturalPairCode := by
  unfold naturalPairCode
  definability

theorem naturalPairCode_natural {x y : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) :
    naturalPairCode x y ∈ (ω : V) := ordinalAdd_natural (triangular_natural (ordinalAdd_natural hx hy)) hx

theorem naturalPairCode_bounds {x y : V} (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) :
    triangular (ordinalAdd x y) ⊆ naturalPairCode x y ∧
      naturalPairCode x y ∈ triangular (succ (ordinalAdd x y)) := by
  have : IsOrdinal x := IsOrdinal.of_mem hx
  have : IsOrdinal y := IsOrdinal.of_mem hy
  have hs := ordinalAdd_natural hx hy
  refine ⟨subset_ordinalAdd _ _, ?_⟩
  rw [triangular_succ hs]
  exact ordinalAdd_mem (mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_ordinalAdd x y)))

theorem naturalPairCode_injective {x y u v : V}
    (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) (hu : u ∈ (ω : V)) (hv : v ∈ (ω : V))
    (heq : naturalPairCode x y = naturalPairCode u v) : x = u ∧ y = v := by
  have : IsOrdinal x := IsOrdinal.of_mem hx
  have : IsOrdinal y := IsOrdinal.of_mem hy
  have : IsOrdinal u := IsOrdinal.of_mem hu
  have : IsOrdinal v := IsOrdinal.of_mem hv
  have hxy := ordinalAdd_natural hx hy
  have huv := ordinalAdd_natural hu hv
  have hsep (a b c d : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
      (hc : c ∈ (ω : V)) (hd : d ∈ (ω : V)) (h : ordinalAdd a b ∈ ordinalAdd c d) :
      naturalPairCode a b ∈ naturalPairCode c d := by
    have : IsOrdinal a := IsOrdinal.of_mem ha
    have : IsOrdinal b := IsOrdinal.of_mem hb
    have : IsOrdinal c := IsOrdinal.of_mem hc
    have : IsOrdinal d := IsOrdinal.of_mem hd
    have hsub : succ (ordinalAdd a b) ⊆ ordinalAdd c d := by
      intro z hz
      rcases mem_succ_iff.mp hz with rfl | hz
      · exact h
      · exact IsOrdinal.toIsTransitive.mem_trans hz h
    exact (naturalPairCode_bounds hc hd).1 _
      (triangular_mono (ω_succ_closed (ordinalAdd_natural ha hb)) (ordinalAdd_natural hc hd) hsub _
        (naturalPairCode_bounds ha hb).2)
  have hsum : ordinalAdd x y = ordinalAdd u v := by
    rcases IsOrdinal.mem_trichotomy (ordinalAdd x y) (ordinalAdd u v) with hlt | he | hgt
    · exact False.elim (mem_irrefl _ (heq ▸ hsep x y u v hx hy hu hv hlt))
    · exact he
    · exact False.elim (mem_irrefl _ (heq.symm ▸ hsep u v x y hu hv hx hy hgt))
  have hxu : x = u := by
    unfold naturalPairCode at heq
    rw [hsum] at heq
    exact ordinalAdd_right_injective heq
  refine ⟨hxu, ?_⟩
  rw [hxu] at hsum
  exact ordinalAdd_right_injective hsum

theorem omega_prod_cardLE_omega : ((ω : V) ×ˢ (ω : V)) ≤# (ω : V) := by
  let F : V → V := fun p ↦ naturalPairCode (kpair.π₁ p) (kpair.π₂ p)
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph ((ω : V) ×ˢ (ω : V)) F hF
  have hf : f ∈ (ω : V) ^ ((ω : V) ×ˢ (ω : V)) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro p hp
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hp
      simpa only [F, kpair.π₁_kpair, kpair.π₂_kpair] using naturalPairCode_natural hx hy)
  refine ⟨f, hf, ?_⟩
  intro p q z hp hq
  obtain ⟨hpD, hzp⟩ := (pair_mem_definableGraph_iff _ F hF p z).mp hp
  obtain ⟨hqD, hzq⟩ := (pair_mem_definableGraph_iff _ F hF q z).mp hq
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hpD
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_prod_iff.mp hqD
  have heq : naturalPairCode x y = naturalPairCode u v := by
    simpa only [F, kpair.π₁_kpair, kpair.π₂_kpair] using hzp.symm.trans hzq
  exact kpair_iff.mpr (naturalPairCode_injective hx hy hu hv heq)

end ZFVP
