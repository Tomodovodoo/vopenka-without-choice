import ZFVP.ModelTheory.TransitiveZFCoding
import ZFVP.ModelTheory.InternalArithmeticGraphs

/-! Addition and multiplication agree in a transitive ZF model and its ambient model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem natural_mem {n : V} (hn : n ∈ (ω : V)) : n ∈ U :=
  (inferInstance : IsTransitive U).mem_trans hn (omega_val U ▸ (ω : SetDomain U).property)

theorem natural_graph_value (F : SetDomain U → SetDomain U) (hF : ℒₛₑₜ-function₁ F)
    {n : SetDomain U} (hn : n ∈ (ω : SetDomain U)) :
    (definableGraph ω F hF).val ‘ n.val = (F n).val := by
  rw [← value_val U (definableGraph ω F hF) n (by simpa only [domain_definableGraph] using hn),
    value_definableGraph _ _ hF hn]

theorem ordinalAdd_val (a b : SetDomain U) (ha : a ∈ (ω : SetDomain U))
    (hb : b ∈ (ω : SetDomain U)) : (ordinalAdd a b).val = ordinalAdd a.val b.val := by
  let f : V := (definableGraph ω (ordinalAdd a) (ordinalAdd_right_definable a)).val
  have hf {n : SetDomain U} (hn : n ∈ (ω : SetDomain U)) : f ‘ n.val = (ordinalAdd a n).val :=
    natural_graph_value U _ _ hn
  have h₀ : f ‘ (0 : V) = a.val := by
    have h := hf (n := 0) (by simp)
    simpa only [zero_def, empty_val, ordinalAdd_zero] using h
  have hs : ∀ n ∈ (ω : V), f ‘ (succ n) = succ (f ‘ n) := by
    intro n hn
    let n' : SetDomain U := ⟨n, natural_mem U hn⟩
    have hn' : n' ∈ (ω : SetDomain U) := (natural_iff U n').mpr hn
    let : IsOrdinal a := IsOrdinal.of_mem ha
    let : IsOrdinal n' := IsOrdinal.of_mem hn'
    have h := hf (ω_succ_closed hn')
    rw [succ_val U, ordinalAdd_succ, succ_val U, ← hf hn'] at h
    exact h
  have hrec : ∀ n ∈ (ω : V), f ‘ n = ordinalAdd a.val n := by
    apply naturalNumber_induction (fun n ↦ f ‘ n = ordinalAdd a.val n) (by definability)
    · simpa only [show (0 : V) = ∅ from rfl, ordinalAdd_zero] using h₀
    · intro n hn ih
      let : IsOrdinal a.val := IsOrdinal.of_mem ((natural_iff U a).mp ha)
      let : IsOrdinal n := IsOrdinal.of_mem hn
      rw [hs n hn, ordinalAdd_succ, ih]
  exact (hf hb).symm.trans (hrec b.val ((natural_iff U b).mp hb))

theorem naturalMul_val (a b : SetDomain U) (ha : a ∈ (ω : SetDomain U))
    (hb : b ∈ (ω : SetDomain U)) : (naturalMul a b).val = naturalMul a.val b.val := by
  let hF : ℒₛₑₜ-function₁ (naturalMul a) := by definability
  let f : V := (definableGraph ω (naturalMul a) hF).val
  have hf {n : SetDomain U} (hn : n ∈ (ω : SetDomain U)) : f ‘ n.val = (naturalMul a n).val :=
    natural_graph_value U _ _ hn
  have h₀ : f ‘ (0 : V) = 0 := by
    have h := hf (n := 0) (by simp)
    simpa only [zero_def, empty_val, naturalMul_empty] using h
  have hs : ∀ n ∈ (ω : V), f ‘ (succ n) = ordinalAdd (f ‘ n) a.val := by
    intro n hn
    let n' : SetDomain U := ⟨n, natural_mem U hn⟩
    have hn' : n' ∈ (ω : SetDomain U) := (natural_iff U n').mpr hn
    have h := hf (ω_succ_closed hn')
    rw [succ_val U, naturalMul_succ a hn', ordinalAdd_val U _ _ (naturalMul_natural ha hn') ha,
      ← hf hn'] at h
    exact h
  have hrec : ∀ n ∈ (ω : V), f ‘ n = naturalMul a.val n := by
    apply naturalNumber_induction (fun n ↦ f ‘ n = naturalMul a.val n) (by definability)
    · simpa only [naturalMul_zero] using h₀
    · intro n hn ih
      rw [hs n hn, naturalMul_succ _ hn, ih]
  exact (hf hb).symm.trans (hrec b.val ((natural_iff U b).mp hb))

end TransitiveZF
end ZFVP
