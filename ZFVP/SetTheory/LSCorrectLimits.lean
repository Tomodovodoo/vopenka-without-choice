import ZFVP.SetTheory.UsubaLSSequence
import ZFVP.SetTheory.Cn
import ZFVP.SetTheory.NaturalIteration

/-! Unbounded LS cardinals supply unbounded limits of LS cardinals at
correct rank stages. Alternating least choices needs no choice axiom. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem lsCorrectLimit_unbounded
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (n : ℕ) (ξ : V) [IsOrdinal ξ] :
    ∃ κ : V, ξ ∈ κ ∧ IsLSCardinal κ ∧ Cn n κ ∧
      ∀ α ∈ κ, ∃ μ ∈ κ, α ∈ μ ∧ IsLSCardinal μ := by
  let c := leastOrdinalOrZero (fun a b : V ↦ a ∈ b ∧ Cn n b) (by definability)
  have hc (a : V) [IsOrdinal a] : a ∈ c a ∧ Cn n (c a) := by
    obtain ⟨b, hab, hb⟩ := cn_unbounded n a
    exact (leastOrdinalOrZero_spec (fun a b : V ↦ a ∈ b ∧ Cn n b)
      (by definability) a ⟨b, hb.ordinal, hab, hb⟩).2.1
  have hcdef : ℒₛₑₜ-function₁[V] c := by unfold c; definability
  let F := fun a : V ↦ usubaNextLS (c a)
  have hF : ℒₛₑₜ-function₁[V] F := by unfold F; definability
  have hspec (a : V) [IsOrdinal a] :
      a ∈ c a ∧ Cn n (c a) ∧ c a ∈ F a ∧ IsLSCardinal (F a) := by
    let := (hc a).2.ordinal
    exact ⟨(hc a).1, (hc a).2, usubaNextLS_spec hLS (c a)⟩
  let a := naturalIteration F hF ξ
  have ha (i : V) (hi : i ∈ (ω : V)) : IsOrdinal (a i) :=
    naturalIteration_invariant F hF ξ IsOrdinal (by definability) inferInstance
      (fun x _ ↦ (usubaNextLS_ordinal (c x))) i hi
  have hasucc (i : V) (hi : i ∈ (ω : V)) : a (succ i) = F (a i) :=
    naturalIteration_succ F hF ξ hi
  have hinc (i : V) (hi : i ∈ (ω : V)) : a i ∈ a (succ i) := by
    let := ha i hi
    rw [hasucc i hi]
    let := (hspec (a i)).2.2.2.1.1
    exact IsOrdinal.toIsTransitive.mem_trans (hspec (a i)).1 (hspec (a i)).2.2.1
  let D := repl a (by unfold a; definability) (ω : V)
  let κ := ⋃ˢ D
  have hd (y : V) : y ∈ D ↔ ∃ i ∈ (ω : V), y = a i := repl_spec _
  have hκ : IsOrdinal κ := IsOrdinal.sUnion (by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := (hd y).mp hy
    exact ha i hi)
  let := hκ
  have haκ (i : V) (hi : i ∈ (ω : V)) : a i ∈ κ :=
    mem_sUnion_iff.mpr ⟨a (succ i), (hd _).mpr ⟨succ i, ω_succ_closed hi, rfl⟩,
      hinc i hi⟩
  have hcof (z : V) (hz : z ∈ κ) : ∃ i ∈ (ω : V), z ∈ a i := by
    obtain ⟨y, hy, hzy⟩ := mem_sUnion_iff.mp hz
    obtain ⟨i, hi, rfl⟩ := (hd y).mp hy
    exact ⟨i, hi, hzy⟩
  have hξκ : ξ ∈ κ := by simpa only [a, naturalIteration_zero] using haκ 0 (by simp)
  have hLSκ : ∀ z ∈ κ, ∃ μ ∈ κ, z ∈ μ ∧ IsLSCardinal μ := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := hcof z hz
    let := ha i hi
    have hs := hspec (a i)
    have hls : IsLSCardinal (a (succ i)) := hasucc i hi ▸ hs.2.2.2
    let := hls.1.1
    exact ⟨a (succ i), haκ _ (ω_succ_closed hi),
      IsOrdinal.toIsTransitive.mem_trans hzi (hinc i hi), hls⟩
  refine ⟨κ, hξκ, lsCardinal_of_cofinally_ls ⟨ξ, hξκ⟩ hLSκ, ?_, hLSκ⟩
  apply cn_closed n ⟨ξ, hξκ⟩
  intro z hz
  obtain ⟨i, hi, hzi⟩ := hcof z hz
  let := ha i hi
  have hs := hspec (a i)
  let := hs.2.1.ordinal
  refine ⟨c (a i), ?_, IsOrdinal.toIsTransitive.mem_trans hzi hs.1, hs.2.1⟩
  have hcnext : c (a i) ∈ a (succ i) := hasucc i hi ▸ hs.2.2.1
  exact IsOrdinal.toIsTransitive.mem_trans hcnext (haκ _ (ω_succ_closed hi))

end ZFVP
