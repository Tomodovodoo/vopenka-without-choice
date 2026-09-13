import ZFVP.ModelTheory.GenericFilterName
import ZFVP.SetTheory.CantorSpace

/-! The name of the generic real of Cohen forcing on finite binary sequences: the pairs `(ž, s)`
for `z ∈ s`. Its value is the union of the generic filter, in any context whose poset is the set of
finite binary sequences with top `∅`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The name `{(ž, s) : s ∈ 2^{<ω}, z ∈ s}` of the generic real. -/
noncomputable def binarySequenceRealName (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  repl (fun w ↦ ⟨checkName ∅ (kpair.π₂ w), kpair.π₁ w⟩ₖ) (by definability)
    {w ∈ binarySequences V ×ˢ ⋃ˢ (binarySequences V) ; kpair.π₂ w ∈ kpair.π₁ w}

theorem mem_binarySequenceRealName_iff (y : V) :
    y ∈ binarySequenceRealName V ↔ ∃ s ∈ binarySequences V, ∃ z ∈ s, y = ⟨checkName ∅ z, s⟩ₖ := by
  unfold binarySequenceRealName
  rw [repl_spec]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hw, hzs⟩ := mem_sep_iff.mp hw
    obtain ⟨s, hs, z, _, rfl⟩ := mem_prod_iff.mp hw
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hzs ⊢
    exact ⟨s, hs, z, hzs, rfl⟩
  · rintro ⟨s, hs, z, hz, rfl⟩
    refine ⟨⟨s, z⟩ₖ, mem_sep_iff.mpr ⟨kpair_mem_iff.mpr ⟨hs, mem_sUnion_iff.mpr ⟨s, hs, hz⟩⟩, ?_⟩, ?_⟩
    · simp only [kpair.π₁_kpair, kpair.π₂_kpair]
      exact hz
    · simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem binarySequenceRealName_isName : IsForcingName (binarySequences V) (binarySequenceRealName V) := by
  apply (forcingName_iff _ _).mpr
  intro y hy
  obtain ⟨s, hs, z, _, rfl⟩ := (mem_binarySequenceRealName_iff y).mp hy
  exact ⟨checkName ∅ z, s, hs, rfl, checkName_isName (empty_mem_finiteSequences _) z⟩

namespace ForcingContext

/-- The value of the Cohen real name is the union of the generic filter. -/
theorem mem_ofName_binarySequenceRealName (S : ForcingContext V) (hP : S.P = binarySequences V)
    (hone : S.one = ∅) (x : S.Model) :
    x ∈ S.ofName ⟨binarySequenceRealName V, hP ▸ binarySequenceRealName_isName⟩ ↔ ∃ s ∈ S.G, ∃ z ∈ s, x = S.check z := by
  rw [S.mem_ofName_iff]
  constructor
  · rintro ⟨ν, p, hp, hνp, rfl⟩
    obtain ⟨s, _, z, hz, he⟩ := (mem_binarySequenceRealName_iff _).mp hνp
    obtain ⟨hν, hps⟩ := kpair_iff.mp he
    refine ⟨s, hps ▸ hp, z, hz, ?_⟩
    rw [S.check_eq_ofName_checkName]
    congr 1
    apply Subtype.ext
    change ν.val = checkName S.one z
    rw [hν, hone]
  · rintro ⟨s, hs, z, hz, rfl⟩
    refine ⟨⟨checkName S.one z, checkName_isName S.top.1 z⟩, s, hs, ?_, rfl⟩
    refine (mem_binarySequenceRealName_iff _).mpr ⟨s, ?_, z, hz, ?_⟩
    · rw [← hP]
      exact S.generic.1.1 s hs
    · change ⟨checkName S.one z, s⟩ₖ = ⟨checkName ∅ z, s⟩ₖ
      rw [hone]

end ForcingContext

end ZFVP
