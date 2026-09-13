import ZFVP.ModelTheory.StageObligations
import ZFVP.ModelTheory.RubinFinitePreservingSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {M : Type u} [SetStructure M] [Nonempty M] [Countable M]

/-- All directed bounds and inseparability obligations, with no new members of old finite sets. -/
theorem exists_finite_extension_all_directed [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (O : Set ((M → Prop) × (M → Prop))) (hO : O.Countable)
    (hins : ∀ p ∈ O, Inseparable M p.1 p.2) :
    ∃ (N : Type u) (_ : SetStructure N) (_ : Nonempty N) (_ : Countable N)
      (j : ElementaryMap M N),
      PreservesInternallyFiniteSets j ∧
      (∀ p ∈ O, Inseparable N (fun y ↦ ∃ a, p.1 a ∧ y = j a) (fun y ↦ ∃ b, p.2 b ∧ y = j b)) ∧
      ∀ (d : SetTheorySemiformula M 1) (r : SetTheorySemiformula M 2),
        DirectedNoLast (fun x ↦ d.Eval ![x] id) (fun x y ↦ r.Eval ![x, y] id) →
          ∃ e : N, d.Eval ![e] (fun m ↦ j m) ∧
            ∀ m : M, d.Eval ![m] id → r.Eval ![j m, e] (fun m ↦ j m) := by
  classical
  obtain ⟨δ, ρ, hdir, hcov⟩ := exists_directed_enumeration (M := M)
  obtain ⟨V, W, hVW, hOcov⟩ := exists_inseparable_enumeration O hO hins
  obtain ⟨E, hfinite⟩ := exists_finite_preserving_rubin_successor M δ ρ V W hVW hdir
  refine ⟨E.Model, E.setStructure, E.nonempty, E.countable, E.embedding, hfinite, fun p hp ↦ ?_,
    fun d r hdr ↦ ?_⟩
  · obtain ⟨n, hV, hW⟩ := hOcov p hp
    have := E.inseparable n
    rw [hV, hW] at this
    exact this
  · obtain ⟨n, hd, hr⟩ := hcov d r hdr
    obtain ⟨x, hmem, hbound⟩ := E.upperBound n
    rw [hd] at hmem
    refine ⟨x, hmem, fun m hm ↦ ?_⟩
    have := hbound m (by rw [dset, hd]; exact hm)
    rw [hr] at this
    exact this

end ZFVP
