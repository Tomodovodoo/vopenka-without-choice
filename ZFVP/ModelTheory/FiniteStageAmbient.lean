import ZFVP.ModelTheory.FiniteStageRun

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {M Ω : Type u} [SetStructure M] [SetStructure Ω]

/-- An elementary substructure of a ZF model satisfies ZF. -/
theorem models_zf_of_map_target {A B : Type*} [SetStructure A] [SetStructure B]
    [Nonempty A] [Nonempty B] [B↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : ElementaryMap A B) :
    A↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  refine ⟨fun φ hφ ↦ ?_⟩
  have hs := Theory.models B 𝗭𝗙 hφ
  change φ.Eval ![] Empty.elim at hs ⊢
  apply (j.elementary φ ![] Empty.elim).mpr
  have hf : (j.toFun ∘ (Empty.elim : Empty → A)) = Empty.elim := funext fun x ↦ x.elim
  have hb : (j.toFun ∘ (![] : Fin 0 → A)) = ![] := funext fun x ↦ x.elim0
  rw [hf, hb]
  exact hs

/-- Finite preservation along a StageRun makes each internal finite extension of its
ambient model countable. -/
theorem StageRun.internallyFinite_members_countable (R : StageRun M Ω)
    [Nonempty Ω] [Ω↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hfinite : ∀ β α, β ≤ α → StagePreservesFinite (R.stage β) (R.stage α))
    (a : Ω) (ha : IsInternallyFinite a) : {b : Ω | b ∈ a}.Countable := by
  obtain ⟨i, hi⟩ := R.cover a
  have : Nonempty ↥(R.stage i).carrier := R.stage_nonempty i
  have : (↥(R.stage i).carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_zf_of_map_target (R.stageEmbedding i)
  let a' : ↥(R.stage i).carrier := ⟨a, hi⟩
  have ha' : IsInternallyFinite a' := ((R.stageEmbedding i).map_internallyFinite_iff a').mp ha
  apply (R.countable i).mono
  intro b hb
  obtain ⟨j, hj⟩ := R.cover b
  let k := max i j
  let b' : ↥(R.stage k).carrier := ⟨b, R.inc (le_max_right i j) hj⟩
  have hb' : b' ∈ StageModel.incl (R.inc (le_max_left i j)) a' :=
    ((R.stageEmbedding k).map_mem_iff _ _).mp hb
  obtain ⟨m, hm, he⟩ := hfinite i k (le_max_left i j) (R.inc (le_max_left i j)) a' ha' b' hb'
  have he' : (m : Ω) = b := congrArg (fun x : ↥(R.stage k).carrier ↦ (x : Ω)) he
  exact he' ▸ m.property

end ZFVP
