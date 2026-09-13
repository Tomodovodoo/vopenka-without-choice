import ZFVP.ModelTheory.LimitRankAbsoluteness

/-! A bounded formula for the graph of the cumulative hierarchy, with a rank stage as parameter.

`piOneHierarchyFormula` says `X = hierarchy α`, and it is Pi-one; `ZFVP.SetTheory.PiOneCorrectStage`
explains why there is no Sigma-one form. The Pi-one case of Bagaria's Theorem 4.3 puts a statement
about rank stages under a negation, so the Pi-one graph is of no use there.

What works instead is to hand the formula a third argument `W`, meant to be a rank stage
`hierarchy θ` containing everything in sight, and to read the graph inside `W`: every element of `X`
carries a rank certificate lying in `W` that puts its rank below `α`, and every element of `W`
carrying such a certificate is in `X`. Rank certificates are bounded
(`boundedRankCertificateBody`) and they exist inside every successor-closed stage
(`rankCertificate_exists_in_limit`), so the whole formula is bounded and still says
`X = hierarchy α` at `W = hierarchy θ`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `x` has a rank certificate inside `W` placing its rank below `α`. -/
def boundedRankLtInFormula : SetTheorySemisentence 3 :=
  “x α W. ∃ T ∈ W, ∃ R ∈ W, ∃ f ∈ W, ∃ b ∈ α, !boundedRankCertificateBody T R f b x”

/-- `α` is an ordinal and `X` is the set of members of `W` whose rank, read off a certificate
inside `W`, lies below `α`. -/
def boundedHierarchyGraphFormula : SetTheorySemisentence 3 :=
  “X a W. !IsOrdinal.dfn a ∧ (∀ x ∈ X, !boundedRankLtInFormula x a W) ∧
    ∀ x ∈ W, !boundedRankLtInFormula x a W → x ∈ X”

theorem boundedRankLtInFormula_bounded : IsBoundedSetFormula boundedRankLtInFormula :=
  .exs (.bvar 2) (.exs (.bvar 3) (.exs (.bvar 4) (.exs (.bvar 4)
    (boundedRankCertificateBody_bounded.subst _))))

theorem boundedHierarchyGraphFormula_bounded : IsBoundedSetFormula boundedHierarchyGraphFormula :=
  .and (isOrdinalFormula_bounded.subst _)
    (.and (.all (.bvar 0) (boundedRankLtInFormula_bounded.subst _))
      (.all (.bvar 2) (.or (boundedRankLtInFormula_bounded.subst _).neg (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The literal reading of `boundedRankCertificateBody`: `f` is a rank table on the transitive set
`T` with values in `R`, the set `x` is in `T`, and the table gives `x` the value `b`. -/
def IsRankCertificate (T R f b x : V) : Prop :=
  IsTransitive T ∧ x ∈ T ∧ IsRankTable T R f ∧ ⟨x, b⟩ₖ ∈ f

theorem eval_boundedRankCertificateBody (T R f b x : V) :
    boundedRankCertificateBody.Evalb ![T, R, f, b, x] ↔ IsRankCertificate T R f b x := by
  simp only [boundedRankCertificateBody, IsRankCertificate]
  simp [IsTransitive.dfn, boundedPairMemberFormula]
  constructor
  · rintro ⟨ht, hx, htab, hp⟩
    let _ : IsTransitive T := ⟨ht⟩
    exact ⟨⟨ht⟩, hx, (eval_boundedRankTableFormula R f).mp htab, hp⟩
  · rintro ⟨ht, hx, htab, hp⟩
    let _ : IsTransitive T := ht
    exact ⟨ht.1, hx, (eval_boundedRankTableFormula R f).mpr htab, hp⟩

instance boundedRankCertificateBody_defined :
    Defined (L := ℒₛₑₜ) (M := V)
      (fun v ↦ IsRankCertificate (v 0) (v 1) (v 2) (v 3) (v 4)) boundedRankCertificateBody :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) m) l) k) j) i
    change boundedRankCertificateBody.Evalb v ↔ IsRankCertificate (v 0) (v 1) (v 2) (v 3) (v 4)
    rw [← hv]
    exact eval_boundedRankCertificateBody (v 0) (v 1) (v 2) (v 3) (v 4)⟩

/-- The literal reading of `boundedRankLtInFormula`. -/
def BoundedRankLtIn (x a W : V) : Prop :=
  ∃ T ∈ W, ∃ R ∈ W, ∃ f ∈ W, ∃ b ∈ a, IsRankCertificate T R f b x

theorem eval_boundedRankLtInFormula (x a W : V) :
    boundedRankLtInFormula.Evalb ![x, a, W] ↔ BoundedRankLtIn x a W := by
  simp [boundedRankLtInFormula, BoundedRankLtIn]

instance boundedRankLtInFormula_defined :
    ℒₛₑₜ-relation₃[V] BoundedRankLtIn via boundedRankLtInFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
    change boundedRankLtInFormula.Evalb v ↔ BoundedRankLtIn (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_boundedRankLtInFormula (v 0) (v 1) (v 2)⟩

/-- The literal reading of `boundedHierarchyGraphFormula`. -/
def BoundedHierarchyGraph (X a W : V) : Prop :=
  IsOrdinal a ∧ (∀ x ∈ X, BoundedRankLtIn x a W) ∧
    ∀ x ∈ W, BoundedRankLtIn x a W → x ∈ X

instance boundedHierarchyGraphFormula_defined :
    ℒₛₑₜ-relation₃[V] BoundedHierarchyGraph via boundedHierarchyGraphFormula :=
  ⟨fun v ↦ by
    simp [boundedHierarchyGraphFormula, BoundedHierarchyGraph,
      (boundedRankLtInFormula_defined (V := V)).iff]⟩

/-- A certificate in `V` pins the rank down, and inside a successor-closed stage every member of
that stage has one. So the bounded reading of "rank below `α`" is correct at such a stage. -/
theorem boundedRankLtIn_iff {θ x a : V} [IsOrdinal θ] (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hx : x ∈ hierarchy θ) : BoundedRankLtIn x a (hierarchy θ) ↔ rank x ∈ a := by
  constructor
  · rintro ⟨T, -, R, -, f, -, b, hb, hc⟩
    have hs : sigmaOneRankFormula.Evalb ![b, x] :=
      (eval_sigmaOneRankFormula_witnesses b x).mpr
        ⟨T, R, f, (eval_boundedRankCertificateBody T R f b x).mpr hc⟩
    exact (eval_sigmaOneRankFormula b x).mp hs ▸ hb
  · intro hr
    obtain ⟨T, hT, R, hR, f, hf, hc⟩ := rankCertificate_exists_in_limit hsucc hx
    exact ⟨T, hT, R, hR, f, hf, rank x, hr,
      (eval_boundedRankCertificateBody T R f (rank x) x).mp hc⟩

theorem boundedHierarchyGraph_iff {θ X a : V} [IsOrdinal θ] (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (ha : a ∈ θ) (hX : X ∈ hierarchy θ) :
    BoundedHierarchyGraph X a (hierarchy θ) ↔ IsOrdinal a ∧ X = hierarchy a := by
  have htrans := hierarchy_transitive θ
  refine and_congr_right fun haord ↦ ?_
  let := haord
  constructor
  · rintro ⟨hlo, hhi⟩
    apply mem_ext
    intro x
    rw [mem_hierarchy_iff_rank_mem]
    constructor
    · intro hxX
      exact (boundedRankLtIn_iff hsucc (htrans.mem_trans hxX hX)).mp (hlo x hxX)
    · intro hrx
      have hxθ : x ∈ hierarchy θ := by
        rw [mem_hierarchy_iff_rank_mem]
        exact IsOrdinal.toIsTransitive.mem_trans hrx ha
      exact hhi x hxθ ((boundedRankLtIn_iff hsucc hxθ).mpr hrx)
  · rintro rfl
    constructor
    · intro x hx
      have hxθ : x ∈ hierarchy θ := htrans.mem_trans hx hX
      exact (boundedRankLtIn_iff hsucc hxθ).mpr ((mem_hierarchy_iff_rank_mem x a).mp hx)
    · intro x hxθ hb
      exact (mem_hierarchy_iff_rank_mem x a).mpr ((boundedRankLtIn_iff hsucc hxθ).mp hb)

/-- At a successor-closed rank stage `hierarchy θ` above `α`, the bounded formula says exactly
that `α` is an ordinal and `X` is the stage `hierarchy α`. -/
theorem eval_boundedHierarchyGraphFormula {θ X α : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hα : α ∈ θ) (hX : X ∈ hierarchy θ) :
    boundedHierarchyGraphFormula.Evalb ![X, α, hierarchy θ] ↔ IsOrdinal α ∧ X = hierarchy α :=
  ((boundedHierarchyGraphFormula_defined (V := V)).iff ![X, α, hierarchy θ]).trans
    (boundedHierarchyGraph_iff hsucc hα hX)

theorem boundedHierarchyGraphFormula_holds {θ α : V} [IsOrdinal θ] [IsOrdinal α]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ) (hα : α ∈ θ) :
    boundedHierarchyGraphFormula.Evalb ![hierarchy α, α, hierarchy θ] :=
  (eval_boundedHierarchyGraphFormula hω hsucc hα (hierarchy_mem hα)).mpr ⟨inferInstance, rfl⟩

theorem boundedHierarchyGraph_unique {θ X α : V} [IsOrdinal θ]
    (hω : (ω : V) ∈ θ) (hsucc : ∀ ξ ∈ θ, succ ξ ∈ θ)
    (hα : α ∈ θ) (hX : X ∈ hierarchy θ)
    (h : boundedHierarchyGraphFormula.Evalb ![X, α, hierarchy θ]) :
    X = hierarchy α :=
  ((eval_boundedHierarchyGraphFormula hω hsucc hα hX).mp h).2

end ZFVP
