import ZFVP.ModelTheory.WoodinCoordinateProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinSelectedThreadDecision (θ i f c d : V) : Prop :=
  ∀ (A : ForcingContext V),
    A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i →
    A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
    A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i → d ∈ A.G →
    ∀ g : ForcingName A.P, g.val = f →
      ∃ X a : A.Model, A.ofName g ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ X ∧
        a ∈ X ∧ (A.ofName g) ‘ a = A.check c

theorem ForcingContext.woodinCoordinate_function {δ θ i j : V} [IsOrdinal θ]
    (A : ForcingContext V)
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName A.P) {X : A.Model}
    (hf : A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ X) :
    A.ofName ⟨woodinBoundCoordinateName θ i f.val j,
      by simpa only [← hP] using woodinBoundCoordinateName_isName θ i f.val j⟩ ∈
      A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X := by
  have hρ := (woodinInverseCoordinate_split hs hj).projection.maps
  have hv := A.forcingCompositionName_value f
    ⟨checkName A.one (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) j),
      checkName_isName A.top.1 _⟩
  change A.ofName ⟨forcingCompositionName A.P A.R f.val
    (checkName A.one (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) j)), _⟩ =
      compose (A.ofName f) (A.check (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) j)) at hv
  simpa only [woodinBoundCoordinateName, ← hP, ← hR, ← ho, hv] using
    compose_function hf ((A.check_function_iff _ _ _).mpr hρ)

theorem ForcingContext.woodinCoordinate_selected {δ θ i f c d j : V} [IsOrdinal θ]
    (A : ForcingContext V)
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hc : c ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hselected : IsWoodinSelectedThreadDecision θ i f c d) (hdG : d ∈ A.G)
    (g : ForcingName A.P) (hg : g.val = f) :
    let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i g.val j,
      by simpa only [← hP] using woodinBoundCoordinateName_isName θ i g.val j⟩
    ∃ X a : A.Model, A.ofName μ ∈ A.check ((forcingCodeP (woodinIterationPrefix θ)) ‘ j) ^ X ∧
      a ∈ X ∧ (A.ofName μ) ‘ a = A.check (c ‘ j) := by
  obtain ⟨X, a, hf, ha, hac⟩ := hselected A hP hR ho hdG g hg
  exact ⟨X, a, A.woodinCoordinate_function hs hj hP hR ho g hf, ha,
    A.woodinCoordinate_value hs hj hP hR ho g hf ha hc hac⟩

def selectedFunctionRangeFormula : SetTheorySemisentence 3 :=
  f“D f c. ∃ X, ∃ a, !boundedFunctionFormula f X D ∧ a ∈ X ∧ !value.dfn c f a”

instance selectedFunctionRangeFormula_defined :
    Defined (fun v : Fin 3 → V ↦ ∃ X a : V, v 1 ∈ v 0 ^ X ∧ a ∈ X ∧ (v 1) ‘ a = v 2)
      selectedFunctionRangeFormula :=
  ⟨fun v ↦ by simp [selectedFunctionRangeFormula, eq_comm]⟩

theorem woodinSelectedThreadDecision_of_forced {θ i f c d : V}
    (hf : d ∈ forcingFormula ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) selectedFunctionRangeFormula
      (standardTuple ![checkName ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
        (forcingInverseCodePoset θ (woodinIterationPrefix θ)), f,
        checkName ((forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i) c])) :
    IsWoodinSelectedThreadDecision θ i f c d := by
  intro A hP hR ho hdG g hg
  have hforce := hf
  rw [← hP, ← hR, ← ho, ← hg] at hforce
  exact (Defined.eval_iff _).mp ((A.formula_truth selectedFunctionRangeFormula
    ![⟨checkName A.one (forcingInverseCodePoset θ (woodinIterationPrefix θ)), checkName_isName A.top.1 _⟩,
      g, ⟨checkName A.one c, checkName_isName A.top.1 _⟩]).mpr ⟨d, hdG, hforce⟩)

theorem ForcingContext.exists_woodinSelectedThreadDecision_below {θ i c e : V}
    (A : ForcingContext V)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName A.P) {X a : A.Model}
    (hf : A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ X)
    (ha : a ∈ X) (hac : (A.ofName f) ‘ a = A.check c) (he : e ∈ A.G) :
    ∃ d ∈ A.G, ⟨d, e⟩ₖ ∈ A.R ∧ IsWoodinSelectedThreadDecision θ i f.val c d := by
  have htruth : selectedFunctionRangeFormula.Evalb
      (fun k ↦ A.ofName ((![⟨checkName A.one (forcingInverseCodePoset θ (woodinIterationPrefix θ)),
        checkName_isName A.top.1 _⟩, f, ⟨checkName A.one c, checkName_isName A.top.1 _⟩] :
          Fin 3 → ForcingName A.P) k)) :=
    (Defined.eval_iff _).mpr ⟨X, a, hf, ha, hac⟩
  obtain ⟨q, hqG, hq⟩ := (A.formula_truth selectedFunctionRangeFormula _).mp htruth
  obtain ⟨d, hdG, hdq, hde⟩ := A.generic.1.2.2.2 q hqG e he
  refine ⟨d, hdG, hde, woodinSelectedThreadDecision_of_forced ?_⟩
  have hd := (forcingFormula_regular A.order selectedFunctionRangeFormula _).2.1
    q hq d (A.generic.1.1 d hdG) hdq
  change d ∈ forcingFormula A.P A.R selectedFunctionRangeFormula
    (standardTuple ![checkName A.one (forcingInverseCodePoset θ (woodinIterationPrefix θ)), f.val,
      checkName A.one c]) at hd
  simpa only [hP, hR, ho] using hd

end ZFVP
