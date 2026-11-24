import Mathlib.Analysis.ODE.PicardLindelof

/-! Nonisolated fibers obtained by integrating a nonzero tangent vector field. -/

noncomputable section

open Set Filter
open scoped Topology

namespace Catenary.Dimension

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → Z} {w : E → E} {a : E}

/-- A local integral curve of a continuously differentiable vector field through `a`
remains in the level set of any first integral. Its derivative at each time is `w`. -/
theorem level_curve_of_ode_invariant (hw : ContDiffAt ℝ 1 w a)
    (hder : ∀ (γ : ℝ → E) (t : ℝ), HasDerivAt γ (w (γ t)) t →
      HasDerivAt (f ∘ γ) 0 t) :
    ∃ γ : ℝ → E, γ 0 = a ∧ ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt γ (w (γ t)) t ∧ f (γ t) = f a := by
  obtain ⟨γ, hγ, ε, hε, hsolve⟩ := exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt 0 hw
  simp only [zero_sub, zero_add] at hsolve
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hd (t : ℝ) (ht : t ∈ Ioo (-ε) ε) := hder γ t (hsolve t ht)
  refine ⟨γ, hγ, ε, hε, fun t ht => ⟨hsolve t ht, ?_⟩⟩
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) ht h0
  simpa only [Function.comp_apply, hγ] using heq

/-- If the vector field is nonzero at `a`, every neighborhood contains a different
point with the same data. The invariant is specified directly along solutions. -/
theorem nonisolated_of_ode_invariant (hw : ContDiffAt ℝ 1 w a)
    (hder : ∀ (γ : ℝ → E) (t : ℝ), HasDerivAt γ (w (γ t)) t →
      HasDerivAt (f ∘ γ) 0 t)
    (ha : w a ≠ 0) {U : Set E} (hU : U ∈ 𝓝 a) :
    ∃ b ∈ U, b ≠ a ∧ f b = f a := by
  obtain ⟨γ, hγ, ε, hε, hsolve⟩ := level_curve_of_ode_invariant hw hder
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hd := (hsolve 0 h0).1
  have hu : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U := hd.continuousAt (by simpa [hγ] using hU)
  by_contra hnone
  have hc : γ =ᶠ[𝓝 (0 : ℝ)] fun _ => a := by
    filter_upwards [isOpen_Ioo.mem_nhds h0, hu] with t ht htu
    by_contra hne
    exact hnone ⟨γ t, htu, hne, (hsolve t ht).2⟩
  have hd0 : HasDerivAt γ 0 (0 : ℝ) := (hasDerivAt_const (0 : ℝ) a).congr_of_eventuallyEq hc
  exact ha (by simpa only [hγ] using hd.unique hd0)

/-- A differentiable data map has a nonisolated fiber wherever an annihilating
continuously differentiable vector field is nonzero. -/
theorem nonisolated_of_vector_field (hw : ContDiff ℝ 1 w) (hf : Differentiable ℝ f)
    (hker : ∀ x, fderiv ℝ f x (w x) = 0) (ha : w a ≠ 0)
    {U : Set E} (hU : U ∈ 𝓝 a) : ∃ b ∈ U, b ≠ a ∧ f b = f a := by
  apply nonisolated_of_ode_invariant hw.contDiffAt _ ha hU
  intro γ t hγ
  simpa only [hker] using (hf (γ t)).hasFDerivAt.comp_hasDerivAt t hγ

end Catenary.Dimension
