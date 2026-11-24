import Chain.Model
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open scoped Topology Matrix Interval
open Set Filter MeasureTheory

namespace Catenary

section
attribute [local instance] Matrix.linftyOpSemiNormedRing Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

private def entryCLM {m : ℕ} (v i : Chamber m) : Mat m →L[ℝ] ℝ :=
  { Matrix.entryLinearMap ℝ ℝ v i with cont := continuous_apply_apply v i }

private def jet {m : ℕ} (A : Mat m) (i v : Chamber m) (q : ℕ) (t : ℝ) : ℝ :=
  ((NormedSpace.exp ℝ (t • A)) * A ^ q) v i

private theorem jet_deriv {m : ℕ} (A : Mat m) (i v : Chamber m) (q : ℕ) (t : ℝ) :
    HasDerivAt (jet A i v q) (jet A i v (q+1) t) t := by
  have h := (hasDerivAt_exp_smul_const A t).mul_const (A^q)
  have hh := (entryCLM v i).hasFDerivAt.comp_hasDerivAt t h
  simpa [jet, entryCLM, Function.comp_def, mul_assoc, pow_succ'] using hh

private theorem continuous_jet {m : ℕ} (A : Mat m) (i v : Chamber m) (q : ℕ) :
    Continuous (jet A i v q) :=
  continuous_iff_continuousAt.mpr fun t => (jet_deriv A i v q t).continuousAt

private theorem jet_zero {m : ℕ} (A : Mat m) (i v : Chamber m) :
    jet A i v 0 = kernel A i v := by funext t; simp [jet, kernel]

theorem continuous_kernel {m : ℕ} (A : Mat m) (i v : Chamber m) :
    Continuous (kernel A i v) := by
  simpa only [jet_zero] using continuous_jet A i v 0

private theorem step_eq_primitive {m : ℕ} (A : Mat m) (i v : Chamber m) (t : ℝ) :
    amount A i v (fun _ => 1) t = ∫ s in (0:ℝ)..t, kernel A i v s := by
  simp only [amount, mul_one]
  simp [intervalIntegral.integral_comp_sub_left]

private theorem eq_deriv_Ioi {f g f' g' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (heq : EqOn f g (Ioi 0)) : EqOn f' g' (Ioi 0) := by
  intro t ht
  have e : f =ᶠ[𝓝 t] g := (isOpen_Ioi.eventually_mem ht).mono fun x hx => heq hx
  exact (hf t).unique ((hg t).congr_of_eventuallyEq e)

theorem markov_eq_of_step {m : ℕ} {A B : Mat m} {i v : Chamber m}
    (h : ∀ t : ℝ, 0 ≤ t → amount A i v (fun _ => 1) t = amount B i v (fun _ => 1) t) :
    ∀ q : ℕ, (A^q) v i = (B^q) v i := by
  have primitiveDeriv (M : Mat m) (t : ℝ) :
      HasDerivAt (fun b : ℝ => ∫ s in (0:ℝ)..b, kernel M i v s) (kernel M i v t) t := by
    have hc := continuous_kernel M i v
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable ..)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hstep : EqOn (fun b : ℝ => ∫ s in (0:ℝ)..b, kernel A i v s)
      (fun b : ℝ => ∫ s in (0:ℝ)..b, kernel B i v s) (Ioi 0) := by
    intro t ht
    simpa only [step_eq_primitive] using h t (le_of_lt ht)
  have hj : ∀ q, EqOn (jet A i v q) (jet B i v q) (Ioi 0) := by
    intro q
    induction q with
    | zero =>
      simpa only [jet_zero] using eq_deriv_Ioi (primitiveDeriv A) (primitiveDeriv B) hstep
    | succ q ih =>
      exact eq_deriv_Ioi (jet_deriv A i v q) (jet_deriv B i v q) ih
  intro q
  have hc := (hj q).closure (continuous_jet A i v q) (continuous_jet B i v q)
  have hz : (0 : ℝ) ∈ closure (Ioi (0:ℝ)) := by simp [closure_Ioi]
  simpa [jet] using hc hz

private theorem kernel_series {m : ℕ} (A : Mat m) (i v : Chamber m) (t : ℝ) :
    kernel A i v t = ∑' q : ℕ, ((q.factorial : ℝ)⁻¹ * t^q) * (A^q) v i := by
  have hs := NormedSpace.expSeries_summable' (𝕂:=ℝ) (t • A)
  have hh := (entryCLM v i).map_tsum hs
  simpa [kernel, NormedSpace.exp_eq_tsum, entryCLM, smul_pow, mul_assoc] using hh

theorem amount_eq_of_markov {m : ℕ} {A B : Mat m} {i v : Chamber m}
    (h : ∀ q : ℕ, (A^q) v i = (B^q) v i) (u : ℝ → ℝ) (t : ℝ) :
    amount A i v u t = amount B i v u t := by
  have hk (s : ℝ) : kernel A i v s = kernel B i v s := by
    rw [kernel_series, kernel_series]
    exact tsum_congr fun q => by rw [h q]
  simp only [amount, hk]

/-- Equality of both complete input/output experiments is equivalent to equality
of the two sequences of Markov parameters of the physical generator. -/
theorem sameCurves_iff_markov {m : ℕ} (i j k ℓ : Chamber m) (θ η : Params m) :
    SameCurves i j k ℓ θ η ↔
    ((∀ q : ℕ, (generator ℓ θ ^ q) j i = (generator ℓ η ^ q) j i) ∧
     (∀ q : ℕ, (generator ℓ θ ^ q) k i = (generator ℓ η ^ q) k i)) := by
  constructor
  · intro h
    exact ⟨markov_eq_of_step fun t ht => (h (fun _ => 1) continuous_const t ht).1,
           markov_eq_of_step fun t ht => (h (fun _ => 1) continuous_const t ht).2⟩
  · rintro ⟨hj,hk⟩ u _ t _
    exact ⟨amount_eq_of_markov hj u t, amount_eq_of_markov hk u t⟩

end
end Catenary
