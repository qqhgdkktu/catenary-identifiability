import Chain.Dynamics
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open scoped Topology Matrix Interval BigOperators
open Set MeasureTheory
namespace Catenary

section
attribute [local instance] Matrix.linftyOpSemiNormedRing Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

private def evol {m} (A : Mat m) (t : ℝ) := NormedSpace.exp ℝ (t • A)

private theorem evol_add {m} (A : Mat m) (s t : ℝ) :
    evol A (s+t) = evol A s * evol A t := by
  unfold evol
  rw [add_smul]
  exact Matrix.exp_add_of_commute ℝ _ _ (((Commute.refl A).smul_left s).smul_right t)

private theorem continuous_evol {m} (A : Mat m) : Continuous (evol A) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_smul_const A t).continuousAt

private def integrand {m} (A : Mat m) (u : ℝ → ℝ) (s : ℝ) := u s • evol A (-s)

private theorem integrand_cont {m} (A : Mat m) {u : ℝ → ℝ} (hu : Continuous u) :
    Continuous (integrand A u) := hu.smul ((continuous_evol A).comp continuous_neg)

private def forcedMatrix {m} (A : Mat m) (u : ℝ → ℝ) (t : ℝ) : Mat m :=
  evol A t * ∫ s in (0:ℝ)..t, integrand A u s

private def leftEntry {m} (L : Mat m) (v i : Chamber m) : Mat m →L[ℝ] ℝ :=
  { toFun := fun M => (L*M) v i
    map_add' := by intro M N; simp [mul_add]
    map_smul' := by intro c M; simp [mul_smul_comm]
    cont := (continuous_const.mul continuous_id).matrix_elem v i }

private theorem amount_eq_matrix {m} (A : Mat m) (i v : Chamber m)
    {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    amount A i v u t = forcedMatrix A u t v i := by
  let L := leftEntry (evol A t) v i
  have he : ∀ s, kernel A i v (t-s) * u s = L (integrand A u s) := by
    intro s
    change evol A (t-s) v i * u s = (evol A t * (u s • evol A (-s))) v i
    rw [sub_eq_add_neg, evol_add, mul_smul_comm]
    simp [mul_comm]
  change (∫ s in (0:ℝ)..t, kernel A i v (t-s) * u s) = L _
  simpa only [he] using L.intervalIntegral_comp_comm ((integrand_cont A hu).intervalIntegrable ..)

private theorem forcedMatrix_deriv {m} (A : Mat m) {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    HasDerivAt (forcedMatrix A u) (A * forcedMatrix A u t + u t • 1) t := by
  have hi := integrand_cont A hu
  have hd := intervalIntegral.integral_hasDerivAt_right (a:=0) (b:=t)
     (hi.intervalIntegrable ..) hi.aestronglyMeasurable.stronglyMeasurableAtFilter hi.continuousAt
  have h := (hasDerivAt_exp_smul_const' A t).mul hd
  have z : evol A t * evol A (-t) = 1 := by rw [← evol_add]; simp [evol]
  change HasDerivAt (fun s => evol A s * ∫ τ in (0:ℝ)..s, integrand A u τ)
    (A * (evol A t * ∫ τ in (0:ℝ)..t, integrand A u τ) + u t • 1) t
  change HasDerivAt (fun s => evol A s * ∫ τ in (0:ℝ)..s, integrand A u τ) _ t at h
  convert h using 1
  simp [integrand, mul_smul_comm, ← mul_assoc, evol, add_comm]
  simpa [evol] using congrArg (fun Q : Mat m => u t • Q) z.symm

/-- The amount defined by convolution actually solves x' = A x + e_i u. -/
theorem amounts_solve_ode {m} (A : Mat m) (i : Chamber m) {u : ℝ → ℝ} (hu : Continuous u)
    (t : ℝ) :
    HasDerivAt (fun s v => amount A i v u s)
      (A.mulVec (fun v => amount A i v u t) + Pi.single i (u t)) t := by
  apply hasDerivAt_pi.mpr
  intro v
  let L : Mat m →L[ℝ] ℝ := { Matrix.entryLinearMap ℝ ℝ v i with cont := continuous_apply_apply v i }
  have hh := L.hasFDerivAt.comp_hasDerivAt t (forcedMatrix_deriv A hu t)
  simpa [L, Function.comp_def, amount_eq_matrix A _ _ hu, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm, mul_ite] using hh

end

/-- Uniqueness on the observed half-line; the competing trajectory only needs
the forward derivative, including at the starting time. -/
theorem trajectory_unique {m} (A : Mat m) (i : Chamber m) {u : ℝ → ℝ} (hu : Continuous u)
    (x : ℝ → Chamber m → ℝ) (h₀ : x 0 = 0) (hc : ContinuousOn x (Ici 0))
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt x (A.mulVec (x t) + Pi.single i (u t)) (Ici t) t)
    (t : ℝ) (ht : 0 ≤ t) : x t = fun v => amount A i v u t := by
  let L := A.toLin'.toContinuousLinearMap
  let V := fun s (z : Chamber m → ℝ) => A.mulVec z + Pi.single i (u s)
  have hLip (s : ℝ) : LipschitzWith ‖L‖₊ (V s) := by
    intro z w
    simpa [V, edist_dist, L, Matrix.toLin'_apply, dist_add_right] using L.lipschitz z w
  have hg : Continuous (fun s v => amount A i v u s) :=
    continuous_iff_continuousAt.mpr fun s => (amounts_solve_ode A i hu s).continuousAt
  apply ODE_solution_unique (a:=(0:ℝ)) (b:=t) hLip
      (hc.mono fun _ h => h.1) (fun s hs => hd s hs.1)
      hg.continuousOn (fun s _ => (amounts_solve_ode A i hu s).hasDerivWithinAt) _ (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
  funext v
  simp [h₀, amount_zero]

end Catenary
