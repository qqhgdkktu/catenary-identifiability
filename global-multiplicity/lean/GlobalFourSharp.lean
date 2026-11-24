import GlobalFour
import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section
namespace Catenary.GlobalMultiplicity.FourAudit
open Polynomial EndpointExterior Continuant
open scoped Polynomial

abbrev obs := F (m:=3) (by decide) (1 : Chamber 3)

private theorem coords (x : X4) : obs x =
    ![Four.coefficients 1 x 3, Four.coefficients 1 x 2, Four.coefficients 1 x 1,
      Four.coefficients 1 x 0, x 5, p x, q x] := by
  have hfull : Middle.full 1 x = (generator 1 x).charpoly :=
    Polynomial.funext fun s => (full_eval 1 x s).trans (TransferData.eval_charpoly_eq_det _ _).symm
  have w : (Middle.suffix 1 x 2).coeff 0 = x 5 := by
    simp (config := {decide := true}) [Middle.suffix,physicalSites,sitesFrom,charpoly_eq_cont,
      cont,step,run,pencilSite,physicalSite,PathSite.weight,PhysicalInverse.diag_total,
      PhysicalInverse.a,PhysicalInverse.b,PhysicalInverse.prev,back]
    try ring
  have a : gain 1 (third (m:=3) (by decide)) x = p x := by
    simp (config := {decide := true}) [gain,third,physicalSites,sitesFrom,Obstruction.pathGain,
      physicalSite,p,fwd]
  have b : gain 1 (last 3) x = q x := by
    simp (config := {decide := true}) [gain,last,physicalSites,sitesFrom,Obstruction.pathGain,
      physicalSite,q,p,fwd,mul_assoc]
    change x 0 * (x 1 * (x 2 * 1)) = _
    ring
  funext i
  fin_cases i <;> simp (config := {decide := true}) [obs,F,hfull,Four.generator_charpoly_eq,
    coeff_C_mul_X_pow,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C,w,a,b]

def oldFrom (y : X4) : X4 := ![y 3,y 2,y 1,y 0,y 5,y 5*y 4,y 6]

theorem old_eq : Four.Fc 1 = oldFrom ∘ obs := by
  funext x
  simp [oldFrom,coords,Four.Fc_eq_observations,Four.diagonal,p,q]

private theorem diff_old (y : X4) : DifferentiableAt ℝ oldFrom y := by
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i <;> simp [oldFrom] <;> fun_prop

private theorem diff_obs (x : X4) : DifferentiableAt ℝ obs x := by
  have h : ∀ i : Fin 7, DifferentiableAt ℝ (fun u => Four.Fc 1 u i) x :=
    differentiableAt_pi.mp (Four.hasStrictFDerivAt_Fc 1 x).differentiableAt
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i <;> simp [coords]
  · simpa [Four.Fc_eq_observations] using h 3
  · simpa [Four.Fc_eq_observations] using h 2
  · simpa [Four.Fc_eq_observations] using h 1
  · simpa [Four.Fc_eq_observations] using h 0
  · fun_prop
  · simp [p]; fun_prop
  · simp [q,p]; fun_prop

private theorem regular (x : X4) (h : (fderiv ℝ (Four.Fc 1) x).det ≠ 0) :
    (fderiv ℝ obs x).det ≠ 0 := by
  intro hz
  rw [old_eq, fderiv_comp x (diff_old _) (diff_obs _)] at h
  exact h (by change LinearMap.det ((fderiv ℝ oldFrom (obs x)).toLinearMap.comp
                (fderiv ℝ obs x).toLinearMap) = 0
              rw [LinearMap.det_comp]
              change _ * (fderiv ℝ obs x).det = 0
              rw [hz,mul_zero])

/-- Full sharp maximum in the physical coefficient coordinates for four chambers, leak 2. -/
theorem sharp_four_leak_two : AtLeast (m:=3) (by decide) 1 2 ∧ ¬ AtLeast (m:=3) (by decide) 1 3 := by
  constructor
  · let x : Fin 2 → X4 := ![GlobalCounterexample.first,GlobalCounterexample.second]
    refine ⟨obs GlobalCounterexample.first,x,?_,?_⟩
    · intro i j e
      fin_cases i <;> fin_cases j <;> first | rfl | exact (GlobalCounterexample.distinct e).elim |
        exact (GlobalCounterexample.distinct e.symm).elim
    · intro t
      fin_cases t
      · exact ⟨GlobalCounterexample.positive.1,rfl,regular GlobalCounterexample.first (by rw [GlobalCounterexample.regular_derivatives.2.2.1]; norm_num)⟩
      · refine ⟨GlobalCounterexample.positive.2,?_,regular GlobalCounterexample.second (by rw [GlobalCounterexample.regular_derivatives.2.2.2]; norm_num)⟩
        exact ((data_iff_curves (by decide) 1 _ _ GlobalCounterexample.positive.1
          GlobalCounterexample.positive.2).2 GlobalCounterexample.same_curves).symm
  · rintro ⟨y,x,inj,h⟩
    have eqc (i j : Fin 3) : Four.Fc 1 (x i) = Four.Fc 1 (x j) := by
      rw [old_eq]
      exact congrArg oldFrom ((h i).2.1.trans (h j).2.1.symm)
    rcases no_three (x 0) (x 1) (x 2) (h 0).1 (h 1).1 (eqc 0 1) (eqc 0 2) with e|e|e
    all_goals have := inj e; omega

#print axioms sharp_four_leak_two
end Catenary.GlobalMultiplicity.FourAudit
