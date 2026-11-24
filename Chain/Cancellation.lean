import Chain.Model
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open scoped Matrix
namespace Catenary.Cancellation

def rates : Params 2 := fun _ => 1

private def pencil (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![s+1,-1,0; -1,s+3,-1; 0,-1,s+1]

private theorem actual_pencil (s : ℝ) :
    s • (1 : Mat 2) - generator 1 rates = pencil s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [pencil,rates,generator,directedEdge,fwd,back,loss,
      Fin.sum_univ_two,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_three, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
  all_goals ring

theorem denominator (s : ℝ) :
    (s • (1 : Mat 2) - generator 1 rates).det = (s+1)*(s^2+4*s+1) := by
  rw [actual_pencil]
  change (pencil s).det = _
  rw [Matrix.det_fin_three]
  simp [pencil]
  ring

/-- At these strictly positive rates both channels cancel the pole candidate -1. -/
theorem both_cancel (s : ℝ) (hs : (s • (1 : Mat 2) - generator 1 rates).det ≠ 0) :
    (s • (1 : Mat 2) - generator 1 rates)⁻¹ 0 1 = 1 / (s^2+4*s+1) ∧
    (s • (1 : Mat 2) - generator 1 rates)⁻¹ 2 1 = 1 / (s^2+4*s+1) := by
  rw [denominator] at hs
  obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp hs
  rw [Matrix.inv_def,denominator,actual_pencil]
  change _ * _ = _ ∧ _ * _ = _
  rw [show (pencil s).adjugate = _ from Matrix.adjugate_fin_three_of (s+1) (-1) 0 (-1) (s+3) (-1) 0 (-1) (s+1)]
  simp [Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,Matrix.cons_val',Matrix.vecHead,Matrix.vecTail]
  field_simp [h₁,h₂]
  ring

theorem removed_root :
    ((-1:ℝ) • (1 : Mat 2) - generator 1 rates).det = 0 ∧
      ((-1:ℝ)^2+4*(-1)+1) = -2 ∧ Positive rates := by
  rw [denominator]
  norm_num [Positive,rates]

end Catenary.Cancellation
