import Chain.FourCoefficients
import Chain.Model
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots

/-! Identification of the four-site polynomial pencil with the full user-facing generator. -/
namespace Catenary.Four

set_option maxHeartbeats 2000000 in
theorem pencil_eq_generator (ℓ : Chamber 3) (x : Params 3) (s : ℝ) :
    pencil ℓ x s = s • (1 : Mat 3) - generator ℓ x := by
  ext i j
  fin_cases ℓ <;> fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [pencil, diagonal, generator, directedEdge, fwd, back, loss,
      Fin.sum_univ_three, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_three, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] <;> ring

theorem characteristic_eq_generator_det (ℓ : Chamber 3) (x : Params 3) (s : ℝ) :
    characteristic ℓ x s = (s • (1 : Mat 3) - generator ℓ x).det := by
  rw [← pencil_eq_generator, pencil_det]

theorem eval_generator_charpoly (ℓ : Chamber 3) (x : Params 3) (s : ℝ) :
    (generator ℓ x).charpoly.eval s = characteristic ℓ x s := by
  rw [characteristic_eq_generator_det]
  change (Polynomial.evalRingHom s) (generator ℓ x).charmatrix.det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simp [RingHom.mapMatrix_apply, Matrix.smul_apply]
  · simp [RingHom.mapMatrix_apply, Matrix.charmatrix_apply_ne _ _ _ h,
      Matrix.smul_apply, Matrix.one_apply, h]

theorem generator_charpoly_eq (ℓ : Chamber 3) (x : Params 3) :
    (generator ℓ x).charpoly =
      Polynomial.X^4 + Polynomial.C (coefficients ℓ x 0) * Polynomial.X^3
      + Polynomial.C (coefficients ℓ x 1) * Polynomial.X^2
      + Polynomial.C (coefficients ℓ x 2) * Polynomial.X
      + Polynomial.C (coefficients ℓ x 3) := by
  apply Polynomial.funext
  intro s
  rw [eval_generator_charpoly, characteristic_eq_coefficients]
  simp

end Catenary.Four
