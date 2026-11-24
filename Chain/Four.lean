import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Four compartments, one input at vertex 0, and outputs at vertices 2 and 3.
The seven coordinates are the three forward rates, the three backward rates,
and the leak rate, in that order. Vertex and parameter indices are zero-based.
-/
namespace Catenary.Four

open scoped BigOperators

abbrev Rates (K : Type*) := Fin 7 → K

/-- The four loss rates on the diagonal of the negative generator. -/
def diagonal {K : Type*} [Zero K] [Add K] (ℓ : Fin 4) (x : Rates K) (r : Fin 4) : K :=
  ![x 0, x 3 + x 1, x 4 + x 2, x 5] r + if r = ℓ then x 6 else 0

/-- The continuant of the four-compartment pencil, evaluated at frequency s. -/
def characteristic {K : Type*} [Zero K] [Add K] [Sub K] [Mul K]
    (ℓ : Fin 4) (x : Rates K) (s : K) : K :=
  let d := fun r => s + diagonal ℓ x r
  let l₂ := d 1 * d 0 - x 0 * x 3
  let l₃ := d 2 * l₂ - x 1 * x 4 * d 0
  d 3 * l₃ - x 2 * x 5 * l₂

/-- The explicit matrix sI-A in the column-sum compartment convention. -/
def pencil {K : Type*} [CommRing K] (ℓ : Fin 4) (x : Rates K) (s : K) :
    Matrix (Fin 4) (Fin 4) K :=
  let d := fun r => s + diagonal ℓ x r
  !![d 0, -x 3, 0, 0; -x 0, d 1, -x 4, 0; 0, -x 1, d 2, -x 5; 0, 0, -x 2, d 3]

theorem pencil_det {K : Type*} [CommRing K] (ℓ : Fin 4) (x : Rates K) (s : K) :
    (pencil ℓ x s).det = characteristic ℓ x s := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, pencil, characteristic,
    Fin.succAbove, Matrix.cons_val', Matrix.cons_val_fin_one]
  ring

/-- The signed minors of row 0 at columns 2 and 3 are transfer numerators. -/
def numerator {K : Type*} [CommRing K] (ℓ : Fin 4) (x : Rates K) (s : K) (v : Fin 4) : K :=
  (-1) ^ (v : ℕ) * ((pencil ℓ x s).submatrix Fin.succ v.succAbove).det

theorem numerator_eq_adjugate {K : Type*} [CommRing K]
    (ℓ : Fin 4) (x : Rates K) (s : K) (v : Fin 4) :
    numerator ℓ x s v = (pencil ℓ x s).adjugate v 0 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [numerator]

theorem transfer_at_regular_frequency (ℓ : Fin 4) (x : Rates ℝ) (s : ℝ) (v : Fin 4)
    (hs : characteristic ℓ x s ≠ 0) :
    pencil ℓ x s * (pencil ℓ x s)⁻¹ = 1 ∧
    (pencil ℓ x s)⁻¹ v 0 = numerator ℓ x s v / characteristic ℓ x s := by
  constructor
  · apply Matrix.mul_nonsing_inv
    exact isUnit_iff_ne_zero.mpr (by simpa only [pencil_det] using hs)
  · rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, ← numerator_eq_adjugate,
      pencil_det, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem numerator_third {K : Type*} [CommRing K] (ℓ : Fin 4) (x : Rates K) (s : K) :
    numerator ℓ x s 2 = x 0 * x 1 * (s + diagonal ℓ x 3) := by
  simp [numerator, Matrix.det_fin_three, Matrix.submatrix, pencil, Fin.succAbove,
    Matrix.cons_val', Matrix.cons_val_fin_one]

theorem numerator_fourth {K : Type*} [CommRing K] (ℓ : Fin 4) (x : Rates K) (s : K) :
    numerator ℓ x s 3 = x 0 * x 1 * x 2 := by
  simp [numerator, Matrix.det_fin_three, Matrix.submatrix, pencil, Fin.succAbove,
    Matrix.cons_val', Matrix.cons_val_fin_one, show ((3 : Fin 4) : ℕ) = 3 by rfl]
  ring

/-- Integral arithmetic expressions shared by the exact computation and real calculus. -/
inductive Expr
  | lit (z : ℤ)
  | var (i : Fin 7)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)

namespace Expr
instance : Zero Expr := ⟨.lit 0⟩
instance : Add Expr := ⟨.add⟩
instance : Sub Expr := ⟨.sub⟩
instance : Mul Expr := ⟨.mul⟩

def eval {K : Type*} [CommRing K] (x : Rates K) : Expr → K
  | .lit z => z
  | .var i => x i
  | .add a b => eval x a + eval x b
  | .sub a b => eval x a - eval x b
  | .mul a b => eval x a * eval x b

@[simp] theorem eval_zero {K : Type*} [CommRing K] (x : Rates K) : eval x 0 = 0 := by
  change ((0 : ℤ) : K) = 0
  simp

@[simp] theorem eval_add_op {K : Type*} [CommRing K] (x : Rates K) (a b : Expr) :
    eval x (a + b) = eval x a + eval x b := rfl
@[simp] theorem eval_sub_op {K : Type*} [CommRing K] (x : Rates K) (a b : Expr) :
    eval x (a - b) = eval x a - eval x b := rfl
@[simp] theorem eval_mul_op {K : Type*} [CommRing K] (x : Rates K) (a b : Expr) :
    eval x (a * b) = eval x a * eval x b := rfl

/-- Formal partial differentiation, with no numerical finite differences. -/
def partialAt (j : Fin 7) : Expr → Expr
  | .lit _ => .lit 0
  | .var i => .lit (if i = j then 1 else 0)
  | .add a b => .add (partialAt j a) (partialAt j b)
  | .sub a b => .sub (partialAt j a) (partialAt j b)
  | .mul a b => .add (.mul a (partialAt j b)) (.mul b (partialAt j a))

theorem map_eval {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (x : Rates K) (e : Expr) : f (eval x e) = eval (fun j => f (x j)) e := by
  induction e <;> simp [eval, *]

noncomputable def polynomial : Expr → MvPolynomial (Fin 7) ℝ
  | .lit z => MvPolynomial.C (z : ℝ)
  | .var j => MvPolynomial.X j
  | .add a b => polynomial a + polynomial b
  | .sub a b => polynomial a - polynomial b
  | .mul a b => polynomial a * polynomial b

theorem eval_polynomial (x : Rates ℝ) (e : Expr) :
    MvPolynomial.eval x e.polynomial = eval x e := by
  induction e <;> simp [polynomial, eval, *]

noncomputable def linear (x : Rates ℝ) : Expr → (Rates ℝ →L[ℝ] ℝ)
  | .lit _ => 0
  | .var i => ContinuousLinearMap.proj i
  | .add a b => linear x a + linear x b
  | .sub a b => linear x a - linear x b
  | .mul a b => eval x a • linear x b + eval x b • linear x a

theorem strict (x : Rates ℝ) (e : Expr) :
    HasStrictFDerivAt (fun y => eval y e) (linear x e) x := by
  induction e with
  | lit z => exact hasStrictFDerivAt_const _ _
  | var j => exact hasStrictFDerivAt_apply j x
  | add a b ha hb => exact ha.add hb
  | sub a b ha hb => exact ha.sub hb
  | mul a b ha hb => exact ha.mul hb

theorem linear_basis (x : Rates ℝ) (j : Fin 7) (e : Expr) :
    linear x e (fun i => if i = j then 1 else 0) = eval x (partialAt j e) := by
  induction e with
  | lit z => simp [linear, eval, partialAt]
  | var i => by_cases h : i = j <;> simp [linear, eval, partialAt, h]
  | add a b ha hb => simp [linear, eval, partialAt, ha, hb]
  | sub a b ha hb => simp [linear, eval, partialAt, ha, hb]
  | mul a b ha hb => simp [linear, eval, partialAt, ha, hb, smul_eq_mul]
end Expr

@[simp] theorem eval_diagonal {K : Type*} [CommRing K] (ℓ r : Fin 4) (x : Rates K) :
    Expr.eval x (diagonal ℓ Expr.var r) = diagonal ℓ x r := by
  fin_cases r <;> fin_cases ℓ <;> simp [diagonal, Expr.eval]

@[simp] theorem eval_characteristic {K : Type*} [CommRing K]
    (ℓ : Fin 4) (x : Rates K) (s : Expr) :
    Expr.eval x (characteristic ℓ Expr.var s) = characteristic ℓ x (Expr.eval x s) := by
  simp [characteristic, Expr.eval]

/-- The seven polynomials of the observable map, including the numerator gain. -/
def terms (ℓ : Fin 4) : Fin 7 → Expr :=
  let x := Expr.var
  let p := x 0 * x 1
  ![characteristic ℓ x (.lit 0), characteristic ℓ x (.lit 1),
    characteristic ℓ x (.lit 2), characteristic ℓ x (.lit 3),
    p, p * diagonal ℓ x 3, p * x 2]

noncomputable def F (ℓ : Fin 4) (x : Rates ℝ) : Rates ℝ := fun i => (terms ℓ i).eval x

theorem F_eq_observations (ℓ : Fin 4) (x : Rates ℝ) :
    F ℓ x = ![characteristic ℓ x 0, characteristic ℓ x 1,
      characteristic ℓ x 2, characteristic ℓ x 3, x 0 * x 1,
      x 0 * x 1 * diagonal ℓ x 3, x 0 * x 1 * x 2] := by
  funext i
  fin_cases i <;> simp [F, terms, Expr.eval]

theorem F_eq_determinants (ℓ : Fin 4) (x : Rates ℝ) :
    F ℓ x = ![(pencil ℓ x 0).det, (pencil ℓ x 1).det,
      (pencil ℓ x 2).det, (pencil ℓ x 3).det, x 0 * x 1,
      numerator ℓ x 0 2, numerator ℓ x 0 3] := by
  simp only [F_eq_observations, pencil_det, numerator_third, numerator_fourth, zero_add]

/-- The gain in coordinate 4 is the leading coefficient of the third-output
numerator, recovered from its values at 1 and 0. -/
theorem gain_eq_numerator_difference {K : Type*} [CommRing K] (ℓ : Fin 4) (x : Rates K) :
    x 0 * x 1 = numerator ℓ x 1 2 - numerator ℓ x 0 2 := by
  rw [numerator_third, numerator_third]
  ring

theorem F_eq_observed_pencil (ℓ : Fin 4) (x : Rates ℝ) :
    F ℓ x = ![(pencil ℓ x 0).det, (pencil ℓ x 1).det,
      (pencil ℓ x 2).det, (pencil ℓ x 3).det,
      numerator ℓ x 1 2 - numerator ℓ x 0 2, numerator ℓ x 0 2, numerator ℓ x 0 3] := by
  rw [F_eq_determinants, ← gain_eq_numerator_difference]

def jacobian {K : Type*} [CommRing K] (ℓ : Fin 4) (x : Rates K) : Matrix (Fin 7) (Fin 7) K :=
  fun i j => ((terms ℓ i).partialAt j).eval x

noncomputable def differential (ℓ : Fin 4) (x : Rates ℝ) : Rates ℝ →L[ℝ] Rates ℝ :=
  ContinuousLinearMap.pi fun i => (terms ℓ i).linear x

theorem hasStrictFDerivAt_F (ℓ : Fin 4) (x : Rates ℝ) :
    HasStrictFDerivAt (F ℓ) (differential ℓ x) x :=
  hasStrictFDerivAt_pi.mpr fun i => (terms ℓ i).strict x

theorem matrix_differential (ℓ : Fin 4) (x : Rates ℝ) :
    LinearMap.toMatrix' (differential ℓ x).toLinearMap = jacobian ℓ x := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  exact (terms ℓ i).linear_basis x j

noncomputable def exceptionPolynomial (ℓ : Fin 4) : MvPolynomial (Fin 7) ℝ :=
  Matrix.det (fun i j => ((terms ℓ i).partialAt j).polynomial)

theorem eval_exceptionPolynomial (ℓ : Fin 4) (x : Rates ℝ) :
    MvPolynomial.eval x (exceptionPolynomial ℓ) = (jacobian ℓ x).det := by
  unfold exceptionPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact Expr.eval_polynomial x _

def witnessZ : Rates ℤ := ![1, 2, 3, 4, 5, 6, 7]
noncomputable def witness : Rates ℝ := fun j => (witnessZ j : ℝ)

/-- Row expansion with shortcuts on zero entries. Its correctness is proved below. -/
def exactDet : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, _ => 1
  | n + 1, a => ∑ j : Fin (n + 1), if a 0 j = 0 then 0 else
      (-1) ^ (j : ℕ) * a 0 j * exactDet n (a.submatrix Fin.succ j.succAbove)

theorem exactDet_eq_det (n : ℕ) (a : Matrix (Fin n) (Fin n) ℤ) :
    exactDet n a = a.det := by
  induction n with
  | zero => simp [exactDet, Matrix.det_fin_zero]
  | succ n ih =>
    rw [exactDet, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : a 0 j = 0 <;> simp [h, ih]

def certificate : Fin 4 → ℤ := ![-311040, -198720, -103680, -51840]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem integer_certificates (ℓ : Fin 4) : (jacobian ℓ witnessZ).det = certificate ℓ := by
  rw [← exactDet_eq_det]
  fin_cases ℓ <;> decide

theorem witness_determinant (ℓ : Fin 4) : (jacobian ℓ witness).det = (certificate ℓ : ℝ) := by
  let f : ℤ →+* ℝ := Int.castRingHom ℝ
  have h : f.mapMatrix (jacobian ℓ witnessZ) = jacobian ℓ witness := by
    ext i j
    exact Expr.map_eval f witnessZ _
  rw [← h, ← RingHom.map_det, integer_certificates]
  rfl

theorem frechet_determinant_witness (ℓ : Fin 4) :
    (fderiv ℝ (F ℓ) witness).det = (certificate ℓ : ℝ) := by
  change LinearMap.det (fderiv ℝ (F ℓ) witness).toLinearMap = _
  rw [(hasStrictFDerivAt_F ℓ witness).hasFDerivAt.fderiv, ← LinearMap.det_toMatrix',
    matrix_differential, witness_determinant]

theorem witness_nonzero (ℓ : Fin 4) : MvPolynomial.eval witness (exceptionPolynomial ℓ) ≠ 0 := by
  rw [eval_exceptionPolynomial, witness_determinant]
  fin_cases ℓ <;> norm_num [certificate]

theorem exceptionPolynomial_ne_zero (ℓ : Fin 4) : exceptionPolynomial ℓ ≠ 0 := by
  intro h
  exact witness_nonzero ℓ (by simp [h])

theorem witness_positive (i : Fin 7) : 0 < witness i := by
  fin_cases i <;> norm_num [witness, witnessZ]

/-- Full local injectivity in the ambient real parameter space outside an explicit
proper algebraic exceptional set, for each of the four possible leak positions. -/
theorem locally_injective (ℓ : Fin 4) (x : Rates ℝ)
    (hx : MvPolynomial.eval x (exceptionPolynomial ℓ) ≠ 0) :
    ∃ U : Set (Rates ℝ), IsOpen U ∧ x ∈ U ∧ Set.InjOn (F ℓ) U := by
  classical
  have hd : (differential ℓ x).det ≠ 0 := by
    change LinearMap.det (differential ℓ x).toLinearMap ≠ 0
    rw [← LinearMap.det_toMatrix', matrix_differential, ← eval_exceptionPolynomial]
    exact hx
  let e := (differential ℓ x).toContinuousLinearEquivOfDetNeZero hd
  have hf : HasStrictFDerivAt (F ℓ) (e : Rates ℝ →L[ℝ] Rates ℝ) x := by
    simpa [e] using hasStrictFDerivAt_F ℓ x
  let g := hf.toPartialHomeomorph (F ℓ)
  exact ⟨g.source, g.open_source, hf.mem_toPartialHomeomorph_source, g.injOn⟩

end Catenary.Four
