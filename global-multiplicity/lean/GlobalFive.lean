import GlobalPhysical
import Chain.ResolventData
import Chain.ResolventFormula
import Chain.Four
import Mathlib.LinearAlgebra.Matrix.Block

/-! Exact regular five-compartment witnesses; inputs at 1, outputs at 3 and 5,
leak at 4. Coefficients of D and W are listed in ascending order. -/
namespace Catenary.GlobalFive
open scoped BigOperators
abbrev Rates (K : Type*) := Fin 9 → K
inductive Expr
  | lit (z : ℤ)
  | var (i : Fin 9)
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
def partialAt (j : Fin 9) : Expr → Expr
  | .lit _ => .lit 0
  | .var i => .lit (if i = j then 1 else 0)
  | .add a b => .add (partialAt j a) (partialAt j b)
  | .sub a b => .sub (partialAt j a) (partialAt j b)
  | .mul a b => .add (.mul a (partialAt j b)) (.mul b (partialAt j a))

theorem map_eval {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (x : Rates K) (e : Expr) : f (eval x e) = eval (fun j => f (x j)) e := by
  induction e <;> simp [eval, *]

noncomputable def polynomial : Expr → MvPolynomial (Fin 9) ℝ
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

theorem linear_basis (x : Rates ℝ) (j : Fin 9) (e : Expr) :
    linear x e (fun i => if i = j then 1 else 0) = eval x (partialAt j e) := by
  induction e with
  | lit z => simp [linear, eval, partialAt]
  | var i => by_cases h : i = j <;> simp [linear, eval, partialAt, h]
  | add a b ha hb => simp [linear, eval, partialAt, ha, hb]
  | sub a b ha hb => simp [linear, eval, partialAt, ha, hb]
  | mul a b ha hb => simp [linear, eval, partialAt, ha, hb, smul_eq_mul]
end Expr

/-- Coefficients obtained from consecutive leading principal continuants.
    The final two tail entries are the nonmonic coefficients of W. -/
def obs {K : Type*} [Add K] [Sub K] [Mul K] (x : Rates K) : Rates K :=
  let d₁ := x 0
  let d₂ := x 1 + x 4
  let d₃ := x 2 + x 5
  let d₄ := x 3 + x 6 + x 8
  let d₅ := x 7
  let b₁ := x 0 * x 4
  let b₂ := x 1 * x 5
  let b₃ := x 2 * x 6
  let b₄ := x 3 * x 7
  let A := d₁+d₂
  let B := d₁*d₂-b₁
  let C := A+d₃
  let D := B+d₃*A-b₂
  let E := d₃*B-b₂*d₁
  let F := C+d₄
  let G := D+d₄*C-b₃
  let H := E+d₄*D-b₃*A
  let I := d₄*E-b₃*B
  ![d₅*I-b₄*E, I+d₅*H-b₄*D, H+d₅*G-b₄*C, G+d₅*F-b₄, F+d₅,
    d₄*d₅-b₄, d₄+d₅, x 0*x 1, x 0*x 1*x 2*x 3]

def first : Rates ℚ := ![1,2,3,1,3,1,2,2,2]
def second : Rates ℚ := ![16/29,29/8,9/4,4/3,481/232,3/2,8/9,3,16/9]
def data : Rates ℚ := ![24,150,206,96,17,8,7,2,6]

theorem rational_witnesses :
    (∀ i, 0 < first i ∧ 0 < second i ∧ obs first i = data i ∧ obs second i = data i) ∧
    first 0 ≠ second 0 := by decide +kernel

theorem eval_obs {K : Type*} [CommRing K] (x : Rates K) (i : Fin 9) :
    Expr.eval x (obs Expr.var i) = obs x i := by
  fin_cases i <;> simp [obs,Expr.eval]

def jac {K : Type*} [CommRing K] (x : Rates K) : Matrix (Fin 9) (Fin 9) K :=
  fun i j => ((obs Expr.var i).partialAt j).eval x

noncomputable def differential (x : Rates ℝ) : Rates ℝ →L[ℝ] Rates ℝ :=
  ContinuousLinearMap.pi fun i => (obs Expr.var i).linear x

theorem strict_obs (x : Rates ℝ) : HasStrictFDerivAt obs (differential x) x := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  simpa only [eval_obs] using (obs Expr.var i).strict x

theorem det_derivative (x : Rates ℝ) : (fderiv ℝ obs x).det = (jac x).det := by
  change LinearMap.det (fderiv ℝ obs x).toLinearMap = _
  rw [(strict_obs x).hasFDerivAt.fderiv, ← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  exact (obs Expr.var i).linear_basis x j

/-- LU determinant certificate checked without expanding a concrete determinant. -/
private theorem det_of_certificate {n : ℕ} (S A L U : Matrix (Fin n) (Fin n) ℚ)
    (t : ℚ) (hlu : S*A = L*U) (hs : S.BlockTriangular id)
    (hl : L.BlockTriangular OrderDual.toDual) (hu : U.BlockTriangular id)
    (hS : (∏ i, S i i) = 1) (hP : (∏ i, L i i) * (∏ i, U i i) = t) : A.det = t := by
  have h := congrArg Matrix.det hlu
  simp only [Matrix.det_mul,Matrix.det_of_upperTriangular hs, Matrix.det_of_upperTriangular hu,
    Matrix.det_of_lowerTriangular _ hl, hS,one_mul,hP] at h
  exact h

private def firstA : Matrix (Fin 9) (Fin 9) ℚ :=
  !![24, 12, 8, 0, 0, 0, 0, 12, 12;
    66, 35, 34, 6, 20, 32, 12, 66, 54;
    50, 33, 36, 24, 30, 36, 20, 58, 44;
    13, 11, 11, 10, 11, 11, 9, 14, 12;
    1, 1, 1, 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 2, 4, 2;
    0, 0, 0, 1, 0, 0, 1, 1, 1;
    2, 1, 0, 0, 0, 0, 0, 0, 0;
    6, 3, 2, 6, 0, 0, 0, 0, 0]

private def firstS : Matrix (Fin 9) (Fin 9) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

private def firstL : Matrix (Fin 9) (Fin 9) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    11/4, 1, 0, 0, 0, 0, 0, 0, 0;
    25/12, 4, 1, 0, 0, 0, 0, 0, 0;
    13/24, 9/4, 61/86, 1, 0, 0, 0, 0, 0;
    1/24, 1/4, 7/86, 1/7, 1, 0, 0, 0, 0;
    0, 0, 0, -2/7, -3, 1, 0, 0, 0;
    0, 0, 0, -2/7, -3, 1, 1, 0, 0;
    1/12, 0, 1/43, 0, -25/3, 4/3, 2, 1, 0;
    1/4, 0, 0, -12/7, -18, 6, 9, 6, 1]

private def firstU : Matrix (Fin 9) (Fin 9) ℚ :=
  !![24, 12, 8, 0, 0, 0, 0, 12, 12;
    0, 2, 12, 6, 20, 32, 12, 33, 21;
    0, 0, -86/3, 0, -50, -92, -28, -99, -65;
    0, 0, 0, -7/2, 63/43, 183/43, 80/43, 597/172, 749/172;
    0, 0, 0, 0, -6/43, -36/301, 4/301, -113/602, -7/86;
    0, 0, 0, 0, 0, 6/7, 25/7, 38/7, 4;
    0, 0, 0, 0, 0, 0, -2, -4, -2;
    0, 0, 0, 0, 0, 0, 0, 1/2, -3/2;
    0, 0, 0, 0, 0, 0, 0, 0, 6]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem first_hm : jac first = firstA := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem first_hlu : firstS * firstA = firstL * firstU := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ, firstS, firstA, firstL, firstU, Matrix.cons_val', Matrix.cons_val_fin_one]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem first_hs : firstS.BlockTriangular id  := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact (by decide : ¬ _) hij)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem first_hl : firstL.BlockTriangular OrderDual.toDual  := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact (by decide : ¬ _) hij)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem first_hu : firstU.BlockTriangular id  := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact (by decide : ¬ _) hij)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem first_s : (∏ i, firstS i i) = 1 := by norm_num [Fin.prod_univ_succ, firstS, firstL, firstU, Matrix.cons_val',Matrix.cons_val_fin_one]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem first_p : (∏ i, firstL i i) * (∏ i, firstU i i) = 3456 := by norm_num [Fin.prod_univ_succ, firstS, firstL, firstU, Matrix.cons_val',Matrix.cons_val_fin_one]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem first_det : (jac first).det = 3456 :=
  (congrArg Matrix.det first_hm).trans
    (det_of_certificate firstS firstA firstL firstU (3456) first_hlu first_hs first_hl
      first_hu first_s first_p)

private def secondA : Matrix (Fin 9) (Fin 9) ℚ :=
  !![87/2, 192/29, 32/3, 0, 0, 0, 0, 8, 27/2;
    3291/32, 24, 410/9, 9/2, 24, 21, 285/16, 136/3, 129/2;
    2105/32, 3115/116, 1639/36, 20, 129/4, 211/8, 467/16, 134/3, 50;
    115/8, 1137/116, 445/36, 10, 43/4, 77/8, 43/4, 38/3, 13;
    1, 1, 1, 1, 1, 1, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 3, 8/3, 3;
    0, 0, 0, 1, 0, 0, 1, 1, 1;
    29/8, 16/29, 0, 0, 0, 0, 0, 0, 0;
    87/8, 48/29, 8/3, 9/2, 0, 0, 0, 0, 0]

private def secondS : Matrix (Fin 9) (Fin 9) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

private def secondL : Matrix (Fin 9) (Fin 9) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    1097/464, 1, 0, 0, 0, 0, 0, 0, 0;
    2105/1392, 1259/624, 1, 0, 0, 0, 0, 0, 0;
    115/348, 25613/28080, 38359/45945, 1, 0, 0, 0, 0, 0;
    2/87, 713/7020, 5176/45945, 252637/1184353, 1, 0, 0, 0, 0;
    0, 0, 0, -367560/1184353, -43/7, 1, 0, 0, 0;
    0, 0, 0, -367560/1184353, -43/7, 1, 1, 0, 0;
    1/12, 0, 78/1021, 613305/2368706, -293/56, -15/8, -9/4, 1, 0;
    1/4, 0, 0, -1654020/1184353, -387/14, 9/2, 6, 20/7, 1]

private def secondU : Matrix (Fin 9) (Fin 9) ℚ :=
  !![87/2, 192/29, 32/3, 0, 0, 0, 0, 8, 27/2;
    0, 7020/841, 5308/261, 9/2, 24, 21, 285/16, 4597/174, 30237/928;
    0, 0, -4084/351, 4543/416, -841/52, -3327/208, -22469/3328, -77635/3744, -240649/6656;
    0, 0, 0, -1184353/367560, 36163/15315, 702811/183780, 409303/2940480, 3569051/1102680, 52952339/5880960;
    0, 0, 0, 0, -141288/1184353, -173736/1184353, -1482873/18949648, -1575163/7106118, -17708529/37899296;
    0, 0, 0, 0, 0, 2/7, 57/16, 139/42, 879/224;
    0, 0, 0, 0, 0, 0, -3, -8/3, -3;
    0, 0, 0, 0, 0, 0, 0, -7/8, -81/32;
    0, 0, 0, 0, 0, 0, 0, 0, 27/7]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem second_hm : jac second = secondA := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem second_hlu : secondS * secondA = secondL * secondU := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ, secondS, secondA, secondL, secondU, Matrix.cons_val', Matrix.cons_val_fin_one]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem second_hs : secondS.BlockTriangular id  := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact (by decide : ¬ _) hij)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem second_hl : secondL.BlockTriangular OrderDual.toDual  := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact (by decide : ¬ _) hij)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem second_hu : secondU.BlockTriangular id  := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; exact (by decide : ¬ _) hij)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem second_s : (∏ i, secondS i i) = 1 := by norm_num [Fin.prod_univ_succ, secondS, secondL, secondU, Matrix.cons_val',Matrix.cons_val_fin_one]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem second_p : (∏ i, secondL i i) * (∏ i, secondU i i) = -4698 := by norm_num [Fin.prod_univ_succ, secondS, secondL, secondU, Matrix.cons_val',Matrix.cons_val_fin_one]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem second_det : (jac second).det = -4698 :=
  (congrArg Matrix.det second_hm).trans
    (det_of_certificate secondS secondA secondL secondU (-4698) second_hlu second_hs second_hl
      second_hu second_s second_p)


noncomputable def overReal (x : Rates ℚ) : Rates ℝ := fun i => (x i : ℝ)

theorem det_real (x : Rates ℚ) :
    (fderiv ℝ obs (overReal x)).det = ((jac x).det : ℝ) := by
  rw [det_derivative]
  let φ : ℚ →+* ℝ := Rat.castHom ℝ
  have hj : φ.mapMatrix (jac x) = jac (overReal x) := by
    ext i j
    exact Expr.map_eval φ x _
  rw [← hj, ← RingHom.map_det]
  rfl

theorem exact_real_derivatives :
    (fderiv ℝ obs (overReal first)).det = 3456 ∧
    (fderiv ℝ obs (overReal second)).det = -4698 := by
  rw [det_real, det_real, first_det, second_det]
  norm_num

theorem real_witnesses :
    (∀ i, 0 < overReal first i ∧ 0 < overReal second i) ∧
    overReal first ≠ overReal second ∧
    obs (overReal first) = obs (overReal second) := by
  have hw := rational_witnesses
  constructor
  · intro i
    unfold overReal
    exact ⟨by exact_mod_cast (hw.1 i).1, by exact_mod_cast (hw.1 i).2.1⟩
  constructor
  · intro h
    have h0 := congrFun h 0
    unfold overReal at h0
    exact hw.2 (by exact_mod_cast h0)
  · funext i
    have h := (hw.1 i).2.2.1.trans (hw.1 i).2.2.2.symm
    let φ := Rat.castHom ℝ
    calc
      obs (overReal first) i = φ (obs first i) := by
        rw [← eval_obs, ← eval_obs first i]
        exact (Expr.map_eval φ first _).symm
      _ = φ (obs second i) := congrArg φ h
      _ = obs (overReal second) i := by
        rw [← eval_obs, ← eval_obs (overReal second) i]
        exact Expr.map_eval φ second _

open Continuant

private noncomputable def sites5 (x : Rates ℝ) (s : ℝ) : List (PathSite ℝ) :=
  [⟨s+x 0,-x 4,-x 0⟩, ⟨s+x 4+x 1,-x 5,-x 1⟩,
   ⟨s+x 5+x 2,-x 6,-x 2⟩, ⟨s+x 6+x 3+x 8,-x 7,-x 3⟩, ⟨s+x 7,0,0⟩]

set_option maxHeartbeats 3000000 in
private theorem physical5 (x : Rates ℝ) (s : ℝ) :
    (physicalSites (m:=4) 3 x).map (shiftedSite s) = sites5 x s := by
  simp (config := {decide := true}) [physicalSites,sitesFrom,physicalSite,shiftedSite,
    generator, directedEdge, fwd, back, loss, Fin.sum_univ_four, sites5]
  repeat' constructor <;> first | rfl | (change s + x 6 + x 3 + x 8 = s + x 6 + x 8 + x 3; ring) | ring

private noncomputable def denOf (z : Rates ℝ) (s : ℝ) : ℝ :=
  z 0 + z 1*s + z 2*s^2 + z 3*s^3 + z 4*s^4 + s^5

private noncomputable def tailOf (z : Rates ℝ) (s : ℝ) : ℝ :=
  z 5 + z 6*s + s^2

set_option maxHeartbeats 3000000 in
theorem den_eq (x : Rates ℝ) (s : ℝ) : cont (sites5 x s) = denOf (obs x) s := by
  dsimp [cont,run,step,PathSite.weight,sites5,denOf,obs]
  ring

theorem tail_eq (x : Rates ℝ) (s : ℝ) : cont ((sites5 x s).drop 3) = tailOf (obs x) s := by
  dsimp [cont,run,step,PathSite.weight,sites5,tailOf,obs]
  ring

set_option maxHeartbeats 1000000 in
theorem transfer_formulas (x : Rates ℝ) (hx : Positive (m:=4) x) (s : ℝ)
    (hd : (s • (1 : Mat 4) - generator 3 x).det ≠ 0) :
    (s • (1 : Mat 4) - generator (m:=4) 3 x)⁻¹ 2 0 = obs x 7 * tailOf (obs x) s / denOf (obs x) s ∧
    (s • (1 : Mat 4) - generator (m:=4) 3 x)⁻¹ 4 0 = obs x 8 / denOf (obs x) s := by
  have h₃ := (physical_transfer_formula (m:=4) 3 0 2 x s hx (by decide) hd).1
  have h₅ := (physical_transfer_formula (m:=4) 3 0 4 x s hx (by decide) hd).1
  simp only [physical5] at h₃ h₅
  change _ = 1 * (directedProduct ((sites5 x s).take 2) * cont ((sites5 x s).drop 3)) / cont (sites5 x s) at h₃
  change _ = 1 * (directedProduct ((sites5 x s).take 4) * 1) / cont (sites5 x s) at h₅
  rw [den_eq,tail_eq] at h₃
  rw [den_eq] at h₅
  have hp : directedProduct ((sites5 x s).take 2) = obs x 7 := by simp [sites5,directedProduct,obs]
  have hq : directedProduct ((sites5 x s).take 4) = obs x 8 := by simp [sites5,directedProduct,obs]; ring
  simpa only [hp,hq,one_mul,mul_one] using And.intro h₃ h₅

theorem sameCurves_of_obs (x y : Rates ℝ) (hx : Positive (m:=4) x) (hy : Positive (m:=4) y)
    (he : obs x = obs y) : SameCurves (m:=4) 0 2 4 3 x y := by
  apply (sameCurves_iff_common_regular (m:=4) 0 2 4 3 x y).mpr
  intro s h1 h2
  have a := transfer_formulas x hx s h1
  have b := transfer_formulas y hy s h2
  rw [he] at a
  exact ⟨a.1.trans b.1.symm, a.2.trans b.2.symm⟩

theorem physical_pair : SameCurves (m:=4) 0 2 4 3 (overReal first) (overReal second) :=
  sameCurves_of_obs _ _ (fun i => (real_witnesses.1 i).1)
    (fun i => (real_witnesses.1 i).2) real_witnesses.2.2

#print axioms exact_real_derivatives
#print axioms physical_pair
open GlobalMultiplicity Polynomial EndpointExterior
open scoped Polynomial

/-- Coordinate identification with the chart used in the all-length statement. -/
theorem obs_eq_F : (obs (K := ℝ)) = F (m:=4) (by decide) 3 := by
  funext x i
  let z := obs x
  have hd : Middle.full (m:=4) 3 x =
      C (z 0) + C (z 1)*X + C (z 2)*X^2 + C (z 3)*X^3 + C (z 4)*X^4 + X^5 := by
    apply Polynomial.funext
    intro s
    rw [Middle.full, Obstruction.interval_eval, physical5, den_eq]
    simp [denOf,z]
  have hw : Middle.suffix (m:=4) 3 x 2 = C (z 5) + C (z 6)*X + X^2 := by
    apply Polynomial.funext
    intro s
    rw [Middle.suffix, Obstruction.interval_eval, List.map_drop, physical5, tail_eq]
    simp [tailOf,z]
  have hp : gain 3 (third (m:=4) (by decide)) x = z 7 := by
    simp (config := {decide := true}) [gain, third, physicalSites, sitesFrom, Obstruction.pathGain,physicalSite, fwd,z,obs]
  have hq : gain 3 (last 4) x = z 8 := by
    simp (config := {decide := true}) [gain, last, physicalSites, sitesFrom, Obstruction.pathGain,physicalSite, fwd,z,obs,mul_assoc]
    change x 0 * (x 1 * (x 2 * (x 3 * 1))) = _
    ring
  change z i = _
  fin_cases i <;> simp (config := {decide := true}) [F,hd,hw,hp,hq,
    coeff_C_mul_X_pow,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]

theorem five_seed : AtLeast (m:=4) (by decide) 3 2 := by
  let a := overReal first
  let b := overReal second
  refine ⟨obs a, ![a,b], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | exact (real_witnesses.2.1 hij).elim | exact (real_witnesses.2.1 hij.symm).elim
  · intro t
    rw [← obs_eq_F]
    fin_cases t
    · exact ⟨fun i => (real_witnesses.1 i).1, rfl, ne_of_eq_of_ne exact_real_derivatives.1 (by norm_num)⟩
    · exact ⟨fun i => (real_witnesses.1 i).2, real_witnesses.2.2.symm,
        ne_of_eq_of_ne exact_real_derivatives.2 (by norm_num)⟩
#print axioms five_seed
end Catenary.GlobalFive
