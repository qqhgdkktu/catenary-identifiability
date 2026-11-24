import Chain.Model
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators Matrix
namespace Catenary
namespace Gauge

/-- Scaling of state coordinates by a positive diagonal matrix. -/
def scaled {m} (w : Chamber m → ℝ) (J : Mat m) : Mat m :=
  fun a b => w a * J a b / w b

theorem diagonal_similarity {m} (w : Chamber m → ℝ) (A : Mat m) :
    scaled w A = Matrix.diagonal w * A * Matrix.diagonal (fun p => (w p)⁻¹) := by
  ext r c
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  rfl

theorem reverse_edge_product {m} {w : Chamber m → ℝ} (hw : ∀ a, 0 < w a)
    {J : Mat m} (hs : J.IsSymm) (a b : Chamber m) :
    scaled w J a b * scaled w J b a = (J a b)^2 := by
  rw [scaled,scaled,hs.apply a b]
  field_simp [(hw a).ne', (hw b).ne']
  ring

theorem column_balance {m} {w : Chamber m → ℝ} {J : Mat m} (ℓ : Chamber m)
    (hs : J.IsSymm) (h : (-J).mulVec w = Pi.single ℓ 1) (r : Chamber m) :
    ∑ a, scaled w J a r = -(if r = ℓ then 1 / w ℓ else 0) := by
  have e := congrFun h r
  simp only [Matrix.mulVec, dotProduct, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib] at e
  have eq : (∑ a, w a * J a r) = ∑ a, J r a * w a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hs.apply r a,mul_comm]
  simp only [scaled,← Finset.sum_div,eq]
  by_cases hr : r = ℓ
  · subst r
    simp only [Pi.single_eq_same] at e
    have hv : (∑ a, J ℓ a * w a) = -1 := by linarith
    simp [hv,div_eq_mul_inv]
  · have hp : (Pi.single ℓ (1:ℝ) : Chamber m → ℝ) r = 0 := by simp [Pi.single_apply,hr,Ne.symm hr]
    rw [hp] at e
    have hv : (∑ a, J r a * w a) = 0 := by linarith
    simp [hv,hr]

theorem scaled_mul {m} {w : Chamber m → ℝ} (hw : ∀ a, w a ≠ 0) (A B : Mat m) :
    scaled w (A*B) = scaled w A * scaled w B := by
  ext r c
  simp only [scaled,Matrix.mul_apply,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  field_simp [hw]
  ring

theorem scaled_one {m} {w : Chamber m → ℝ} (hw : ∀ a, w a ≠ 0) :
    scaled w (1 : Mat m) = 1 := by
  ext r c
  by_cases h : r=c <;> simp [scaled,Matrix.one_apply,h,hw]

theorem scaled_pow {m} {w : Chamber m → ℝ} (hw : ∀ a, w a ≠ 0) (A : Mat m) (q : ℕ) :
    scaled w (A^q) = scaled w A ^ q := by
  induction q with
  | zero => simp [scaled_one hw]
  | succ q ih => simp [pow_succ,scaled_mul hw,ih]

end Gauge
end Catenary
