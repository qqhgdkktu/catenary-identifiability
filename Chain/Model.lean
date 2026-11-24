import Chain.Placement
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section
open scoped BigOperators Matrix Interval
namespace Catenary

/-- m edges, m+1 labelled chambers, 2m+1 unknown positive rates. -/
abbrev Params (m : ℕ) := Fin (2*m+1) → ℝ
abbrev Chamber (m : ℕ) := Fin (m+1)
abbrev Mat (m : ℕ) := Matrix (Chamber m) (Chamber m) ℝ

def fwd {m : ℕ} (r : Fin m) : Fin (2*m+1) := ⟨r, by omega⟩
def back {m : ℕ} (r : Fin m) : Fin (2*m+1) := ⟨m+r.val, by omega⟩
def loss (m : ℕ) : Fin (2*m+1) := ⟨2*m, by omega⟩

def directedEdge {m : ℕ} (src dst : Chamber m) : Mat m :=
  fun row col => if col = src then
    (if row = dst then 1 else 0) - (if row = src then 1 else 0) else 0

def generator {m : ℕ} (ℓ : Chamber m) (θ : Params m) : Mat m :=
  fun row col =>
    (∑ r : Fin m, (θ (fwd r) * directedEdge r.castSucc r.succ row col
      + θ (back r) * directedEdge r.succ r.castSucc row col))
    - (if row = ℓ ∧ col = ℓ then θ (loss m) else 0)

def Positive {m : ℕ} (θ : Params m) : Prop := ∀ p, 0 < θ p

/-- Impulse kernel and zero-state convolution for a known continuous input. -/
def kernel {m : ℕ} (A : Mat m) (i v : Chamber m) (t : ℝ) : ℝ :=
  NormedSpace.exp ℝ (t • A) v i

def amount {m : ℕ} (A : Mat m) (i v : Chamber m) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in (0:ℝ)..t, kernel A i v (t-τ) * u τ

def SameCurves {m : ℕ} (i j k ℓ : Chamber m) (θ η : Params m) : Prop :=
  ∀ u : ℝ → ℝ, Continuous u → ∀ t : ℝ, 0 ≤ t →
    (amount (generator ℓ θ) i j u t = amount (generator ℓ η) i j u t ∧
     amount (generator ℓ θ) i k u t = amount (generator ℓ η) i k u t)

/-- A polynomial witness must be nonzero at at least one positive point.
This rules out vacuous exceptional sets on the model's parameter domain. -/
def GenericLocalID {m : ℕ} (i j k ℓ : Chamber m) : Prop :=
  ∃ p : MvPolynomial (Fin (2*m+1)) ℝ,
    (∃ θ : Params m, Positive θ ∧ MvPolynomial.eval θ p ≠ 0) ∧
    ∀ θ : Params m, Positive θ → MvPolynomial.eval θ p ≠ 0 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ η : Params m,
        Positive η → dist η θ < ε → SameCurves i j k ℓ θ η → η = θ

/-- Full physical target. This defines a proposition and does not assert a proof. -/
def PhysicalClassification : Prop :=
  ∀ (m : ℕ) (_ : 2 ≤ m) (i j k ℓ : Chamber m), j < k →
    (GenericLocalID i j k ℓ ↔ placement (m+1) (i.val+1) (j.val+1) (k.val+1))

theorem amount_zero {m : ℕ} (A : Mat m) (i v : Chamber m) (u : ℝ → ℝ) :
    amount A i v u 0 = 0 := by simp [amount]

theorem directedEdge_columnSum {m : ℕ} (src dst col : Chamber m) :
    ∑ row, directedEdge src dst row col = 0 := by
  by_cases h : col = src
  · simp [directedEdge, h, Finset.sum_sub_distrib]
  · simp [directedEdge, h]

theorem generator_columnSum {m : ℕ} (ℓ col : Chamber m) (θ : Params m) :
    ∑ row, generator ℓ θ row col = -(if col = ℓ then θ (loss m) else 0) := by
  classical
  simp only [generator, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, directedEdge_columnSum,
    mul_zero, add_zero, Finset.sum_const_zero, zero_sub]
  by_cases h : col = ℓ <;> simp [h]

end Catenary
