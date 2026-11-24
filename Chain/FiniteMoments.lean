import Chain.Dynamics
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.RingDivision

noncomputable section
open Polynomial
open scoped BigOperators Polynomial
namespace Catenary

private theorem entry_aeval_sum {m : ℕ} (A : Mat m) (i v : Chamber m) (p : ℝ[X]) :
    (aeval A p) v i = ∑ d ∈ p.support, p.coeff d * (A^d) v i := by
  conv_lhs => rw [p.as_sum_support]
  simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.sum_apply]

/-- A pair of n × n matrices is compared by at most 2n coefficients in each channel.
The shared annihilator is the product of their monic characteristic polynomials. -/
theorem markov_finite_iff {m : ℕ} (A B : Mat m) (i v : Chamber m) :
    (∀ q : ℕ, (A^q) v i = (B^q) v i) ↔
      ∀ q : ℕ, q < 2*(m+1) → (A^q) v i = (B^q) v i := by
  constructor
  · exact fun h q _ => h q
  intro h q
  let P := A.charpoly * B.charpoly
  have hmon : P.Monic := A.charpoly_monic.mul B.charpoly_monic
  have hA : aeval A P = 0 := by simp [P, Matrix.aeval_self_charpoly]
  have hB : aeval B P = 0 := by simp [P, Matrix.aeval_self_charpoly]
  let r := (X^q : ℝ[X]) %ₘ P
  have hrA : aeval A r = A^q := by simpa [r] using
    (aeval_modByMonic_eq_self_of_root (p:=(X^q : ℝ[X])) hmon hA)
  have hrB : aeval B r = B^q := by simpa [r] using
    (aeval_modByMonic_eq_self_of_root (p:=(X^q : ℝ[X])) hmon hB)
  have hdeg : P.degree = ↑(2*(m+1)) := by
    simp [P, degree_mul, Matrix.charpoly_degree_eq_dim, Chamber, two_mul]
  rw [← hrA, ← hrB, entry_aeval_sum, entry_aeval_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := (le_degree_of_ne_zero (mem_support_iff.mp hd)).trans_lt (degree_modByMonic_lt (X^q) hmon)
  rw [hdeg] at hd'
  exact congrArg ((r.coeff d) * ·) (h d (by exact_mod_cast hd'))

theorem sameCurves_iff_finite {m : ℕ} (i j k ℓ : Chamber m) (θ η : Params m) :
    SameCurves i j k ℓ θ η ↔
    ((∀ q : ℕ, q < 2*(m+1) → (generator ℓ θ ^ q) j i = (generator ℓ η ^ q) j i) ∧
     (∀ q : ℕ, q < 2*(m+1) → (generator ℓ θ ^ q) k i = (generator ℓ η ^ q) k i)) := by
  rw [sameCurves_iff_markov, markov_finite_iff, markov_finite_iff]

end Catenary
