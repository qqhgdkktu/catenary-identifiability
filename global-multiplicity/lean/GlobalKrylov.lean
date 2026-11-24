import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The endpoint is numbered 0, so coordinates with smaller indices correspond to
the tail of the chain in the manuscript. The proof needs only the lower bandwidth
condition and nonzero subdiagonal, both automatic for an irreducible Jacobi matrix. -/

namespace Catenary.GlobalKrylov

open scoped BigOperators Matrix

variable {n : ℕ} (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
variable (band : ∀ i j : Fin (n+1), j.val+1 < i.val → T i j = 0)
include band

/-- The kth endpoint Krylov column vanishes beyond row k. -/
theorem endpoint_support (k : ℕ) (i : Fin (n+1)) (hi : k < i.val) :
    (T^k) i 0 = 0 := by
  classical
  induction k generalizing i with
  | zero =>
    have hne : i ≠ 0 := by intro he; subst i; simp at hi
    simp [Matrix.one_apply, hne]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : k < j.val
    · rw [ih j hj, mul_zero]
    · rw [band i j (by omega), zero_mul]

variable (link : ∀ i j : Fin (n+1), i.val = j.val+1 → T i j ≠ 0)
include link

/-- Exactly at its last reachable row, a Krylov column is nonzero. -/
theorem endpoint_frontier (k : ℕ) (i : Fin (n+1)) (hi : i.val = k) :
    (T^k) i 0 ≠ 0 := by
  classical
  induction k generalizing i with
  | zero =>
    have he : i = 0 := Fin.ext hi
    simp [he]
  | succ k ih =>
    let j : Fin (n+1) := ⟨k, by omega⟩
    rw [pow_succ', Matrix.mul_apply, Finset.sum_eq_single j]
    · exact mul_ne_zero (link i j hi) (ih j rfl)
    · intro t _ ht
      by_cases hgt : k < t.val
      · rw [endpoint_support T band k t hgt, mul_zero]
      · have hne : t.val ≠ k := fun h => ht (Fin.ext h)
        rw [band i t (by omega), zero_mul]
    · simp

/-- Square matrix of the m Krylov columns restricted to their first m rows. -/
def krylovBlock (m : ℕ) (hm : m ≤ n+1) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (T^j.val) ((Fin.castLEOrderEmb hm) i) 0

/-- The restricted endpoint Krylov matrix is invertible, including the empty case. -/
theorem det_krylovBlock_ne_zero {m : ℕ} (hm : m ≤ n+1) :
    (krylovBlock T m hm).det ≠ 0 := by
  classical
  have htri : (krylovBlock T m hm).BlockTriangular id := by
    intro i j hij
    exact endpoint_support T band j.val ((Fin.castLEOrderEmb hm) i) hij
  rw [Matrix.det_of_upperTriangular htri]
  apply Finset.prod_ne_zero_iff.mpr
  exact fun i _ => endpoint_frontier T band link i.val ((Fin.castLEOrderEmb hm) i) rfl

/-- The linear combinations of e₀,T e₀,…,T^(m-1)e₀ are exactly the vectors
supported in the first m coordinates. Coordinate reversal gives the tail in §3. -/
theorem endpoint_krylov_iff_supported {m : ℕ} (hm : m ≤ n+1) (z : Fin (n+1) → ℝ) :
    (∃ c : Fin m → ℝ, ∀ i, z i = ∑ j, (T^j.val) i 0 * c j) ↔
    ∀ i : Fin (n+1), m ≤ i.val → z i = 0 := by
  classical
  constructor
  · rintro ⟨c, hc⟩ i hi
    rw [hc]
    apply Finset.sum_eq_zero
    intro j _
    rw [endpoint_support T band j.val i (lt_of_lt_of_le j.isLt hi), zero_mul]
  · intro hz
    let B := krylovBlock T m hm
    let y : Fin m → ℝ := fun i => z ((Fin.castLEOrderEmb hm) i)
    use B⁻¹ *ᵥ y
    intro i
    by_cases hlt : i.val < m
    · let r : Fin m := ⟨i.val,hlt⟩
      have hr : (Fin.castLEOrderEmb hm) r = i := Fin.ext rfl
      have hinv : B * B⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_krylovBlock_ne_zero T band link hm))
      have eq := congrFun (show B *ᵥ (B⁻¹ *ᵥ y) = y by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]) r
      change (∑ j, (T^j.val) ((Fin.castLEOrderEmb hm) r) 0 * (B⁻¹ *ᵥ y) j) =
        z ((Fin.castLEOrderEmb hm) r) at eq
      rw [hr] at eq
      exact eq.symm
    · rw [hz i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro j _
      rw [endpoint_support T band j.val i (by have := j.isLt; omega), zero_mul]

end Catenary.GlobalKrylov
