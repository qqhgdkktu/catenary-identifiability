import GlobalVariational
import GlobalKrylov

/-! Moment-to-tail bridge. Index 0 denotes the measured endpoint, and the first m
coordinates in this convention are the final m coordinates in the manuscript. -/
noncomputable section
open Matrix
open scoped BigOperators Matrix

namespace Catenary.GlobalSpectralBridge

open GlobalUpper GlobalKrylov GlobalVariational

variable {n m : ℕ}
local notation "N" => Fin (n+1)

def endpoint : N → ℝ := fun i => if i = 0 then 1 else 0

def cols (T : Matrix N N ℝ) (m : ℕ) : Matrix N (Fin m) ℝ :=
  fun i j => (T^j.val) i 0

def embed (hm : m ≤ n+1) : Matrix N (Fin m) ℝ :=
  fun i j => if i = (Fin.castLEOrderEmb hm) j then 1 else 0

theorem cols_eq_embed_mul (T : Matrix N N ℝ) (hm : m ≤ n+1)
    (band : ∀ i j : N, j.val+1 < i.val → T i j = 0) :
    cols T m = embed hm * krylovBlock T m hm := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < m
  · let k : Fin m := ⟨i.val,hi⟩
    have he : i = (Fin.castLEOrderEmb hm) k := Fin.ext rfl
    rw [Finset.sum_eq_single k]
    · simp [embed,he,cols,krylovBlock]
    · intro t _ ht
      have hne : i ≠ (Fin.castLEOrderEmb hm) t := fun h =>
        ht ((Fin.castLEOrderEmb hm).injective (h.symm.trans he))
      simp only [embed,if_neg hne,zero_mul]
    · simp
  · rw [show cols T m i j = 0 from endpoint_support T band j.val i (by have := j.isLt; omega)]
    symm
    apply Finset.sum_eq_zero
    intro t _
    have hne : i ≠ (Fin.castLEOrderEmb hm) t := by
      intro he
      apply hi
      rw [he]
      exact t.isLt
    simp only [embed,if_neg hne,zero_mul]

theorem moment_identities (T : Matrix N N ℝ) (x w : N → ℝ) (m : ℕ)
    (hs : Tᵀ = T) (hmom : ∀ k : ℕ, (T^k) 0 0 = ∑ i, w i * x i^k) :
    momentGram m x w = (cols T m)ᵀ * T * (cols T m) ∧
    (design m x)ᵀ *ᵥ w = (cols T m)ᵀ *ᵥ endpoint := by
  classical
  have hTc (i : N) (j : Fin m) :
      (T * cols T m) i j = (T^(j.val+1)) i 0 := by
    rw [pow_succ']
    rfl
  have hc (i : N) (j : Fin m) : cols T m i j = (T^j.val) 0 i := by
    have eq : (T^j.val)ᵀ = T^j.val := by rw [Matrix.transpose_pow,hs]
    exact congrArg (fun A : Matrix N N ℝ => A 0 i) eq
  constructor
  · ext i j
    have hR : ((cols T m)ᵀ * T * cols T m) i j = (T^(i.val+(j.val+1))) 0 0 := by
      rw [Matrix.mul_assoc,Matrix.mul_apply,pow_add, Matrix.mul_apply]
      simp only [Matrix.transpose_apply,hTc,hc]
    rw [hR,hmom]
    unfold momentGram
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Matrix.transpose_apply,Matrix.diagonal_mul,design,pow_add,pow_one]
    ring
  · funext j
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,endpoint]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change (∑ i, x i^j.val * w i) = (T^j.val) 0 0
    rw [hmom]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- An explicit orthogonal eigendecomposition supplies all endpoint moments. -/
theorem endpoint_moments_of_diagonalization (T Q : Matrix N N ℝ) (x : N → ℝ)
    (hr : Q * Qᵀ = 1) (hl : Qᵀ * Q = 1) (hT : T = Q * diagonal x * Qᵀ) (k : ℕ) :
    (T^k) 0 0 = ∑ i, (Q 0 i)^2 * x i^k := by
  classical
  have hp (a : ℕ) : T^a = Q * (diagonal x)^a * Qᵀ := by
    induction a with
    | zero => simp [hr]
    | succ a ih =>
      rw [pow_succ,ih,hT,pow_succ]
      calc
        (Q * diagonal x ^ a * Qᵀ) * (Q * diagonal x * Qᵀ)
            = Q * diagonal x ^ a * (Qᵀ * Q) * diagonal x * Qᵀ := by simp [Matrix.mul_assoc]
        _ = _ := by rw [hl,Matrix.mul_one, Matrix.mul_assoc Q]
  rw [hp,Matrix.diagonal_pow,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_diagonal,Matrix.transpose_apply, Pi.pow_apply]
  ring

/-- The compressed quadratic form is the actual principal block. -/
theorem compression_submatrix (T : Matrix N N ℝ) (hm : m ≤ n+1) :
    (embed hm)ᵀ * T * embed hm =
      T.submatrix (Fin.castLEOrderEmb hm) (Fin.castLEOrderEmb hm) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [embed,Matrix.transpose_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true, Matrix.mul_apply,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq,Matrix.submatrix_apply]

/-- Spectral variational minimum from an actual endpoint orthogonal diagonalization.
The subdiagonal and lower band hypotheses hold for an irreducible Jacobi matrix. -/
theorem phi_of_diagonalization (T Q : Matrix N N ℝ) (x : N → ℝ) (hm : m ≤ n+1)
    (hx : ∀ i, 0 < x i) (hr : Q * Qᵀ = 1) (hl : Qᵀ * Q = 1)
    (hT : T = Q * diagonal x * Qᵀ)
    (band : ∀ i j : N, j.val+1 < i.val → T i j = 0)
    (link : ∀ i j : N, i.val = j.val+1 → T i j ≠ 0)
    (ht : IsUnit (T.submatrix (Fin.castLEOrderEmb hm) (Fin.castLEOrderEmb hm)).det) :
    phi m x (fun i => (Q 0 i)^2) = (∑ i, (Q 0 i)^2 / x i) -
      (((embed hm)ᵀ *ᵥ endpoint) ⬝ᵥ
        ((T.submatrix (Fin.castLEOrderEmb hm) (Fin.castLEOrderEmb hm))⁻¹ *ᵥ
          ((embed hm)ᵀ *ᵥ endpoint))) := by
  have hs : Tᵀ = T := by rw [hT,Matrix.transpose_mul,Matrix.transpose_mul,
    Matrix.transpose_transpose,Matrix.diagonal_transpose,← Matrix.mul_assoc]
  obtain ⟨hG,hb⟩ := moment_identities T x (fun i => (Q 0 i)^2) m hs
    (endpoint_moments_of_diagonalization T Q x hr hl hT)
  apply phi_tail_inverse hx (fun i => sq_nonneg _) (krylovBlock T m hm)
    (T.submatrix (Fin.castLEOrderEmb hm) (Fin.castLEOrderEmb hm)) ((embed hm)ᵀ *ᵥ endpoint)
    (isUnit_iff_ne_zero.mpr (det_krylovBlock_ne_zero T band link hm)) ht
  · rw [hG,cols_eq_embed_mul T hm band,← compression_submatrix]
    simp [Matrix.transpose_mul,Matrix.mul_assoc]
  · rw [hb,cols_eq_embed_mul T hm band,Matrix.transpose_mul,Matrix.mulVec_mulVec]

/-- A coordinate inclusion is injective even when m=0. -/
theorem embed_injective (hm : m ≤ n+1) : Function.Injective (embed hm).mulVec := by
  classical
  have atRow (v : Fin m → ℝ) (i : Fin m) :
      ((embed hm) *ᵥ v) ((Fin.castLEOrderEmb hm) i) = v i := by
    simp [embed,Matrix.mulVec,dotProduct]
  intro a b h
  funext i
  rw [← atRow a i, ← atRow b i,h]

theorem compressed_det_unit (T : Matrix N N ℝ) (hm : m ≤ n+1) (hT : T.PosDef) :
    IsUnit (T.submatrix (Fin.castLEOrderEmb hm) (Fin.castLEOrderEmb hm)).det := by
  have h := hT.conjTranspose_mul_mul_same (embed_injective hm)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,compression_submatrix] at h
  exact isUnit_iff_ne_zero.mpr h.det_pos.ne'

theorem inverse_endpoint_of_diagonalization (T Q : Matrix N N ℝ) (x : N → ℝ)
    (hx : ∀ i, 0 < x i) (hr : Q * Qᵀ = 1) (hl : Qᵀ * Q = 1)
    (hT : T = Q * diagonal x * Qᵀ) :
    T⁻¹ 0 0 = ∑ i, (Q 0 i)^2 / x i := by
  classical
  let d := diagonal fun i => (x i)⁻¹
  have hd : diagonal x * d = 1 := by
    dsimp only [d]
    rw [Matrix.diagonal_mul_diagonal]
    convert (Matrix.diagonal_one : (diagonal (fun _ : N => (1 : ℝ))) = 1) using 1
    exact congrArg Matrix.diagonal (funext fun i => mul_inv_cancel₀ (hx i).ne')
  have eq : T⁻¹ = Q * d * Qᵀ := by
    apply Matrix.inv_eq_right_inv
    calc
      T * (Q * d * Qᵀ) = Q * diagonal x * (Qᵀ * Q) * d * Qᵀ := by rw [hT]; simp [Matrix.mul_assoc]
      _ = Q * (diagonal x * d) * Qᵀ := by rw [hl,Matrix.mul_one,Matrix.mul_assoc Q]
      _ = 1 := by rw [hd, Matrix.mul_one,hr]
  rw [eq,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (Q * d) 0 i = Q 0 i * (x i)⁻¹ from Matrix.mul_diagonal _ _ _ _, Matrix.transpose_apply,div_eq_mul_inv]
  ring

/-- The spectral minimum for the *actual* canonical endpoint measure of a
positive-definite Jacobi matrix is the full inverse entry minus its principal-tail
correction. No moment, diagonalization, Gram, or invertibility hypotheses remain. -/
theorem phi_principal_inverse (T : Matrix N N ℝ) (hp : T.PosDef) (hm : m ≤ n+1)
    (band : ∀ i j : N, j.val+1 < i.val → T i j = 0)
    (link : ∀ i j : N, i.val = j.val+1 → T i j ≠ 0) :
    phi m hp.1.eigenvalues (fun i => (hp.1.eigenvectorUnitary.1 0 i)^2) = T⁻¹ 0 0 -
      (((embed hm)ᵀ *ᵥ endpoint) ⬝ᵥ
        ((T.submatrix (Fin.castLEOrderEmb hm) (Fin.castLEOrderEmb hm))⁻¹ *ᵥ
          ((embed hm)ᵀ *ᵥ endpoint))) := by
  let Q := hp.1.eigenvectorUnitary.1
  let x := hp.1.eigenvalues
  have hr : Q * Qᵀ = 1 := by
    simpa only [Q,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
      using hp.1.eigenvectorUnitary.2.2
  have hl : Qᵀ * Q = 1 := by
    simpa only [Q,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
      using hp.1.eigenvectorUnitary.2.1
  have hT : T = Q * diagonal x * Qᵀ := by
    simpa only [x,Q,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id,Function.id_comp] using hp.1.spectral_theorem
  rw [inverse_endpoint_of_diagonalization T Q x hp.eigenvalues_pos hr hl hT]
  exact phi_of_diagonalization T Q x hm hp.eigenvalues_pos hr hl hT band link (compressed_det_unit T hm hp)

end Catenary.GlobalSpectralBridge
