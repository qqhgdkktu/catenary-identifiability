import GlobalCofactors
import GlobalSpectralBridge

/-! Zero-frequency gain from the endpoint measure of a reversed Jacobi realization.
The matrix assumptions identify its principal minors with the physical chain. -/
noncomputable section
open Matrix
open scoped BigOperators Matrix

namespace Catenary.GlobalGainPhi
open GlobalUpper GlobalCofactors GlobalSpectralBridge EndpointExterior

private theorem inv_zero {r : ℕ} (T : Matrix (Fin (r+1)) (Fin (r+1)) ℝ) :
    T⁻¹ 0 0 = (T.submatrix Fin.succ Fin.succ).det / T.det := by
  rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [div_eq_inv_mul]

private theorem compressed_endpoint {n d : ℕ} (h : d+1 ≤ n+1) :
    (embed h)ᵀ *ᵥ endpoint = Pi.single (0 : Fin (d+1)) 1 := by
  have he : @endpoint n = Pi.single 0 1 := by
    funext i
    simp [endpoint,Pi.single_apply,eq_comm]
  rw [he, Matrix.mulVec_single_one, Matrix.transpose_transpose]
  funext i
  by_cases hi : i = 0
  · subst i
    simp [embed,Pi.single_apply]
  · have hj : (0 : Fin (n+1)) ≠ Fin.castLE h i := by
      intro hh
      apply hi
      exact Fin.ext (congrArg (fun k : Fin (n+1) => k.val) hh.symm)
    simp [embed,Pi.single_apply,hi,hj,Ne.symm hi]

/-- Interior-leak DC gain. The four determinant hypotheses identify the
full matrix, its endpoint deletion, its principal tail, and the endpoint
deletion of that tail. The endpoint weights use Mathlib's eigenbasis. -/
theorem gain_div_dc_eq_phi {n d : ℕ} (ℓ : Chamber n) (θ : Params n) (hθ : Positive θ)
    (hd : ℓ.val + (d+1) = n) (T : Matrix (Chamber n) (Chamber n) ℝ) (hp : T.PosDef)
    (band : ∀ i j : Chamber n, j.val+1 < i.val → T i j = 0)
    (link : ∀ i j : Chamber n, i.val = j.val+1 → T i j ≠ 0)
    (hD : T.det = (Middle.full ℓ θ).eval 0)
    (hH : (T.submatrix Fin.succ Fin.succ).det = (Middle.prefix ℓ θ n).eval 0)
    (hR : (T.submatrix (Fin.castLEOrderEmb (show d+1 ≤ n+1 by omega))
          (Fin.castLEOrderEmb (show d+1 ≤ n+1 by omega))).det = (Middle.suffix ℓ θ ℓ.val).eval 0)
    (hC : ((T.submatrix (Fin.castLEOrderEmb (show d+1 ≤ n+1 by omega))
          (Fin.castLEOrderEmb (show d+1 ≤ n+1 by omega))).submatrix Fin.succ Fin.succ).det
          = (middlePolynomial ℓ ℓ (Fin.last n) θ).eval 0) :
    gain ℓ (Fin.last n) θ / (Middle.full ℓ θ).eval 0 =
      phi (d+1) hp.1.eigenvalues (fun i => (hp.1.eigenvectorUnitary.1 0 i)^2) := by
  have hw : d+1 ≤ n+1 := by omega
  have pos := hp.det_pos
  rw [hD] at pos
  rw [phi_principal_inverse T hp hw band link,compressed_endpoint,
    Matrix.mulVec_single_one, single_dotProduct,one_mul,Matrix.transpose_apply,
    inv_zero, inv_zero, hD, hH, hC, hR, gain_eq_cofactor_quotient ℓ θ hθ (by omega)]
  field_simp [pos.ne', (suffix_eval_pos ℓ ℓ θ hθ le_rfl).ne']
  ring_nf
  simp

/-- The empty-tail case needs only the full determinant and its endpoint deletion. -/
theorem terminal_gain_div_dc_eq_phi {n : ℕ} (θ : Params n)
    (T : Matrix (Chamber n) (Chamber n) ℝ) (hp : T.PosDef)
    (band : ∀ i j : Chamber n, j.val+1 < i.val → T i j = 0)
    (link : ∀ i j : Chamber n, i.val = j.val+1 → T i j ≠ 0)
    (hD : T.det = (Middle.full (Fin.last n) θ).eval 0)
    (hH : (T.submatrix Fin.succ Fin.succ).det = (Middle.prefix (Fin.last n) θ n).eval 0) :
    gain (Fin.last n) (Fin.last n) θ / (Middle.full (Fin.last n) θ).eval 0 =
      phi 0 hp.1.eigenvalues (fun i => (hp.1.eigenvectorUnitary.1 0 i)^2) := by
  rw [phi_principal_inverse T hp (Nat.zero_le _) band link,
    gain_eq_prefix_eval _ _ _ le_rfl, inv_zero,hD,hH]
  simp [dotProduct]

#print axioms gain_div_dc_eq_phi
#print axioms terminal_gain_div_dc_eq_phi
end Catenary.GlobalGainPhi
