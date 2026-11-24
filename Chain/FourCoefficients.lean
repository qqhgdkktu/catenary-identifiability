import Chain.Four

/-! Independent certificates for the decreasing-power coefficient ordering. -/
namespace Catenary.Four

/-- Decreasing-degree coefficients c₃,c₂,c₁,c₀ of the monic continuant. -/
def coefficients {K : Type*} [Zero K] [Add K] [Sub K] [Mul K]
    (ℓ : Fin 4) (x : Rates K) : Fin 4 → K :=
  let d := diagonal ℓ x
  let b₁ := x 0 * x 3
  let b₂ := x 1 * x 4
  let b₃ := x 2 * x 5
  let u₁ := d 0 + d 1
  let u₀ := d 1 * d 0 - b₁
  let v₂ := u₁ + d 2
  let v₁ := u₀ + d 2 * u₁ - b₂
  let v₀ := d 2 * u₀ - b₂ * d 0
  ![v₂ + d 3, v₁ + d 3 * v₂ - b₃,
    v₀ + d 3 * v₁ - b₃ * u₁, d 3 * v₀ - b₃ * u₀]

@[simp] theorem eval_coefficients {K : Type*} [CommRing K]
    (ℓ : Fin 4) (x : Rates K) (j : Fin 4) :
    Expr.eval x (coefficients ℓ Expr.var j) = coefficients ℓ x j := by
  fin_cases j <;> simp [coefficients, Expr.eval]

theorem characteristic_eq_coefficients {K : Type*} [CommRing K]
    (ℓ : Fin 4) (x : Rates K) (s : K) :
    characteristic ℓ x s =
      s^4 + coefficients ℓ x 0 * s^3 + coefficients ℓ x 1 * s^2
        + coefficients ℓ x 2 * s + coefficients ℓ x 3 := by
  dsimp [coefficients, characteristic]
  ring

def coefficientTerms (ℓ : Fin 4) : Fin 7 → Expr :=
  let c := coefficients ℓ Expr.var
  ![c 0, c 1, c 2, c 3, terms ℓ 4, terms ℓ 5, terms ℓ 6]

noncomputable def Fc (ℓ : Fin 4) (x : Rates ℝ) : Rates ℝ :=
  fun i => (coefficientTerms ℓ i).eval x

theorem Fc_eq_observations (ℓ : Fin 4) (x : Rates ℝ) :
    Fc ℓ x = ![coefficients ℓ x 0, coefficients ℓ x 1, coefficients ℓ x 2,
      coefficients ℓ x 3, x 0 * x 1, x 0 * x 1 * diagonal ℓ x 3, x 0 * x 1 * x 2] := by
  funext i
  fin_cases i <;> simp [Fc, coefficientTerms, terms, Expr.eval]

/-- Replacing the descending monic-quartic coefficients by its samples. -/
def sampleCoefficients {K : Type*} [CommRing K] (c : Rates K) : Rates K :=
  let value := fun s : K => s^4 + c 0 * s^3 + c 1 * s^2 + c 2 * s + c 3
  ![value 0, value 1, value 2, value 3, c 4, c 5, c 6]

theorem F_eq_sampleCoefficients (ℓ : Fin 4) (x : Rates ℝ) :
    F ℓ x = sampleCoefficients (Fc ℓ x) := by
  rw [F_eq_observations, Fc_eq_observations]
  simp only [sampleCoefficients, characteristic_eq_coefficients]
  rfl

theorem locally_injective_Fc (ℓ : Fin 4) (x : Rates ℝ)
    (hx : MvPolynomial.eval x (exceptionPolynomial ℓ) ≠ 0) :
    ∃ U : Set (Rates ℝ), IsOpen U ∧ x ∈ U ∧ Set.InjOn (Fc ℓ) U := by
  obtain ⟨U, hopen, hmem, hinj⟩ := locally_injective ℓ x hx
  refine ⟨U, hopen, hmem, ?_⟩
  intro u hu v hv h
  apply hinj hu hv
  rw [F_eq_sampleCoefficients, F_eq_sampleCoefficients, h]

def coefficientJacobian {K : Type*} [CommRing K] (ℓ : Fin 4) (x : Rates K) :
    Matrix (Fin 7) (Fin 7) K := fun i j => ((coefficientTerms ℓ i).partialAt j).eval x

noncomputable def coefficientDifferential (ℓ : Fin 4) (x : Rates ℝ) : Rates ℝ →L[ℝ] Rates ℝ :=
  ContinuousLinearMap.pi fun i => (coefficientTerms ℓ i).linear x

theorem hasStrictFDerivAt_Fc (ℓ : Fin 4) (x : Rates ℝ) :
    HasStrictFDerivAt (Fc ℓ) (coefficientDifferential ℓ x) x :=
  hasStrictFDerivAt_pi.mpr fun i => (coefficientTerms ℓ i).strict x

theorem coefficientMatrix_differential (ℓ : Fin 4) (x : Rates ℝ) :
    LinearMap.toMatrix' (coefficientDifferential ℓ x).toLinearMap = coefficientJacobian ℓ x := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  exact (coefficientTerms ℓ i).linear_basis x j

def coefficientCertificate : Fin 4 → ℤ := ![-25920, -16560, -8640, -4320]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem integer_coefficient_certificates (ℓ : Fin 4) :
    (coefficientJacobian ℓ witnessZ).det = coefficientCertificate ℓ := by
  rw [← exactDet_eq_det]
  fin_cases ℓ <;> decide

theorem coefficient_witness_determinant (ℓ : Fin 4) :
    (coefficientJacobian ℓ witness).det = (coefficientCertificate ℓ : ℝ) := by
  let f : ℤ →+* ℝ := Int.castRingHom ℝ
  have h : f.mapMatrix (coefficientJacobian ℓ witnessZ) = coefficientJacobian ℓ witness := by
    ext i j
    exact Expr.map_eval f witnessZ _
  rw [← h, ← RingHom.map_det, integer_coefficient_certificates]
  rfl

theorem coefficient_frechet_determinant_witness (ℓ : Fin 4) :
    (fderiv ℝ (Fc ℓ) witness).det = (coefficientCertificate ℓ : ℝ) := by
  change LinearMap.det (fderiv ℝ (Fc ℓ) witness).toLinearMap = _
  rw [(hasStrictFDerivAt_Fc ℓ witness).hasFDerivAt.fderiv, ← LinearMap.det_toMatrix',
    coefficientMatrix_differential, coefficient_witness_determinant]

def evaluationVandermonde : Matrix (Fin 4) (Fin 4) ℤ := fun t j =>
  (t.val : ℤ) ^ (3 - j.val)

theorem evaluationVandermonde_det : evaluationVandermonde.det = 12 := by
  rw [← exactDet_eq_det]
  decide

theorem certificate_ratio (ℓ : Fin 4) :
    certificate ℓ = evaluationVandermonde.det * coefficientCertificate ℓ := by
  rw [evaluationVandermonde_det]
  fin_cases ℓ <;> decide

end Catenary.Four
