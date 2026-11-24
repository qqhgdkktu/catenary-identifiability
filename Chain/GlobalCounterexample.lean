import Chain.FourPencil
import Chain.ResolventData

/-! Two positive regular points of the same four-chamber experiment:
inlet 1, outputs 3 and 4, leak at 2 in one-based notation. -/
noncomputable section

namespace Catenary.GlobalCounterexample

open Filter Set Topology

/-- All six directed rates are one; the leak rate is two. -/
def firstZ : Four.Rates ℤ := fun r => if r = 6 then 2 else 1

/-- The second backward rate is two; the five other directed rates and leak are one. -/
def secondZ : Four.Rates ℤ := fun r => if r = 4 then 2 else 1

private def overReal (x : Four.Rates ℤ) : Params 3 := fun i => (x i : ℝ)

def first : Params 3 := overReal firstZ
def second : Params 3 := overReal secondZ

theorem positive : Positive first ∧ Positive second := by
  constructor <;> intro i <;> simp only [first, second, overReal, firstZ, secondZ] <;>
    split <;> norm_num

theorem distinct : first ≠ second := by
  intro h
  have e := congrFun h (6 : Fin 7)
  norm_num (config := {decide := true}) [first, second, overReal, firstZ, secondZ] at e

/-- The actual unreduced denominator of both transfers. -/
def denominator (s : ℝ) : ℝ := s^4 + 8*s^3 + 18*s^2 + 12*s + 2

private theorem diagonal_rows (x : Params 3) :
    Four.diagonal 1 x 0 = x 0 ∧ Four.diagonal 1 x 1 = x 3 + x 1 + x 6 ∧
    Four.diagonal 1 x 2 = x 4 + x 2 ∧ Four.diagonal 1 x 3 = x 5 := by
  exact ⟨add_zero _, rfl, add_zero _, add_zero _⟩

theorem characteristics (s : ℝ) :
    Four.characteristic 1 first s = denominator s ∧
      Four.characteristic 1 second s = denominator s := by
  obtain ⟨a,b,c,d⟩ := diagonal_rows first
  obtain ⟨e,f,g,h⟩ := diagonal_rows second
  simp only [Four.characteristic, a,b,c,d,e,f,g,h]
  norm_num (config := {decide := true}) [first, second, overReal, firstZ, secondZ, denominator]
  constructor <;> ring

theorem numerators (s : ℝ) :
    Four.numerator 1 first s 2 = s + 1 ∧ Four.numerator 1 second s 2 = s + 1 ∧
    Four.numerator 1 first s 3 = 1 ∧ Four.numerator 1 second s 3 = 1 := by
  have d := (diagonal_rows first).2.2.2
  have h := (diagonal_rows second).2.2.2
  simp only [Four.numerator_third, Four.numerator_fourth, d,h]
  norm_num (config := {decide := true}) [first, second, overReal, firstZ, secondZ]

/-- The two solutions agree at both sensors for every continuous input and all t≥0. -/
theorem same_curves : SameCurves (m:=3) 0 2 3 1 first second := by
  apply (sameCurves_iff_common_regular 0 2 3 1 first second).mpr
  intro s hs hs'
  have a : Four.characteristic 1 first s ≠ 0 := by rwa [Four.characteristic_eq_generator_det]
  have b : Four.characteristic 1 second s ≠ 0 := by rwa [Four.characteristic_eq_generator_det]
  obtain ⟨c,d⟩ := characteristics s
  obtain ⟨e,f,g,h⟩ := numerators s
  rw [← Four.pencil_eq_generator 1 first s, ← Four.pencil_eq_generator 1 second s]
  rw [(Four.transfer_at_regular_frequency 1 first s 2 a).2,
      (Four.transfer_at_regular_frequency 1 second s 2 b).2,
      (Four.transfer_at_regular_frequency 1 first s 3 a).2,
      (Four.transfer_at_regular_frequency 1 second s 3 b).2, c,d,e,f,g,h]
  exact ⟨rfl,rfl⟩

theorem positive_global_counterexample :
    ∃ θ η : Params 3, Positive θ ∧ Positive η ∧ θ ≠ η ∧ SameCurves 0 2 3 1 θ η :=
  ⟨first, second, positive.1, positive.2, distinct, same_curves⟩

private theorem sampled_derivative (x : Four.Rates ℤ) :
    (fderiv ℝ (Four.F 1) (overReal x)).det = ((Four.jacobian 1 x).det : ℝ) := by
  let f : ℤ →+* ℝ := Int.castRingHom ℝ
  have h : f.mapMatrix (Four.jacobian 1 x) = Four.jacobian 1 (overReal x) := by
    ext i j
    exact Four.Expr.map_eval f x _
  change LinearMap.det (fderiv ℝ (Four.F 1) (overReal x)).toLinearMap = _
  rw [(Four.hasStrictFDerivAt_F _ _).hasFDerivAt.fderiv, ← LinearMap.det_toMatrix',
    Four.matrix_differential, ← h, ← RingHom.map_det]
  rfl

private theorem coefficient_derivative (x : Four.Rates ℤ) :
    (fderiv ℝ (Four.Fc 1) (overReal x)).det = ((Four.coefficientJacobian 1 x).det : ℝ) := by
  let f : ℤ →+* ℝ := Int.castRingHom ℝ
  have h : f.mapMatrix (Four.coefficientJacobian 1 x) = Four.coefficientJacobian 1 (overReal x) := by
    ext i j
    exact Four.Expr.map_eval f x _
  change LinearMap.det (fderiv ℝ (Four.Fc 1) (overReal x)).toLinearMap = _
  rw [(Four.hasStrictFDerivAt_Fc _ _).hasFDerivAt.fderiv, ← LinearMap.det_toMatrix',
    Four.coefficientMatrix_differential, ← h, ← RingHom.map_det]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem integer_determinants :
    (Four.jacobian 1 firstZ).det = 12 ∧ (Four.jacobian 1 secondZ).det = -24 ∧
    (Four.coefficientJacobian 1 firstZ).det = 1 ∧
    (Four.coefficientJacobian 1 secondZ).det = -2 := by
  repeat' apply And.intro
  all_goals rw [← Four.exactDet_eq_det]; decide

/-- Determinants of the true real Fréchet derivatives for both maps in both points. -/
theorem regular_derivatives :
    (fderiv ℝ (Four.F 1) first).det = 12 ∧ (fderiv ℝ (Four.F 1) second).det = -24 ∧
    (fderiv ℝ (Four.Fc 1) first).det = 1 ∧ (fderiv ℝ (Four.Fc 1) second).det = -2 := by
  obtain ⟨a,b,c,d⟩ := integer_determinants
  simp [first, second, sampled_derivative, coefficient_derivative, a,b,c,d]

/-- The seven monic-denominator and numerator coefficients determine the two
transfer functions for every real rate vector in this placement. -/
theorem same_curves_of_coefficient_data (ℓ : Chamber 3) (θ η : Params 3)
    (h : Four.Fc ℓ θ = Four.Fc ℓ η) : SameCurves 0 2 3 ℓ θ η := by
  rw [Four.Fc_eq_observations, Four.Fc_eq_observations] at h
  have hc : Four.coefficients ℓ θ = Four.coefficients ℓ η := by
    funext r
    fin_cases r <;> first | exact congrFun h 0 | exact congrFun h 1
                          | exact congrFun h 2 | exact congrFun h 3
  have gain : θ 0 * θ 1 = η 0 * η 1 := congrFun h 4
  have constant₃ : θ 0 * θ 1 * Four.diagonal ℓ θ 3 =
      η 0 * η 1 * Four.diagonal ℓ η 3 := congrFun h 5
  have constant₄ : θ 0 * θ 1 * θ 2 = η 0 * η 1 * η 2 := congrFun h 6
  apply (sameCurves_iff_common_regular 0 2 3 ℓ θ η).mpr
  intro s hs hs'
  have a : Four.characteristic ℓ θ s ≠ 0 := by rwa [Four.characteristic_eq_generator_det]
  have b : Four.characteristic ℓ η s ≠ 0 := by rwa [Four.characteristic_eq_generator_det]
  have den : Four.characteristic ℓ θ s = Four.characteristic ℓ η s := by
    simp only [Four.characteristic_eq_coefficients, hc]
  rw [← Four.pencil_eq_generator ℓ θ s, ← Four.pencil_eq_generator ℓ η s]
  rw [(Four.transfer_at_regular_frequency ℓ θ s 2 a).2,
      (Four.transfer_at_regular_frequency ℓ η s 2 b).2,
      (Four.transfer_at_regular_frequency ℓ θ s 3 a).2,
      (Four.transfer_at_regular_frequency ℓ η s 3 b).2]
  simp only [Four.numerator_third, Four.numerator_fourth, mul_add, den]
  rw [constant₃, constant₄, gain]
  exact ⟨rfl,rfl⟩

private theorem equal_coefficients : Four.Fc 1 first = Four.Fc 1 second := by
  rw [Four.Fc_eq_observations, Four.Fc_eq_observations]
  obtain ⟨a,b,c,d⟩ := diagonal_rows first
  obtain ⟨e,f,g,h⟩ := diagonal_rows second
  simp only [Four.coefficients, a,b,c,d,e,f,g,h]
  norm_num (config := {decide := true}) [first, second, overReal, firstZ, secondZ,
    Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.vecHead, Matrix.vecTail]

/-- An open neighborhood of the first positive vector consists entirely of
vectors admitting a distinct positive realization of the same two curves. -/
theorem open_positive_ambiguity :
    ∃ U : Set (Params 3), IsOpen U ∧ first ∈ U ∧
      ∀ θ ∈ U, Positive θ ∧ ∃ η : Params 3, Positive η ∧ θ ≠ η ∧ SameCurves 0 2 3 1 θ η := by
  classical
  obtain ⟨V,W,hV,hW,hfirst,hsecond,disjoint⟩ := t2_separation distinct
  have hp : IsOpen {x : Params 3 | Positive x} := by
    change IsOpen {x : Params 3 | ∀ p, (0 : ℝ) < x p}
    simp only [← Set.iInter_setOf]
    exact isOpen_iInter_of_finite fun p => isOpen_lt continuous_const (continuous_apply p)
  have hn : (Four.coefficientDifferential 1 second).det ≠ 0 := by
    rw [← (Four.hasStrictFDerivAt_Fc 1 second).hasFDerivAt.fderiv, regular_derivatives.2.2.2]
    norm_num
  let e := (Four.coefficientDifferential 1 second).toContinuousLinearEquivOfDetNeZero hn
  have hd : HasStrictFDerivAt (Four.Fc 1) (e : Params 3 →L[ℝ] Params 3) second := by
    simpa [e] using Four.hasStrictFDerivAt_Fc 1 second
  let Wpos := W ∩ {x : Params 3 | Positive x}
  have im : (Four.Fc 1) '' Wpos ∈ 𝓝 (Four.Fc 1 first) := by
    rw [equal_coefficients, ← hd.map_nhds_eq_of_equiv]
    exact image_mem_map ((hW.inter hp).mem_nhds ⟨hsecond,positive.2⟩)
  have near := (Four.hasStrictFDerivAt_Fc 1 first).continuousAt.preimage_mem_nhds im
  have both := inter_mem ((hV.inter hp).mem_nhds ⟨hfirst,positive.1⟩) near
  obtain ⟨U,sub,hU,mem⟩ := mem_nhds_iff.mp both
  refine ⟨U,hU,mem,?_⟩
  intro θ hθ
  obtain ⟨⟨θV,θpos⟩,η,⟨ηW,ηpos⟩,agree⟩ := sub hθ
  refine ⟨θpos,η,ηpos,?_,same_curves_of_coefficient_data 1 θ η agree.symm⟩
  intro same
  exact Set.disjoint_left.mp disjoint θV (same ▸ ηW)

end Catenary.GlobalCounterexample
