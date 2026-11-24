import Chain.FiniteMoments
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators Matrix
open MvPolynomial
namespace Catenary

abbrev IRate (m : ℕ) := Fin (2*m+1)
abbrev PRate (m : ℕ) := MvPolynomial (IRate m) ℝ

/-- The generator over the polynomial ring in the physical rates. -/
def universalGenerator {m : ℕ} (ℓ : Chamber m) : Matrix (Chamber m) (Chamber m) (PRate m) :=
  fun row col =>
    (∑ r : Fin m, (X (fwd r) * C (directedEdge r.castSucc r.succ row col)
      + X (back r) * C (directedEdge r.succ r.castSucc row col)))
    - (if row = ℓ ∧ col = ℓ then X (loss m) else 0)

theorem eval_universal_generator {m : ℕ} (ℓ : Chamber m) (θ : Params m) :
    (universalGenerator ℓ).map (eval θ) = generator ℓ θ := by
  ext r c
  by_cases h : r = ℓ ∧ c = ℓ <;> simp [universalGenerator, generator, Matrix.map_apply, h]

def observedPolynomial {m : ℕ} (i j k ℓ : Chamber m) (row : Bool × Fin (2*(m+1))) : PRate m :=
  (universalGenerator ℓ ^ row.2.val) (if row.1 then k else j) i

theorem eval_observedPolynomial {m : ℕ} (i j k ℓ : Chamber m) (θ : Params m)
    (row : Bool × Fin (2*(m+1))) :
    eval θ (observedPolynomial i j k ℓ row) =
       (generator ℓ θ ^ row.2.val) (if row.1 then k else j) i := by
  have h := congrArg (fun M : Mat m => M (if row.1 then k else j) i)
    (map_pow ((eval θ).mapMatrix) (universalGenerator ℓ) row.2.val)
  simpa only [observedPolynomial, RingHom.mapMatrix_apply, Matrix.map_apply,
    eval_universal_generator] using h

theorem polynomial_strict_jet {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (x : Fin d → ℝ) :
    ∃ L : (Fin d → ℝ) →L[ℝ] ℝ, HasStrictFDerivAt (fun y => eval y p) L x ∧
      ∀ j, L (Pi.single j 1) = eval x (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_, ?_⟩
    · simpa using (hasStrictFDerivAt_const (E := Fin d → ℝ) a x)
    · simp [pderiv_C]
  | add p q hp hq =>
    obtain ⟨L,hL,dL⟩ := hp
    obtain ⟨M,hM,dM⟩ := hq
    refine ⟨L+M, ?_, ?_⟩
    · simpa using hL.add hM
    · intro j; simp [dL, dM]
  | mul_X p i hp =>
    obtain ⟨L,hL,dL⟩ := hp
    have hX := hasStrictFDerivAt_apply i x (𝕜:=ℝ)
    refine ⟨(eval x p) • ContinuousLinearMap.proj i + (x i) • L, ?_, ?_⟩
    · simpa using hL.mul hX
    · intro j
      by_cases h : i = j <;> simp [pderiv_mul, Pi.single_apply, dL, h, smul_eq_mul, eq_comm]

/-- The determinant of an actual square minor of the polynomial Markov map. -/
def witnessPolynomial {m : ℕ} (i j k ℓ : Chamber m)
    (pick : IRate m → Bool × Fin (2*(m+1))) : PRate m :=
  Matrix.det (fun r c => pderiv c (observedPolynomial i j k ℓ (pick r)))

def polynomialValues {m : ℕ} {o : Type*} (P : o → PRate m) (x : Params m) : o → ℝ :=
  fun r => eval x (P r)

def polynomialJacobianDet {m : ℕ} (P : IRate m → PRate m) : PRate m :=
  Matrix.det (fun r c => pderiv c (P r))

/-- The determinant of the derivative is the evaluation of a fixed polynomial. -/
theorem square_polynomial_jet {m} (P : IRate m → PRate m) (x : Params m) :
    ∃ D : Params m →L[ℝ] Params m, HasStrictFDerivAt (polynomialValues P) D x ∧
      eval x (polynomialJacobianDet P) = D.det := by
  classical
  choose L hL hLbasis using fun r => polynomial_strict_jet (P r) x
  let D : Params m →L[ℝ] Params m := ContinuousLinearMap.pi L
  have hD : HasStrictFDerivAt (polynomialValues P) D x := hasStrictFDerivAt_pi.mpr hL
  refine ⟨D,hD,?_⟩
  have he : LinearMap.toMatrix' D.toLinearMap = fun r c => eval x (pderiv c (P r)) := by
    ext r c
    rw [LinearMap.toMatrix'_apply]
    change L r (fun j => if j = c then 1 else 0) = _
    rw [show (fun j : IRate m => if j = c then (1:ℝ) else 0) = Pi.single c 1 by
      funext j; by_cases h : j=c <;> simp [Pi.single_apply,h,Ne.symm,eq_comm]]
    exact hLbasis r c
  change _ = LinearMap.det D.toLinearMap
  rw [← LinearMap.det_toMatrix',he]
  simp only [polynomialJacobianDet,RingHom.map_det]
  rfl

/-- The observed polynomial functions may only be readable locally away from
a further exceptional polynomial q. The new exceptional set is still proper. -/
theorem genericLocalID_of_readable_polynomials {m} (i j k ℓ : Chamber m)
    (P : IRate m → PRate m) (q : PRate m) (x₀ : Params m) (hx₀ : Positive x₀)
    (hq : eval x₀ q ≠ 0) (h₀ : eval x₀ (polynomialJacobianDet P) ≠ 0)
    (hread : ∀ x : Params m, Positive x → eval x q ≠ 0 →
      ∃ e : ℝ, 0 < e ∧ ∀ y : Params m, Positive y → dist y x < e →
        SameCurves i j k ℓ x y → polynomialValues P x = polynomialValues P y) :
    GenericLocalID i j k ℓ := by
  classical
  refine ⟨q * polynomialJacobianDet P,⟨x₀,hx₀,by simpa using mul_ne_zero hq h₀⟩,?_⟩
  intro x hp hx
  rw [map_mul] at hx
  obtain ⟨hqx,hjx⟩ := mul_ne_zero_iff.mp hx
  obtain ⟨D,hD,hdet⟩ := square_polynomial_jet P x
  let e := D.toContinuousLinearEquivOfDetNeZero (hdet ▸ hjx)
  have hf : HasStrictFDerivAt (polynomialValues P) (e : Params m →L[ℝ] Params m) x := by
    simpa [e] using hD
  let g := hf.toPartialHomeomorph _
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp g.open_source x hf.mem_toPartialHomeomorph_source
  obtain ⟨ε',hε',hr⟩ := hread x hp hqx
  refine ⟨min ε ε',lt_min hε hε',?_⟩
  intro y hy hd H
  obtain ⟨he,hsmall⟩ := lt_min_iff.mp hd
  exact (g.injOn hf.mem_toPartialHomeomorph_source (hball he) (hr y hy hsmall H)).symm

/-- General sufficient condition from a single nonzero physical Jacobian minor.
The positional existence of this witness is a separate mathematical question. -/
theorem genericLocalID_of_witness {m : ℕ} (i j k ℓ : Chamber m)
    (pick : IRate m → Bool × Fin (2*(m+1))) (x₀ : Params m) (hx₀ : Positive x₀)
    (h₀ : eval x₀ (witnessPolynomial i j k ℓ pick) ≠ 0) : GenericLocalID i j k ℓ := by
  let P := fun r => observedPolynomial i j k ℓ (pick r)
  apply genericLocalID_of_readable_polynomials i j k ℓ P 1 x₀ hx₀ (by simp) h₀
  intro x _ _
  refine ⟨1,zero_lt_one,?_⟩
  intro y _ _ H
  have hm := (sameCurves_iff_markov i j k ℓ x y).mp H
  funext r
  simp only [polynomialValues,P,eval_observedPolynomial]
  split <;> first | apply hm.2 | apply hm.1

end Catenary

namespace Catenary

/-- The linear-algebra part of §2. If the image of a derivative factors
through the counted coefficient space, it cannot have full column rank
when the placement inequality fails. -/
theorem left_factor_not_injective {n i j k q : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hjk : j < k) (hk : k ≤ n)
    (bad : ¬ placement n i j k)
    (L : (Fin (2*n-1) → ℝ) →ₗ[ℝ] (Fin (n + (i-1) + (n-j) + (n-k) + 2) → ℝ))
    (R : (Fin (n + (i-1) + (n-j) + (n-k) + 2) → ℝ) →ₗ[ℝ] (Fin q → ℝ)) :
    ¬ Function.Injective (R.comp L) := by
  intro hinj
  have hLin : Function.Injective L := fun a b h => hinj (congrArg R h)
  have hdim := LinearMap.finrank_le_finrank_of_injective hLin
  simp only [Module.finrank_fin_fun] at hdim
  exact (not_le_of_gt ((left_deficit_iff hi hij hjk hk).mpr bad)) hdim

end Catenary
