import Chain.Dynamics
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Abel

/-! Exact equivalence of scalar Markov sequences and transfer entries
on any infinite set of common regular real frequencies. -/

noncomputable section
open Polynomial
open scoped Polynomial
namespace Catenary
namespace TransferData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def atValue (P : Matrix ι ι ℝ[X]) (s : ℝ) : Matrix ι ι ℝ :=
  (evalRingHom s).mapMatrix P

private theorem at_charmatrix (A : Matrix ι ι ℝ) (s : ℝ) :
    atValue A.charmatrix s = s • 1 - A := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [atValue, RingHom.mapMatrix_apply, Matrix.smul_apply]
  · simp [atValue, RingHom.mapMatrix_apply, Matrix.charmatrix_apply_ne _ _ _ h,
      Matrix.one_apply, Matrix.smul_apply, h]

theorem eval_charpoly_eq_det (A : Matrix ι ι ℝ) (s : ℝ) :
    A.charpoly.eval s = (s • 1 - A).det := by
  change (evalRingHom s) A.charmatrix.det = _
  rw [RingHom.map_det]
  exact congrArg Matrix.det (at_charmatrix A s)

private theorem entries_aeval_eq (A B : Matrix ι ι ℝ) (i v : ι)
    (h : ∀ q : Nat, (A^q) v i = (B^q) v i) (p : ℝ[X]) :
    (aeval A p) v i = (aeval B p) v i := by
  conv_lhs => rw [p.as_sum_support]
  conv_rhs => rw [p.as_sum_support]
  simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.sum_apply, h]

private theorem pencil_times_aeval (A : Matrix ι ι ℝ) (s : ℝ) (P Q : ℝ[X])
    (hP : aeval A P = 0) (hQ : P - C (P.eval s) = (X - C s) * Q) :
    (s • 1 - A) * aeval A Q = (P.eval s) • 1 := by
  have h := congrArg (aeval A) hQ
  simp only [map_sub, map_mul, aeval_X, aeval_C, hP,
    Algebra.algebraMap_eq_smul_one, zero_sub] at h
  rw [← neg_sub A (s • 1), neg_mul, ← h, neg_neg]

/-- Equality of every power entry gives equality of the two resolvents at
every real number where both pencils are invertible. -/
theorem resolvent_eq_of_markov (A B : Matrix ι ι ℝ) (i v : ι)
    (h : ∀ q : Nat, (A^q) v i = (B^q) v i) (s : ℝ)
    (ha : (s • 1 - A).det ≠ 0) (hb : (s • 1 - B).det ≠ 0) :
    (s • 1 - A)⁻¹ v i = (s • 1 - B)⁻¹ v i := by
  let P := A.charpoly * B.charpoly
  have haP : aeval A P = 0 := by simp [P, Matrix.aeval_self_charpoly]
  have hbP : aeval B P = 0 := by simp [P, Matrix.aeval_self_charpoly]
  have hn : P.eval s ≠ 0 := by simpa [P, eval_charpoly_eq_det] using mul_ne_zero ha hb
  obtain ⟨Q,hQ⟩ := X_sub_C_dvd_sub_C_eval (p := P) (a := s)
  have lift (M : Matrix ι ι ℝ) (hm : (s • 1 - M).det ≠ 0) (hpm : aeval M P = 0) :
      aeval M Q = P.eval s • (s • 1 - M)⁻¹ := by
    have eqn := congrArg (fun V => (s • 1 - M)⁻¹ * V) (pencil_times_aeval M s P Q hpm hQ)
    simpa only [← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hm), one_mul,
      mul_smul_comm, mul_one] using eqn
  have e := entries_aeval_eq A B i v h Q
  rw [lift A ha haP, lift B hb hbP] at e
  exact mul_left_cancel₀ hn e

private def numerator (P : Matrix ι ι ℝ[X]) (W : Matrix ι ι ℝ) (v i : ι) : ℝ[X] :=
  (P.adjugate * Polynomial.C.mapMatrix W) v i

private theorem numerator_eval (P : Matrix ι ι ℝ[X]) (W : Matrix ι ι ℝ) (v i : ι) (s : ℝ) :
    (numerator P W v i).eval s = ((atValue P s).adjugate * W) v i := by
  change ((evalRingHom s).mapMatrix (P.adjugate * Polynomial.C.mapMatrix W)) v i = _
  rw [map_mul, RingHom.map_adjugate]
  have hw : (evalRingHom s).mapMatrix (Polynomial.C.mapMatrix W) = W := by
    ext x y
    simp [RingHom.mapMatrix_apply]
  rw [hw]
  rfl

private theorem quotient_formula (P : Matrix ι ι ℝ[X]) (W : Matrix ι ι ℝ)
    (v i : ι) (s : ℝ) :
    ((atValue P s)⁻¹ * W) v i = (numerator P W v i).eval s / P.det.eval s := by
  have hd : P.det.eval s = (atValue P s).det := (evalRingHom s).map_det P
  rw [hd, numerator_eval, Matrix.inv_def, Ring.inverse_eq_inv, smul_mul_assoc]
  simp [Matrix.smul_apply, div_eq_inv_mul]

/-- On an infinite set of common regular points a rational matrix entry
determines its value at every other common regular point. -/
private theorem extend_equality (P Q : Matrix ι ι ℝ[X]) (U V : Matrix ι ι ℝ)
    (v i : ι) (S : Set ℝ) (hinf : S.Infinite)
    (hP : ∀ s ∈ S, (atValue P s).det ≠ 0) (hQ : ∀ s ∈ S, (atValue Q s).det ≠ 0)
    (h : ∀ s ∈ S, ((atValue P s)⁻¹ * U) v i = ((atValue Q s)⁻¹ * V) v i)
    (t : ℝ) (hPt : (atValue P t).det ≠ 0) (hQt : (atValue Q t).det ≠ 0) :
    ((atValue P t)⁻¹ * U) v i = ((atValue Q t)⁻¹ * V) v i := by
  have d (X : Matrix ι ι ℝ[X]) (s : ℝ) : X.det.eval s = (atValue X s).det :=
    (evalRingHom s).map_det X
  have eqpoly : numerator P U v i * Q.det = numerator Q V v i * P.det := by
    apply eq_of_infinite_eval_eq
    apply hinf.mono
    intro s hs
    change (numerator P U v i * Q.det).eval s = (numerator Q V v i * P.det).eval s
    simp only [eval_mul]
    have e := h s hs
    rw [quotient_formula, quotient_formula] at e
    exact (div_eq_div_iff (by rw [d]; exact hP s hs) (by rw [d]; exact hQ s hs)).mp e
  rw [quotient_formula, quotient_formula]
  apply (div_eq_div_iff (by rw [d]; exact hPt) (by rw [d]; exact hQt)).mpr
  simpa only [eval_mul] using congrArg (Polynomial.eval t) eqpoly

private def normalizedPencil (A : Matrix ι ι ℝ) : Matrix ι ι ℝ[X] :=
  fun i j => C ((1 : Matrix ι ι ℝ) i j) - X * C (A i j)

private theorem at_normalized (A : Matrix ι ι ℝ) (t : ℝ) :
    atValue (normalizedPencil A) t = 1 - t • A := by
  ext i j
  simp [atValue, normalizedPencil, RingHom.mapMatrix_apply, Matrix.smul_apply]
  exact mul_comm _ _

omit [Fintype ι] in
private theorem rescale_pencil (A : Matrix ι ι ℝ) (s : ℝ) (hs : s ≠ 0) :
    1 - s⁻¹ • A = s⁻¹ • (s • 1 - A) := by
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul]

private theorem rescale_inverse (A : Matrix ι ι ℝ) (s : ℝ) (hs : s ≠ 0)
    (hA : (s • 1 - A).det ≠ 0) :
    (1 - s⁻¹ • A)⁻¹ = s • (s • 1 - A)⁻¹ := by
  letI := invertibleOfNonzero (inv_ne_zero hs)
  rw [rescale_pencil A s hs, Matrix.inv_smul _ _ (isUnit_iff_ne_zero.mpr hA), invOf_eq_inv,
    inv_inv]

private theorem shift_normalized (A : Matrix ι ι ℝ) (v i : ι) (t : ℝ) (q : Nat)
    (hA : (1 - t • A).det ≠ 0) :
    t * (((1 - t • A)⁻¹ * A^(q+1)) v i) =
      (((1 - t • A)⁻¹ * A^q) v i) - (A^q) v i := by
  let R := (1 - t • A)⁻¹
  have hh : R * (1 - t • A) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)
  rw [mul_sub, mul_one, mul_smul_comm] at hh
  have hstep : t • (R*A) = R - 1 := by rw [← hh]; abel
  have hm : t • (R * A^(q+1)) = R * A^q - A^q := by
    rw [pow_succ', ← mul_assoc, ← smul_mul_assoc, hstep, sub_mul, one_mul]
  exact congrFun (congrFun hm v) i

/-- Any infinite set of common regular frequencies suffices to recover all
Markov parameters in one channel. The set need not have a finite accumulation point. -/
theorem markov_eq_of_resolvent_on_infinite (A B : Matrix ι ι ℝ) (i v : ι)
    (S : Set ℝ) (hS : S.Infinite)
    (ha : ∀ s ∈ S, (s • 1 - A).det ≠ 0) (hb : ∀ s ∈ S, (s • 1 - B).det ≠ 0)
    (he : ∀ s ∈ S, (s • 1 - A)⁻¹ v i = (s • 1 - B)⁻¹ v i) :
    ∀ q : Nat, (A^q) v i = (B^q) v i := by
  classical
  let T := (fun s : ℝ => s⁻¹) '' (S \ {0})
  have hT : T.Infinite := (hS.diff (Set.finite_singleton 0)).image inv_injective.injOn
  have nonzero (t : ℝ) (ht : t ∈ T) : t ≠ 0 := by
    obtain ⟨s,hs,rfl⟩ := ht
    exact inv_ne_zero (by simpa using hs.2)
  have reg (M : Matrix ι ι ℝ) (hM : ∀ s ∈ S, (s • 1 - M).det ≠ 0)
      (t : ℝ) (ht : t ∈ T) : (1 - t • M).det ≠ 0 := by
    obtain ⟨s,hs,rfl⟩ := ht
    have hs0 : s ≠ 0 := by simpa using hs.2
    rw [rescale_pencil M s hs0, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hs0)) (hM s hs.1)
  let Obs (q : Nat) := ∀ t ∈ T,
    (((1 - t • A)⁻¹ * A^q) v i) = (((1 - t • B)⁻¹ * B^q) v i)
  have zero : Obs 0 := by
    rintro _ ⟨s,hs,rfl⟩
    have hs0 : s ≠ 0 := by simpa using hs.2
    simp only [pow_zero, mul_one, rescale_inverse A s hs0 (ha s hs.1),
      rescale_inverse B s hs0 (hb s hs.1), Matrix.smul_apply, smul_eq_mul, he s hs.1]
  have recover (q : Nat) (h : Obs q) : (A^q) v i = (B^q) v i := by
    have z := extend_equality (normalizedPencil A) (normalizedPencil B) (A^q) (B^q) v i T hT
      (fun t ht => by simpa only [at_normalized] using reg A ha t ht)
      (fun t ht => by simpa only [at_normalized] using reg B hb t ht)
      (fun t ht => by simpa only [at_normalized] using h t ht) 0
      (by simp [at_normalized]) (by simp [at_normalized])
    simpa [at_normalized] using z
  have allObs : ∀ q, Obs q := by
    intro q
    induction q with
    | zero => exact zero
    | succ q ih =>
        intro t ht
        apply mul_left_cancel₀ (nonzero t ht)
        rw [shift_normalized A v i t q (reg A ha t ht), shift_normalized B v i t q (reg B hb t ht),
          ih t ht, recover q ih]
  exact fun q => recover q (allObs q)

theorem common_regular_infinite (A B : Matrix ι ι ℝ) :
    {s : ℝ | (s • 1 - A).det ≠ 0 ∧ (s • 1 - B).det ≠ 0}.Infinite := by
  have hn := mul_ne_zero A.charpoly_monic.ne_zero B.charpoly_monic.ne_zero
  apply (finite_setOf_isRoot hn).infinite_compl.mono
  intro s hs
  change (A.charpoly * B.charpoly).eval s ≠ 0 at hs
  simpa only [eval_mul, eval_charpoly_eq_det, mul_ne_zero_iff] using hs

end TransferData

/-- On each infinite set of frequencies regular for both physical generators,
equality of the two transfer channels is equivalent to all zero-state curves. -/
theorem sameCurves_iff_resolvent_on_infinite {m : ℕ} (i j k ℓ : Chamber m) (θ η : Params m)
    (S : Set ℝ) (hS : S.Infinite)
    (hθ : ∀ s ∈ S, (s • 1 - generator ℓ θ).det ≠ 0)
    (hη : ∀ s ∈ S, (s • 1 - generator ℓ η).det ≠ 0) :
    SameCurves i j k ℓ θ η ↔ ∀ s ∈ S,
      (s • 1 - generator ℓ θ)⁻¹ j i = (s • 1 - generator ℓ η)⁻¹ j i ∧
      (s • 1 - generator ℓ θ)⁻¹ k i = (s • 1 - generator ℓ η)⁻¹ k i := by
  rw [sameCurves_iff_markov]
  constructor
  · rintro ⟨hj,hk⟩ s hs
    exact ⟨TransferData.resolvent_eq_of_markov _ _ i j hj s (hθ s hs) (hη s hs),
      TransferData.resolvent_eq_of_markov _ _ i k hk s (hθ s hs) (hη s hs)⟩
  · intro h
    exact ⟨TransferData.markov_eq_of_resolvent_on_infinite _ _ i j S hS hθ hη
      (fun s hs => (h s hs).1), TransferData.markov_eq_of_resolvent_on_infinite _ _ i k S hS hθ hη
      (fun s hs => (h s hs).2)⟩

/-- The same physical equivalence with the entire common regular set. Its
infinitude follows from monicity of the two characteristic polynomials. -/
theorem sameCurves_iff_common_regular {m : ℕ} (i j k ℓ : Chamber m) (θ η : Params m) :
    SameCurves i j k ℓ θ η ↔ ∀ s : ℝ,
      (s • 1 - generator ℓ θ).det ≠ 0 → (s • 1 - generator ℓ η).det ≠ 0 →
      (s • 1 - generator ℓ θ)⁻¹ j i = (s • 1 - generator ℓ η)⁻¹ j i ∧
      (s • 1 - generator ℓ θ)⁻¹ k i = (s • 1 - generator ℓ η)⁻¹ k i := by
  have h := sameCurves_iff_resolvent_on_infinite i j k ℓ θ η _
    (TransferData.common_regular_infinite (generator ℓ θ) (generator ℓ η))
    (fun _ hs => hs.1) (fun _ hs => hs.2)
  constructor
  · exact fun e s hθ hη => h.mp e s ⟨hθ,hη⟩
  · exact fun e => h.mpr (fun s hs => e s hs.1 hs.2)

end Catenary
