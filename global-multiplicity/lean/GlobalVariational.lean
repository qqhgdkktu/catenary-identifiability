import GlobalLift
import GlobalUpper

noncomputable section
open Matrix Filter
open scoped Topology BigOperators Matrix
namespace Catenary.GlobalVariational
open GlobalUpper GlobalLift

/-- The unscaled least-squares quantity in the lifts is the same spectral infimum
as in the upper bound, including the empty residual basis m=0. -/
theorem phi_eq_gramValue {n m : ℕ} (hm : m ≤ n) {x w : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (hw : ∀ i, 0 < w i) (hd : Function.Injective x) :
    phi m x w = gramValue (fun i => w i / x i) (fun _ => 1)
      (fun i (j : Fin m) => x i ^ (j.val+1)) := by
  let v := fun i (j : Fin m) => x i ^ (j.val+1)
  let a := fun i => w i / x i
  have hg := monomial_gram_nonsingular hm a x (fun i => div_pos (hw i) (hx i))
    (fun i => (hx i).ne') hd
  have hl := gramValue_isLeast a (fun _ => 1) v (fun i => (div_pos (hw i) (hx i)).le) hg
  have eq (z : Fin m → ℝ) : energy x w z = lsEnergy a (fun _ => 1) v z := by
    apply Finset.sum_congr rfl
    intro i _
    have e : x i * ∑ j, z j * x i ^ j.val = v i ⬝ᵥ z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [v,pow_succ]
      ring
    simp only [GlobalUpper.residual,e,a]
    ring
  unfold phi
  simp_rw [eq]
  exact hl.csInf_eq

/-- Normalized lift B with the same infimum phi used for the level count. -/
theorem liftB_limit_phi {n m : ℕ} (hm : m ≤ n) {J : Type*} [Fintype J]
    (x a : Fin n → ℝ) (y : J → ℝ) (ε t p : ℝ) (hε : 0 < ε)
    (hx : ∀ i, 0 < x i) (ha : ∀ i, 0 < a i) (hd : Function.Injective x)
    (hs : 0 < ∑ i, a i) :
    Tendsto (liftBValue n m x a y ε t p) (𝓝 0)
      (𝓝 (((∑ i, a i) / ((∑ i, a i)+ε)) * phi m x (fun i => a i / ∑ j, a j))) := by
  have hw (i) := div_pos (ha i) hs
  rw [phi_eq_gramValue hm hx hw hd]
  apply liftB_explicit_limit n m x a y ε t p hε (fun i => (ha i).le) hx hs
  exact monomial_gram_nonsingular hm _ x (fun i => div_pos (hw i) (hx i))
    (fun i => (hx i).ne') hd

/-- If K is the invertible tail-coordinate matrix of the Krylov columns, the
    two moment identities identify phi with the inverse-tail correction. -/
theorem phi_tail_inverse {n m : ℕ} {x w : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    (hw : ∀ i, 0 ≤ w i) (K T : Matrix (Fin m) (Fin m) ℝ) (e : Fin m → ℝ)
    (hk : IsUnit K.det) (ht : IsUnit T.det)
    (hG : momentGram m x w = Kᵀ * T * K) (hb : (design m x)ᵀ *ᵥ w = Kᵀ *ᵥ e) :
    phi m x w = (∑ i, w i / x i) - (e ⬝ᵥ (T⁻¹ *ᵥ e)) := by
  let u := K⁻¹ *ᵥ (T⁻¹ *ᵥ e)
  have hku : K *ᵥ u = T⁻¹ *ᵥ e := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hk,Matrix.one_mulVec]
  have htu : T *ᵥ (T⁻¹ *ᵥ e) = e := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ ht,Matrix.one_mulVec]
  have hu : momentGram m x w *ᵥ u = (design m x)ᵀ *ᵥ w := by
    rw [hG,hb,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hku,htu]
  rw [phi_eq_moment_minimum hx hw u hu,hb,Matrix.mulVec_transpose,← Matrix.dotProduct_mulVec,hku]

end Catenary.GlobalVariational
