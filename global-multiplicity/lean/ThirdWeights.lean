import Chain.FiniteMoments

/-! The two-pole uniqueness step of §3. All measures are finite, with real
weights. The hypotheses here are in the spectral coordinates of the paper. -/
noncomputable section
open scoped BigOperators

namespace Catenary.ThirdWeights

private def moment {n : ℕ} (w f : Fin n → ℝ) : ℝ := ∑ i, w i * f i

private theorem mix {n : ℕ} (w u v f : Fin n → ℝ) (a b c : ℝ) :
    moment (fun i => a*w i+b*u i+c*v i) f =
      a*moment w f+b*moment u f+c*moment v f := by
  unfold moment
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

private theorem shift {n : ℕ} (x w f : Fin n → ℝ) (k : ℝ)
    (h : ∀ i, x i ≠ k) :
    moment (fun i => w i / (x i-k)) (fun i => x i*f i) =
      moment w f + k*moment (fun i => w i / (x i-k)) f := by
  unfold moment
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [sub_ne_zero.mpr (h i)]
  ring

/-- For a shared quadratic denominator with simple poles c,e, the 0th and
1st orthogonality equations force the same normalized weights if the two
Cauchy sums are nonzero. The numerator of the competitor is any quadratic. -/
theorem quadratic_weight_uniqueness {n : ℕ} (x w v f : Fin n → ℝ)
    (c e k A B C : ℝ) (hce : c ≠ e) (hk : k ≠ 0)
    (hc : ∀ i, x i ≠ c) (he : ∀ i, x i ≠ e)
    (rel : ∀ i, v i = w i * (A*(x i)^2+B*x i+C) /
                         (k*(x i-c)*(x i-e)))
    (hw : ∑ i, w i = 1) (hv : ∑ i, v i = 1)
    (w0 : ∑ i, w i*f i = 0) (v0 : ∑ i, v i*f i = 0)
    (w1 : ∑ i, w i*(x i*f i) = 0) (v1 : ∑ i, v i*(x i*f i) = 0)
    (Ic : ∑ i, w i/(x i-c)*f i ≠ 0) (Ie : ∑ i, w i/(x i-e)*f i ≠ 0) :
    v = w := by
  let a := A/k
  let b := (A*c^2+B*c+C)/k/(c-e)
  let d := -(A*e^2+B*e+C)/k/(c-e)
  let wc := fun i => w i/(x i-c)
  let we := fun i => w i/(x i-e)
  have ha' : a*k = A := div_mul_cancel₀ _ hk
  have hb' : b*(c-e)*k = A*c^2+B*c+C := by
    dsimp only [b]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hce),div_mul_cancel₀ _ hk]
  have hd' : d*(c-e)*k = -(A*e^2+B*e+C) := by
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hce),div_mul_cancel₀ _ hk]
  have rep : v = fun i => a*w i+b*wc i+d*we i := by
    funext i
    rw [rel]
    let y := x i
    have wc' : wc i*(y-c) = w i := div_mul_cancel₀ _ (sub_ne_zero.mpr (hc i))
    have we' : we i*(y-e) = w i := div_mul_cancel₀ _ (sub_ne_zero.mpr (he i))
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero hk (sub_ne_zero.mpr (hc i)))
      (sub_ne_zero.mpr (he i)))).2
    change w i*(A*y^2+B*y+C) = (a*w i+b*wc i+d*we i)*(k*(y-c)*(y-e))
    apply mul_right_cancel₀ (sub_ne_zero.mpr hce)
    linear_combination (-w i*(y-c)*(y-e)*(c-e))*ha' - (w i*(y-e))*hb'
      - (w i*(y-c))*hd' - b*k*(y-e)*(c-e)*wc' - d*k*(y-c)*(c-e)*we'
  change moment w f = 0 at w0
  change moment v f = 0 at v0
  change moment w (fun i => x i*f i) = 0 at w1
  change moment v (fun i => x i*f i) = 0 at v1
  change moment wc f ≠ 0 at Ic
  change moment we f ≠ 0 at Ie
  rw [rep,mix,w0,mul_zero,zero_add] at v0
  rw [rep,mix,w1,mul_zero,zero_add,shift x w f c hc,shift x w f e he,w0,
    zero_add,zero_add] at v1
  change b*(c*moment wc f)+d*(e*moment we f) = 0 at v1
  have prodzero : (c-e)*(b*moment wc f) = 0 := by linear_combination v1 - e*v0
  have hb : b = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp prodzero).resolve_left
    (sub_ne_zero.mpr hce))).resolve_right Ic
  rw [hb,zero_mul,zero_add] at v0
  have hd : d = 0 := (mul_eq_zero.mp v0).resolve_right Ie
  simp only [hb,hd,zero_mul,add_zero] at rep
  rw [rep, ← Finset.mul_sum, hw,mul_one] at hv
  simpa only [hv,one_mul] using rep

#print axioms quadratic_weight_uniqueness
end Catenary.ThirdWeights
