import GlobalUpper
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Two transverse crossings for the reciprocal endpoint-gain formula on a
positive affine slice. The endpoints may each lose a different spectral mass. -/

noncomputable section
open Set
open scoped BigOperators
namespace Catenary.ThirdExceptional

variable {ι : Type*} [Fintype ι]

/-- The reciprocal gain, up to a fixed positive scale. -/
def reciprocalSum (k w v : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, k i / (w i + t * v i)

private theorem reciprocal_jensen {a b X Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) (hX : 0<X) (hY : 0<Y) :
    1 / (a*X+b*Y) ≤ a / X + b / Y := by
  have hZ : 0 < a*X+b*Y := by
    by_cases h : a=0
    · subst a
      simp_all
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm h)) hX)
        (mul_nonneg hb hY.le)
  have eqn : a/X+b/Y-1/(a*X+b*Y) =
      a*b*(X-Y)^2/(X*Y*(a*X+b*Y)) := by
    field_simp [hX.ne', hY.ne', hZ.ne']
    rw [show b=1-a by linarith]
    ring
  have hpos := div_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (X-Y)))
    (mul_nonneg (mul_nonneg hX.le hY.le) hZ.le)
  linarith

theorem reciprocalSum_convexOn (k w v : ι → ℝ) {s : Set ℝ} (hs : Convex ℝ s)
    (hk : ∀ i, 0 ≤ k i) (hw : ∀ t ∈ s, ∀ i, 0 < w i+t*v i) :
    ConvexOn ℝ s (reciprocalSum k w v) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul, reciprocalSum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (reciprocal_jensen ha hb hab (hw x hx i) (hw y hy i)) (hk i)
  have he : w i+(a*x+b*y)*v i = a*(w i+x*v i)+b*(w i+y*v i) := by
    linear_combination -(w i)*hab
  rw [he]
  convert h using 1 <;> ring

private theorem diffAt (k w v : ι → ℝ) {t : ℝ} (hw : ∀ i, 0 < w i+t*v i) :
    DifferentiableAt ℝ (reciprocalSum k w v) t := by
  unfold reciprocalSum
  fun_prop (disch := exact (hw _).ne')

omit [Fintype ι] in
/-- Moving a small positive fraction of the way from a zero endpoint mass
to a positive interior mass makes its reciprocal contribution exceed a level. -/
private theorem near_endpoint {a b level : ℝ} (k w v : ι → ℝ) (j : ι)
    (hk : 0 < k j) (hb : 0 < w j+b*v j) (ha : w j+a*v j=0) (hq : 0<level) :
    ∃ u : ℝ, 0<u ∧ u<1 ∧ level < k j / (w j+((1-u)*a+u*b)*v j) := by
  have hpos := lt_min (show (0:ℝ)<1 by norm_num) (div_pos hk (mul_pos hq hb))
  obtain ⟨u, hu, hhalf⟩ := exists_between hpos
  have h1 := hhalf.trans_le (min_le_left _ _)
  have h2 := hhalf.trans_le (min_le_right _ _)
  refine ⟨u,hu,h1,?_⟩
  have he : w j+((1-u)*a+u*b)*v j=u*(w j+b*v j) := by
    linear_combination (1-u)*ha
  rw [he,lt_div_iff₀ (mul_pos hu hb)]
  have hmul := (lt_div_iff₀ (mul_pos hq hb)).mp h2
  linarith only [show level*(u*(w j+b*v j))=u*(level*(w j+b*v j)) by ring, hmul]

/-- For every level above an interior value, there is a crossing on either side,
with strictly negative and strictly positive derivatives respectively. -/
theorem two_transverse_crossings (k w v : ι → ℝ) {a b c level : ℝ}
    (hab : a<b) (hbc : b<c) (hk : ∀ i, 0<k i)
    (hw : ∀ t ∈ Ioo a c, ∀ i, 0<w i+t*v i)
    (ha : ∃ i, w i+a*v i=0) (hc : ∃ i, w i+c*v i=0)
    (hlevel : reciprocalSum k w v b < level) :
    ∃ x ∈ Ioo a b, ∃ y ∈ Ioo b c,
      reciprocalSum k w v x=level ∧ reciprocalSum k w v y=level ∧
      deriv (reciprocalSum k w v) x<0 ∧ 0<deriv (reciprocalSum k w v) y := by
  obtain ⟨j,hj⟩ := ha
  obtain ⟨l,hl⟩ := hc
  have hb : b ∈ Ioo a c := ⟨hab,hbc⟩
  have lower {t : ℝ} (ht : t ∈ Ioo a c) (i : ι) :
      k i/(w i+t*v i) ≤ reciprocalSum k w v t :=
    Finset.single_le_sum (f := fun z => k z/(w z+t*v z))
      (fun z _ => (div_pos (hk z) (hw t ht z)).le) (Finset.mem_univ i)
  have hq := ((div_pos (hk j) (hw b hb j)).trans_le (lower hb j)).trans hlevel
  obtain ⟨u,hu,hu1,hleft⟩ := near_endpoint k w v j (hk j) (hw b hb j) hj hq
  obtain ⟨z,hz,hz1,hright⟩ := near_endpoint k w v l (hk l) (hw b hb l) hl hq
  let A := (1-u)*a+u*b
  let C := (1-z)*c+z*b
  have haA : a<A := by dsimp [A]; nlinarith [mul_pos hu (sub_pos.mpr hab)]
  have hAb : A<b := by dsimp [A]; nlinarith [mul_pos (sub_pos.mpr hu1) (sub_pos.mpr hab)]
  have hbC : b<C := by dsimp [C]; nlinarith [mul_pos (sub_pos.mpr hz1) (sub_pos.mpr hbc)]
  have hCc : C<c := by dsimp [C]; nlinarith [mul_pos hz (sub_pos.mpr hbc)]
  have hs : Icc A C ⊆ Ioo a c := fun t ht => ⟨haA.trans_le ht.1,ht.2.trans_lt hCc⟩
  have hA := hleft.trans_le (lower ⟨haA,hAb.trans hbc⟩ j)
  have hC := hright.trans_le (lower ⟨hab.trans hbC,hCc⟩ l)
  have hd (t : ℝ) (ht : t ∈ Icc A C) := diffAt k w v (hw t (hs ht))
  have hconv := reciprocalSum_convexOn k w v (convex_Icc A C) (fun i => (hk i).le)
    (fun t ht => hw t (hs ht))
  obtain ⟨x,y,hx,hy,ex,ey,dx,dy⟩ := GlobalUpper.two_regular_of_peak
    (f := -(reciprocalSum k w v)) (q := -level) hAb hbC hconv.neg
    (fun t ht => (hd t ht).neg.continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1.le,ht.2.le⟩).neg)
    (neg_lt_neg hA) (neg_lt_neg hlevel) (neg_lt_neg hC)
  simp only [Pi.neg_apply,neg_inj] at ex ey
  change 0 < deriv (fun t => -reciprocalSum k w v t) x at dx
  change deriv (fun t => -reciprocalSum k w v t) y < 0 at dy
  rw [deriv.neg] at dx dy
  exact ⟨x,⟨haA.trans hx.1,hx.2⟩,y,⟨hy.1,hy.2.trans hCc⟩,ex,ey,by linarith,by linarith⟩

/-- The endpoint cofactor residue identity, the diagonal resolvent at zero,
and the physical first-leak formula imply the reciprocal sum for the gain. -/
theorem endpoint_gain_identity (x denominator left right : ι → ℝ) (D K R q : ℝ)
    (hx : ∀ i, x i ≠ 0) (hd : ∀ i, denominator i ≠ 0) (hr : ∀ i, right i ≠ 0)
    (hD : D ≠ 0) (hK : K ≠ 0)
    (hres : ∀ i, left i * right i = K / (denominator i)^2)
    (hdiag : R/D = ∑ i, left i / x i) (hq : q=K/R) :
    D/q = ∑ i, (D^2/(x i*(denominator i)^2))/right i := by
  calc
    D/q = (D^2/K)*(R/D) := by rw [hq]; field_simp; ring
    _ = (D^2/K)*(∑ i, left i/x i) := by rw [hdiag]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have he := (eq_div_iff (pow_ne_zero 2 (hd i))).mp (hres i)
      field_simp [hK,hx i,hd i,hr i]
      linear_combination (D^2*x i)*he

/-- The positive distal gain itself has equal values and opposite nonzero
derivatives at the two parameter values. -/
theorem two_gain_crossings (k w v : ι → ℝ) {a b c scale target : ℝ}
    (hab : a<b) (hbc : b<c) (hk : ∀ i, 0<k i)
    (hw : ∀ t ∈ Ioo a c, ∀ i, 0<w i+t*v i)
    (ha : ∃ i, w i+a*v i=0) (hc : ∃ i, w i+c*v i=0)
    (hs : 0<scale) (ht : 0<target) (hpeak : target < scale/reciprocalSum k w v b) :
    ∃ x ∈ Ioo a b, ∃ y ∈ Ioo b c,
      scale/reciprocalSum k w v x=target ∧ scale/reciprocalSum k w v y=target ∧
      0<deriv (fun t => scale/reciprocalSum k w v t) x ∧
      deriv (fun t => scale/reciprocalSum k w v t) y<0 := by
  let j := ha.choose
  have hb : b ∈ Ioo a c := ⟨hab,hbc⟩
  have hS (t : ℝ) (ht' : t ∈ Ioo a c) : 0<reciprocalSum k w v t :=
    (div_pos (hk j) (hw t ht' j)).trans_le (Finset.single_le_sum
      (f := fun z => k z/(w z+t*v z)) (fun z _ => (div_pos (hk z) (hw t ht' z)).le)
      (Finset.mem_univ j))
  have hlevel : reciprocalSum k w v b < scale/target := by
    rw [lt_div_iff₀ ht, mul_comm]
    exact (lt_div_iff₀ (hS b hb)).mp hpeak
  obtain ⟨x,hx,y,hy,ex,ey,dx,dy⟩ := two_transverse_crossings k w v hab hbc hk hw ha hc hlevel
  have xs : x ∈ Ioo a c := ⟨hx.1,hx.2.trans hbc⟩
  have ys : y ∈ Ioo a c := ⟨hab.trans hy.1,hy.2⟩
  have gain (t : ℝ) (he : reciprocalSum k w v t = scale/target) :
      scale/reciprocalSum k w v t=target := by rw [he]; field_simp
  have derivative (t : ℝ) (hm : t ∈ Ioo a c) :
      deriv (fun z => scale/reciprocalSum k w v z) t =
        -(scale*deriv (reciprocalSum k w v) t)/(reciprocalSum k w v t)^2 := by
    simpa using ((hasDerivAt_const t scale).div
      (diffAt k w v (hw t hm)).hasDerivAt (hS t hm).ne').deriv
  refine ⟨x,hx,y,hy,gain x ex,gain y ey,?_,?_⟩
  · rw [derivative x xs]
    exact div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hs dx)) (sq_pos_of_pos (hS x xs))
  · rw [derivative y ys]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (mul_pos hs dy)) (sq_pos_of_pos (hS y ys))

/-- A nonconstant, mass-preserving perturbation of positive finite weights
has a bounded interval of positivity with a zero mass at each endpoint. -/
theorem affine_weight_endpoints (w v : ι → ℝ) (hw : ∀ i, 0<w i)
    (hsum : ∑ i, v i = 0) (hmove : ∃ i, v i ≠ 0) :
    ∃ a c : ℝ, a<0 ∧ 0<c ∧
      (∀ t ∈ Ioo a c, ∀ i, 0<w i+t*v i) ∧
      (∃ i, w i+a*v i=0) ∧ (∃ i, w i+c*v i=0) := by
  classical
  obtain ⟨j,hj⟩ := hmove
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨j,Finset.mem_univ _⟩
  have hp : ∃ i, 0<v i := by
    by_contra! hn
    have h := Finset.sum_neg' (s := (Finset.univ : Finset ι))
      (fun i _ => hn i) ⟨j,Finset.mem_univ _,lt_of_le_of_ne (hn j) hj⟩
    linarith
  have hn : ∃ i, v i<0 := by
    by_contra! hp'
    have h := Finset.sum_pos' (s := (Finset.univ : Finset ι))
      (fun i _ => hp' i) ⟨j,Finset.mem_univ _,lt_of_le_of_ne (hp' j) hj.symm⟩
    linarith
  obtain ⟨p,hp⟩ := hp
  obtain ⟨n,hn⟩ := hn
  let m (i : ι) := v i / w i
  obtain ⟨P,_,hP⟩ := Finset.exists_max_image Finset.univ m hne
  obtain ⟨N,_,hN⟩ := Finset.exists_min_image Finset.univ m hne
  have hpos : 0<m P := (div_pos hp (hw p)).trans_le (hP p (Finset.mem_univ _))
  have hneg : m N<0 := (hN n (Finset.mem_univ _)).trans_lt (div_neg_of_neg_of_pos hn (hw n))
  let a := -(1/m P)
  let c := -(1/m N)
  have ha : a<0 := neg_lt_zero.mpr (div_pos one_pos hpos)
  have hc : 0<c := neg_pos.mpr (div_neg_of_pos_of_neg one_pos hneg)
  have eP : 1+a*m P=0 := by dsimp [a]; field_simp
  have eN : 1+c*m N=0 := by dsimp [c]; field_simp [hneg.ne]
  have fac (t : ℝ) (i : ι) : w i+t*v i=w i*(1+t*m i) := by
    dsimp [m]; field_simp [(hw i).ne']
  refine ⟨a,c,ha,hc,?_,⟨P,?_⟩,⟨N,?_⟩⟩
  · intro t ht i
    rw [fac]
    apply mul_pos (hw i)
    by_cases ht0 : 0≤t
    · have h1 := mul_lt_mul_of_neg_right ht.2 hneg
      have h2 := mul_le_mul_of_nonneg_left (hN i (Finset.mem_univ _)) ht0
      linarith
    · have h1 := mul_lt_mul_of_pos_right ht.1 hpos
      have h2 := mul_le_mul_of_nonpos_left (hP i (Finset.mem_univ _)) (le_of_not_ge ht0)
      linarith
  · rw [fac,eP,mul_zero]
  · rw [fac,eN,mul_zero]

/-- No endpoints or witnesses to a peak are inputs: every positive level below
the gain at the original measure is attained on both sides of that measure. -/
theorem normalized_slice_two_gains (k w v : ι → ℝ) {scale target : ℝ}
    (hk : ∀ i, 0<k i) (hw : ∀ i, 0<w i)
    (hsum : ∑ i, v i=0) (hmove : ∃ i, v i≠0)
    (hs : 0<scale) (ht : 0<target) (hpeak : target < scale/reciprocalSum k w v 0) :
    ∃ x y : ℝ, x<0 ∧ 0<y ∧
      (∀ i, 0<w i+x*v i) ∧ (∀ i, 0<w i+y*v i) ∧
      scale/reciprocalSum k w v x=target ∧ scale/reciprocalSum k w v y=target ∧
      0<deriv (fun t => scale/reciprocalSum k w v t) x ∧
      deriv (fun t => scale/reciprocalSum k w v t) y<0 := by
  obtain ⟨a,c,ha,hc,hw',hA,hC⟩ := affine_weight_endpoints w v hw hsum hmove
  obtain ⟨x,hx,y,hy,hxq,hyq,hxd,hyd⟩ := two_gain_crossings k w v ha hc hk hw' hA hC hs ht hpeak
  exact ⟨x,y,hx.2,hy.1,hw' x ⟨hx.1,hx.2.trans hc⟩,hw' y ⟨ha.trans hy.1,hy.2⟩,hxq,hyq,hxd,hyd⟩

#print axioms endpoint_gain_identity
#print axioms two_transverse_crossings
#print axioms two_gain_crossings
#print axioms normalized_slice_two_gains
end Catenary.ThirdExceptional
