import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Upper-bound and attainability lemmas for the variational problem on an affine
slice of endpoint spectral weights. The physical spectral-coordinate bridge is a
separate mathematical statement. -/

noncomputable section
open Set
open scoped BigOperators

namespace Catenary.GlobalUpper

/-- Write r(x)=1-x v(x), with the m coefficients of v as coordinates. -/
def residual {m : ℕ} (v : Fin m → ℝ) (x : ℝ) : ℝ :=
  1 - x * ∑ j, v j * x ^ j.val

def energy {n m : ℕ} (lam w : Fin n → ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ i, w i * ((residual v (lam i)) ^ 2 / lam i)

def phi {n : ℕ} (m : ℕ) (lam w : Fin n → ℝ) : ℝ := ⨅ v : Fin m → ℝ, energy lam w v

theorem energy_nonneg {n m : ℕ} {lam w : Fin n → ℝ} (h : ∀ i, 0 < lam i)
    (hw : ∀ i, 0 ≤ w i) (v : Fin m → ℝ) : 0 ≤ energy lam w v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (div_nonneg (sq_nonneg _) (h i).le)

theorem phi_le_energy {n m : ℕ} {lam w : Fin n → ℝ} (h : ∀ i, 0 < lam i)
    (hw : ∀ i, 0 ≤ w i) (v : Fin m → ℝ) : phi m lam w ≤ energy lam w v := by
  apply ciInf_le _ v
  exact ⟨0, fun z ⟨u, hu⟩ => hu ▸ energy_nonneg h hw u⟩

theorem energy_mix {n m : ℕ} (lam x y : Fin n → ℝ) (a b : ℝ) (v : Fin m → ℝ) :
    energy lam (fun i => a * x i + b * y i) v = a * energy lam x v + b * energy lam y v := by
  simp only [energy, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The Rayleigh minimization is concave for all nonnegative spectral weights. -/
theorem phi_concave {n : ℕ} (m : ℕ) {lam : Fin n → ℝ} (h : ∀ i, 0 < lam i) :
    ConcaveOn ℝ {w : Fin n → ℝ | ∀ i, 0 ≤ w i} (phi m lam) := by
  constructor
  · intro x hx y hy a b ha hb hab i
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  · intro x hx y hy a b ha hb hab
    apply le_ciInf
    intro v
    change a * phi m lam x + b * phi m lam y ≤ energy lam (fun i => a * x i + b * y i) v
    rw [energy_mix]
    exact add_le_add (mul_le_mul_of_nonneg_left (phi_le_energy h hx v) ha)
      (mul_le_mul_of_nonneg_left (phi_le_energy h hy v) hb)

/-- Three equal levels force a zero middle derivative. Analyticity is redundant. -/
theorem slope_zero_at_middle {s : Set ℝ} {f : ℝ → ℝ} (hc : ConcaveOn ℝ s f)
    {x y z d : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) (h1 : f x = f y) (h2 : f z = f y)
    (hder : HasDerivAt f d y) : d = 0 := by
  have hle := hc.le_slope_of_hasDerivAt hx hy hxy hder
  have hge := hc.slope_le_of_hasDerivAt hy hz hyz hder
  simp [slope_def_field, h1, h2] at hle hge
  exact le_antisymm hle hge

/-- Any finite selection of regular preimages on a concave slice has size ≤ 2. -/
theorem regular_level_card_le_two {s : Set ℝ} {f : ℝ → ℝ} (hc : ConcaveOn ℝ s f)
    (level : ℝ) (solutions : Finset ℝ)
    (hf : ∀ x ∈ solutions, x ∈ s ∧ f x = level ∧ ∃ d ≠ 0, HasDerivAt f d x) :
    solutions.card ≤ 2 := by
  by_contra! hn
  have hn' : 3 ≤ solutions.card := hn
  let e := solutions.orderEmbOfCardLe hn'
  have hp (i : Fin 3) := hf (e i) (solutions.orderEmbOfCardLe_mem hn' i)
  obtain ⟨hx, hxl, _⟩ := hp 0
  obtain ⟨hy, hyl, d, hd, hdy⟩ := hp 1
  obtain ⟨hz, hzl, _⟩ := hp 2
  exact hd (slope_zero_at_middle hc hx hy hz (e.strictMono (by decide : (0 : Fin 3) < 1))
    (e.strictMono (by decide : (1 : Fin 3) < 2)) (hxl.trans hyl.symm) (hzl.trans hyl.symm) hdy)


/-- Pull back the weight-space estimate to an actual affine line. -/
theorem phi_concave_slice {n : ℕ} (m : ℕ) {lam : Fin n → ℝ} (h : ∀ i, 0 < lam i)
    (w v : Fin n → ℝ) {s : Set ℝ} (hs : Convex ℝ s)
    (hw : ∀ t ∈ s, ∀ i, 0 ≤ w i + t * v i) :
    ConcaveOn ℝ s (fun t => phi m lam (fun i => w i + t * v i)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := (phi_concave m h).2 (hw x hx) (hw y hy) ha hb hab
  convert hh using 2
  funext i
  change w i + (a*x+b*y)*v i = a*(w i+x*v i)+b*(w i+y*v i)
  linear_combination -(w i)*hab

/-- No more than two nonsingular solutions of the energy equation on an affine weight slice. -/
theorem phi_slice_card_le_two {n : ℕ} (m : ℕ) {lam : Fin n → ℝ} (h : ∀ i, 0 < lam i)
    (w v : Fin n → ℝ) {s : Set ℝ} (hs : Convex ℝ s)
    (hw : ∀ t ∈ s, ∀ i, 0 ≤ w i + t * v i) (level : ℝ) (xs : Finset ℝ)
    (hxs : ∀ x ∈ xs, x ∈ s ∧ phi m lam (fun i => w i + x*v i) = level ∧
      ∃ d ≠ 0, HasDerivAt (fun t => phi m lam (fun i => w i + t*v i)) d x) : xs.card ≤ 2 :=
  regular_level_card_le_two (phi_concave_slice m h w v hs hw) level xs hxs

/-- An affine system restricted to a convex domain has a convex fiber. If a point in this
fiber is isolated, it is the only solution (applies to the leak-3 and leak-n linear slices). -/
theorem convex_fiber_unique_of_isolated {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s U : Set V} (hs : Convex ℝ s) {x : V} (hx : x ∈ s) (hU : IsOpen U) (hxU : x ∈ U)
    (hiso : ∀ y ∈ s ∩ U, y = x) : ∀ y ∈ s, y = x := by
  intro y hy
  by_contra hbad
  have hcover : s ⊆ U ∪ ({x}ᶜ : Set V) := by
    intro z hz
    by_cases e : z = x
    · exact Or.inl (e ▸ hxU)
    · exact Or.inr e
  obtain ⟨z, hz, hzU, hzc⟩ := hs.isPreconnected U {x}ᶜ hU isClosed_singleton.isOpen_compl hcover
    ⟨x, hx, hxU⟩ ⟨y, hy, hbad⟩
  exact hzc (hiso z ⟨hz, hzU⟩)

/-- A strict three-point peak gives two transverse intersections at every intermediate level. -/
theorem two_regular_of_peak {a b c q : ℝ} {f : ℝ → ℝ} (hab : a < b) (hbc : b < c)
    (hc : ConcaveOn ℝ (Icc a c) f) (hcont : ContinuousOn f (Icc a c))
    (hdiff : ∀ x ∈ Ioo a c, DifferentiableAt ℝ f x)
    (ha : f a < q) (hb : q < f b) (hcq : f c < q) :
    ∃ x y, x ∈ Ioo a b ∧ y ∈ Ioo b c ∧ f x = q ∧ f y = q ∧
      0 < deriv f x ∧ deriv f y < 0 := by
  have hsub1 : Icc a b ⊆ Icc a c := fun t ht => ⟨ht.1, ht.2.trans hbc.le⟩
  have hsub2 : Icc b c ⊆ Icc a c := fun t ht => ⟨hab.le.trans ht.1, ht.2⟩
  obtain ⟨x, hx, hxq⟩ := intermediate_value_Icc hab.le (hcont.mono hsub1) ⟨ha.le, hb.le⟩
  obtain ⟨y, hy, hyq⟩ := intermediate_value_Icc' hbc.le (hcont.mono hsub2) ⟨hcq.le, hb.le⟩
  have hax : a < x := lt_of_le_of_ne hx.1 (fun e => ha.ne (e.symm ▸ hxq))
  have hxb : x < b := lt_of_le_of_ne hx.2 (fun e => hb.ne (e ▸ hxq.symm))
  have hby : b < y := lt_of_le_of_ne hy.1 (fun e => hb.ne (e.symm ▸ hyq.symm))
  have hyc : y < c := lt_of_le_of_ne hy.2 (fun e => hcq.ne (e ▸ hyq))
  have hbmem : b ∈ Icc a c := ⟨hab.le,hbc.le⟩
  have h1 := hc.slope_le_deriv (hsub1 hx) hbmem hxb (hdiff x ⟨hax,hxb.trans hbc⟩)
  have h2 := hc.deriv_le_slope hbmem (hsub2 hy) hby (hdiff y ⟨hab.trans hby,hyc⟩)
  rw [slope_def_field, hxq] at h1
  rw [slope_def_field, hyq] at h2
  exact ⟨x,y,⟨hax,hxb⟩,⟨hby,hyc⟩,hxq,hyq,
    lt_of_lt_of_le (div_pos (sub_pos.mpr hb) (sub_pos.mpr hxb)) h1,
    lt_of_le_of_lt h2 (div_neg_of_neg_of_pos (sub_neg.mpr hb) (sub_pos.mpr hby))⟩


open Filter Topology

/-- Finitely many distinct regular solutions at arbitrary data continue simultaneously
into any dense set of data. The open eligible set may encode positivity and regularity. -/
theorem move_regular_fiber_to_dense {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {k : ℕ}
    (F : X → Y) {y : Y} (x : Fin k → X) (hinj : Function.Injective x)
    (hf : ∀ i, F (x i) = y) (D : Fin k → X ≃L[ℝ] Y)
    (hd : ∀ i, HasStrictFDerivAt F ((D i) : X →L[ℝ] Y) (x i))
    {eligible : Set X} (ho : IsOpen eligible) (hel : ∀ i, x i ∈ eligible)
    {good : Set Y} (hg : Dense good) :
    ∃ z ∈ good, ∃ u : Fin k → X, Function.Injective u ∧ ∀ i, u i ∈ eligible ∧ F (u i) = z := by
  let g (i : Fin k) := (hd i).localInverse F (D i) (x i)
  have gc (i : Fin k) : ContinuousAt (g i) y := by
    rw [← hf i]; exact (hd i).localInverse_continuousAt
  have gb (i : Fin k) : g i y = x i := by
    rw [← hf i]; exact (hd i).localInverse_apply_image
  have gs (i : Fin k) : ∀ᶠ z in 𝓝 y, F (g i z) = z := by
    rw [← hf i]; exact (hd i).eventually_right_inverse
  have go (i : Fin k) : ∀ᶠ z in 𝓝 y, g i z ∈ eligible :=
    (gc i).tendsto (ho.mem_nhds ((gb i).symm ▸ hel i))
  have sep (i j : Fin k) : ∀ᶠ z in 𝓝 y, i ≠ j → g i z ≠ g j z := by
    by_cases h : i = j
    · exact Eventually.of_forall (fun _ hij => (hij h).elim)
    · have h0 : g i y - g j y ≠ 0 := sub_ne_zero.mpr (by simpa only [gb] using hinj.ne h)
      exact ((gc i |>.sub (gc j)).eventually_ne h0).mono (fun _ hz _ => sub_ne_zero.mp hz)
  have hnear : ∀ᶠ z in 𝓝 y, (Function.Injective fun i => g i z) ∧
      ∀ i, g i z ∈ eligible ∧ F (g i z) = z := by
    have pairs := eventually_all.2 (fun i => eventually_all.2 (fun j => sep i j))
    filter_upwards [pairs, eventually_all.2 (fun i => (go i).and (gs i))] with z hp he
    exact ⟨fun {i j} hij => by by_contra hn; exact hp i j hn hij, he⟩
  obtain ⟨z, hzgood, hz⟩ := hg.inter_nhds_nonempty hnear
  exact ⟨z, hzgood, fun i => g i z, hz⟩

open Matrix

/-- Completion of the square for the Gram matrix in (5), including an empty matrix. -/
theorem gram_minimum {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ) (b u : Fin m → ℝ)
    (base : ℝ) (hsymm : G.transpose = G) (hnon : ∀ v, 0 ≤ v ⬝ᵥ (G *ᵥ v))
    (hu : G *ᵥ u = b) :
    (⨅ v : Fin m → ℝ, base - 2 * (b ⬝ᵥ v) + v ⬝ᵥ (G *ᵥ v)) = base - b ⬝ᵥ u := by
  have hmin (v : Fin m → ℝ) : base - b ⬝ᵥ u ≤ base - 2 * (b ⬝ᵥ v) + v ⬝ᵥ (G *ᵥ v) := by
    have hv := hnon (v-u)
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hu] at hv
    have hcross : u ⬝ᵥ (G *ᵥ v) = b ⬝ᵥ v := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hu]
    rw [hcross, dotProduct_comm v b, dotProduct_comm u b] at hv
    linarith
  apply le_antisymm
  · have hbounded : BddBelow (range fun v : Fin m → ℝ =>
        base - 2 * (b ⬝ᵥ v) + v ⬝ᵥ (G *ᵥ v)) :=
      ⟨base - b ⬝ᵥ u, fun w ⟨v, hv⟩ => hv ▸ hmin v⟩
    apply (ciInf_le hbounded u).trans
    rw [hu, dotProduct_comm u b]; linarith
  · exact le_ciInf hmin


/-- Rectangular Vandermonde matrix evaluating the m free coefficients at the n nodes. -/
def design {n : ℕ} (m : ℕ) (lam : Fin n → ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => lam i ^ j.val

def momentGram {n : ℕ} (m : ℕ) (lam w : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  let A := design m lam
  Aᵀ * (Matrix.diagonal (fun i => w i * lam i) * A)

theorem gram_dot {n m : ℕ} (lam w : Fin n → ℝ) (v : Fin m → ℝ) :
    v ⬝ᵥ (momentGram m lam w *ᵥ v) =
    ∑ i, (w i * lam i) * (((design m lam) *ᵥ v) i)^2 := by
  unfold momentGram
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem energy_as_quadratic {n m : ℕ} {lam : Fin n → ℝ} (h : ∀ i, 0 < lam i)
    (w : Fin n → ℝ) (v : Fin m → ℝ) :
    energy lam w v = (∑ i, w i / lam i) - 2 * (((design m lam)ᵀ *ᵥ w) ⬝ᵥ v) +
      v ⬝ᵥ (momentGram m lam w *ᵥ v) := by
  have hcross : ((design m lam)ᵀ *ᵥ w) ⬝ᵥ v = w ⬝ᵥ ((design m lam) *ᵥ v) := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have hres (i : Fin n) : residual v (lam i) = 1 - lam i * ((design m lam) *ᵥ v) i := by
    simp only [residual, Matrix.mulVec, design, dotProduct]
    congr 2
    apply Finset.sum_congr rfl; intro j hj; exact mul_comm _ _
  rw [hcross, gram_dot]
  simp only [energy, hres, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [ne_of_gt (h i)]; ring

/-- Formula (5) with u the solution of the normal equations; positivity and nonsingularity
of the weighted Gram matrix identify u with G⁻¹ b in the paper. -/
theorem phi_eq_moment_minimum {n m : ℕ} {lam w : Fin n → ℝ}
    (h : ∀ i, 0 < lam i) (hw : ∀ i, 0 ≤ w i) (u : Fin m → ℝ)
    (hu : momentGram m lam w *ᵥ u = (design m lam)ᵀ *ᵥ w) :
    phi m lam w = (∑ i, w i / lam i) - (((design m lam)ᵀ *ᵥ w) ⬝ᵥ u) := by
  unfold phi
  simp_rw [energy_as_quadratic h]
  apply gram_minimum _ _ u _ _ _ hu
  · simp only [momentGram, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  · intro v
    rw [gram_dot]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hw i) (h i).le) (sq_nonneg _)


/-- Strictly positive weights at distinct positive nodes ensure a positive definite Gram matrix. -/
theorem momentGram_posDef {n m : ℕ} (hm : m ≤ n) {lam w : Fin n → ℝ}
    (h : ∀ i, 0 < lam i) (hw : ∀ i, 0 < w i) (hinj : Function.Injective lam) :
    (momentGram m lam w).PosDef := by
  classical
  constructor
  · change (momentGram m lam w)ᴴ = momentGram m lam w
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [momentGram, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]
  · intro v hv
    have hnot : ∃ i, ((design m lam) *ᵥ v) i ≠ 0 := by
      by_contra! hall
      apply hv
      let emb := Fin.castLEOrderEmb hm
      exact Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (hinj.comp emb.injective)
        (fun i => hall (emb i))
    obtain ⟨j,hj⟩ := hnot
    rw [show star v = v by ext; simp, gram_dot]
    exact Finset.sum_pos' (fun i _ => mul_nonneg (mul_nonneg (hw i).le (h i).le) (sq_nonneg _))
      ⟨j,Finset.mem_univ j,mul_pos (mul_pos (hw j) (h j)) (sq_pos_of_ne_zero hj)⟩

/-- The variational principle has the explicit moment/inverse formula without assuming
existence of a minimizer or an independently supplied inverse certificate. -/
theorem phi_inverse_formula {n m : ℕ} (hm : m ≤ n) {lam w : Fin n → ℝ}
    (h : ∀ i, 0 < lam i) (hw : ∀ i, 0 < w i) (hinj : Function.Injective lam) :
    phi m lam w = (∑ i, w i / lam i) - (((design m lam)ᵀ *ᵥ w) ⬝ᵥ
      ((momentGram m lam w)⁻¹ *ᵥ ((design m lam)ᵀ *ᵥ w))) := by
  apply phi_eq_moment_minimum h (fun i => (hw i).le)
  have hdet := (momentGram_posDef hm h hw hinj).det_pos.ne'
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

open Finset Polynomial in
/-- The degree drop in Lagrange interpolation needed to realize the trailing polynomial W. -/
theorem barycentric_vanishing {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : Function.Injective x)
    (P : Polynomial ℝ) (hp : P.degree < ((n-1 : ℕ) : WithBot ℕ)) :
    ∑ i, P.eval (x i) / (Lagrange.nodal Finset.univ x).derivative.eval (x i) = 0 := by
  classical
  let s : Finset (Fin n) := univ
  have hcard : s.card = n := by simp [s]
  have hlt : P.degree < (s.card : WithBot ℕ) := by
    rw [hcard]
    exact hp.trans (by exact_mod_cast (show n-1 < n by omega))
  have interp := Lagrange.eq_interpolate (s:=s) (v:=x) hx.injOn hlt
  have hc := congrArg (fun q : Polynomial ℝ => q.coeff (n-1)) interp
  dsimp only at hc

  rw [Polynomial.coeff_eq_zero_of_degree_lt hp] at hc
  rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff] at hc
  have hsum := hc.symm
  change (∑ i ∈ s, P.eval (x i) / (Lagrange.nodal s x).derivative.eval (x i)) = 0
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.coeff_C_mul, Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
    ← Lagrange.nodal_erase_eq_nodal_div hi, Polynomial.coeff_C_mul]
  have he : (Lagrange.nodal (s.erase i) x).natDegree = n-1 := by
    rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem hi, hcard]
  have hmon := (Lagrange.nodal_monic (s:=s.erase i) (v:=x)).coeff_natDegree
  rw [he] at hmon
  rw [hmon, mul_one, Lagrange.nodalWeight_eq_eval_nodal_derative hi, div_eq_mul_inv]

end Catenary.GlobalUpper
