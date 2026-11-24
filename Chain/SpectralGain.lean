import Chain.Spectral
import Chain.ResolventFormula
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Физический сдвиг и отношение алгебраических дополнений -/

namespace Catenary.SpectralGain

open Polynomial Continuant

private theorem positive_numerator (xs : List ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hp : ∀ t ∈ xs, 0 < t) (u : ℕ) (hu : u < xs.length) :
    0 < firstNumerator (xs.map (Spectral.shiftedSite z)) u := by
  induction xs generalizing u with
  | nil => simp at hu
  | cons t xs ih =>
    have ht : ∀ a ∈ xs, 0 < a := fun a ha => hp a (List.mem_cons_of_mem _ ha)
    cases u with
    | zero =>
      change 0 < cont (xs.map (Spectral.shiftedSite z))
      rw [← Spectral.eval_as_cont]
      exact Spectral.positive_on_ray ht hz
    | succ u =>
      change 0 < -((Spectral.shiftedSite z t).lower) * firstNumerator (xs.map _) u
      simpa [Spectral.shiftedSite] using ih ht u (Nat.lt_of_succ_lt_succ hu)

/-- Обратная матрица (zI−J₀) имеет строго положительные элементы для
    произвольного неотрицательного сдвига на положительных метках. -/
theorem positive_shifted_inverse (xs : List ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hp : ∀ t ∈ xs, 0 < t) :
    ∀ i j, 0 < (pathMatrix (xs.map (Spectral.shiftedSite z)))⁻¹ i j := by
  classical
  let sites := xs.map (Spectral.shiftedSite z)
  have hD : 0 < cont sites := (Spectral.eval_as_cont z xs) ▸ Spectral.positive_on_ray hp hz
  have hswap (ys : List ℕ) : (ys.map (Spectral.shiftedSite z)).map swapSite =
      ys.map (Spectral.shiftedSite z) := by rw [List.map_map]; rfl
  have both (i j : Fin sites.length) (hh : i ≤ j) :
      0 < (pathMatrix sites)⁻¹ i j ∧ 0 < (pathMatrix sites)⁻¹ j i := by
    have hdir : directedProduct (sites.take i.val) = 1 := by
      change directedProduct ((xs.map _).take i.val) = 1
      rw [← List.map_take, Spectral.shifted_directed]
    have hswapPre : (sites.take i.val).map swapSite = sites.take i.val := by
      change ((xs.map _).take i.val).map swapSite = (xs.map _).take i.val
      rw [← List.map_take, hswap]
    have pair := inv_at_indices sites i j hh hD.ne' (hdir.trans_ne one_ne_zero)
      (by rw [hswapPre]; exact hdir.trans_ne one_ne_zero)
    dsimp only at pair
    have hpre : 0 < cont (sites.take i.val) := by
      change 0 < cont ((xs.map _).take i.val)
      rw [← List.map_take, ← Spectral.eval_as_cont]
      exact Spectral.positive_on_ray (fun a ha => hp a (List.mem_of_mem_take ha)) hz
    have hlen : j.val - i.val < (xs.drop i.val).length := by
      have hj : j.val < xs.length := by simpa [sites] using j.isLt
      have hij : i.val ≤ j.val := hh
      rw [List.length_drop]; omega
    have hnum := positive_numerator (xs.drop i.val) hz (fun a ha => hp a (List.mem_of_mem_drop ha))
      (j.val - i.val) hlen
    have hdrop : sites.drop i.val = (xs.drop i.val).map (Spectral.shiftedSite z) := List.map_drop.symm
    rw [pair.1, pair.2, hdrop, hswap]
    exact ⟨div_pos (mul_pos hpre hnum) hD, div_pos (mul_pos hpre hnum) hD⟩
  intro i j
  rcases le_total i j with h | h
  · exact (both i j h).1
  · exact (both j i h).2

/-- Для каждой камеры утечки положительный вектор w удовлетворяет
    (zI−J₀)w=eℓ; это конкретная физическая нормировка §3. -/
theorem exists_positive_gauge (xs : List ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hp : ∀ t ∈ xs, 0 < t) (ell : Fin (xs.map (Spectral.shiftedSite z)).length) :
    ∃ w, (∀ i, 0 < w i) ∧
      (pathMatrix (xs.map (Spectral.shiftedSite z))).mulVec w = Pi.single ell 1 := by
  classical
  let M := pathMatrix (xs.map (Spectral.shiftedSite z))
  have hdet : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    change (pathMatrix (xs.map (Spectral.shiftedSite z))).det ≠ 0
    rw [det_eq_cont, ← Spectral.eval_as_cont]
    exact (Spectral.positive_on_ray hp hz).ne'
  refine ⟨M⁻¹.mulVec (Pi.single ell 1), ?_, ?_⟩
  · intro i
    simpa [Matrix.mulVec_single, M] using positive_shifted_inverse xs hz hp i ell
  · change M.mulVec (M⁻¹.mulVec _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]

/-- При простой спектральной точке та самая координата присоединённой
    матрицы, на которую делится физический коэффициент, ненулевая для
    любой утечки. -/
theorem witness_cofactor_ne_zero (t : ℕ) (xs : List ℕ) (hd : (t :: xs).Nodup) (z : ℝ)
    (hz : (Spectral.block (t :: xs)).eval z = 0)
    (ell : Fin ((t :: xs).map (Spectral.shiftedSite z)).length) :
    (pathMatrix ((t :: xs).map (Spectral.shiftedSite z))).adjugate ⟨0, by simp⟩ ell ≠ 0 := by
  classical
  let M := pathMatrix ((t :: xs).map (Spectral.shiftedSite z))
  let e : Fin ((t :: xs).map (Spectral.shiftedSite z)).length := ⟨0, by simp⟩
  have hdiag : M.adjugate e e = cont (xs.map (Spectral.shiftedSite z)) := by
    change (pathMatrix (Spectral.shiftedSite z t :: xs.map (Spectral.shiftedSite z))).adjugate
      (0 : Fin ((xs.map (Spectral.shiftedSite z)).length + 1))
      (0 : Fin ((xs.map (Spectral.shiftedSite z)).length + 1)) = _
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.val_zero, add_zero, pow_zero, one_mul, Fin.zero_succAbove]
    exact det_eq_cont _
  have ht := Spectral.adjacent_tail xs t z hz
  rw [Spectral.eval_as_cont] at ht
  have hcol : (fun j => M.adjugate j e) ≠ 0 := by
    intro h
    exact ht (hdiag.symm.trans (congrFun h e))
  have hdet : M.det = 0 := by
    change (pathMatrix ((t :: xs).map (Spectral.shiftedSite z))).det = 0
    rwa [det_eq_cont, ← Spectral.eval_as_cont]
  have hker : M.mulVec (fun j => M.adjugate j e) = 0 := by
    funext j
    change (M * M.adjugate) j e = 0
    rw [Matrix.mul_adjugate, hdet, zero_smul, Matrix.zero_apply]
  have hne := Spectral.pencil_kernel_nowhere_zero (t :: xs) hd z _ hcol hker ell
  have hsym : M.adjugate.transpose = M.adjugate := by
    rw [Matrix.adjugate_transpose]
    exact congrArg Matrix.adjugate (Spectral.shifted_symm _ _)
  have heq : M.adjugate e ell = M.adjugate ell e := congrFun (congrFun hsym ell) e
  exact heq.trans_ne hne

/-- Отношение координат w=M⁻¹eℓ совпадает с отношением кофакторов. -/
theorem inverse_gauge_ratio {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (M : Matrix ι ι F) (hdet : M.det ≠ 0) (u v ell : ι) :
    let w := M⁻¹.mulVec (Pi.single ell 1)
    w v / w u = M.adjugate v ell / M.adjugate u ell := by
  intro w
  simp only [w, Matrix.mulVec_single, Matrix.inv_def, Matrix.transpose_apply,
    Pi.smul_apply, MulOpposite.op_one, one_smul, mul_one, Matrix.smul_apply,
    smul_eq_mul, Ring.inverse_eq_inv]
  exact mul_div_mul_left _ _ (inv_ne_zero hdet)

/-- Телескопирование направленных скоростей после диагонального подобия. -/
theorem gauge_gain_product {F : Type*} [Field F] (c w : ℕ → F) (n : ℕ)
    (hw : ∀ i ≤ n, w i ≠ 0) :
    (∏ i ∈ Finset.range n, (c i * w (i + 1) / w i)) =
      (∏ i ∈ Finset.range n, c i) * w n / w 0 := by
  induction n with
  | zero => simp [hw 0 (le_refl _)]
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih (fun i h => hw i (by omega))]
    field_simp [hw n (by omega), hw 0 (by omega)]
    ring

/-- Измеряемое произведение скоростей aᵣ=cᵣwᵣ₊₁/wᵣ записано одним
    отношением реальных кофакторов. В цепи f перечисляет камеры пути. -/
theorem scaled_path_gain_eq_cofactor {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (M : Matrix ι ι F) (hdet : M.det ≠ 0) (ell : ι) (f : ℕ → ι) (c : ℕ → F) (n : ℕ) :
    let w := M⁻¹.mulVec (Pi.single ell 1)
    (∀ r ≤ n, w (f r) ≠ 0) →
      (∏ r ∈ Finset.range n, c r * w (f (r+1)) / w (f r)) =
        (∏ r ∈ Finset.range n, c r) * (M.adjugate (f n) ell / M.adjugate (f 0) ell) := by
  intro w hw
  rw [gauge_gain_product c (fun r => w (f r)) n hw, mul_div_assoc]
  exact congrArg ((∏ r ∈ Finset.range n, c r) * ·) (inverse_gauge_ratio M hdet (f 0) (f n) ell)

section Adjugate

variable {R : Type*} [CommRing R]

/-- Тождество для фактических алгебраических дополнений произвольного
    симметричного трёхдиагонального блока, включая вырожденную матрицу.
    Значения элементов в R могут быть многочленами по параметру возмущения. -/
theorem adjugate_prefix_identity (pre post : List (PathSite R)) (v : PathSite R)
    (ell : Fin (pre ++ v :: post).length)
    (hs : (pathMatrix (pre ++ v :: post)).transpose = pathMatrix (pre ++ v :: post)) :
    let M := pathMatrix (pre ++ v :: post)
    let i : Fin (pre ++ v :: post).length := ⟨pre.length, by simp⟩
    let e : Fin (pre ++ v :: post).length := ⟨0, by simp⟩
    directedProduct pre * M.adjugate i ell =
      M.adjugate e ell * cont pre + M.det * (-firstNumerator pre ell.val) := by
  classical
  intro M i e
  let g : Fin (pre ++ v :: post).length → R := fun j => firstNumerator pre j.val
  have hg : M.mulVec g = Pi.single e (cont pre) - Pi.single i (directedProduct pre) := by
    funext k
    change (pathMatrix (pre ++ v :: post)).mulVec (fun j => firstNumerator pre j.val) k = _
    rw [mulVec_padded_prefix]
    have he : k = e ↔ k.val = 0 := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    have hi : k = i ↔ k.val = pre.length := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    simp only [Pi.sub_apply, Pi.single_apply, he, hi]
  have hrow := congrArg (fun w => M.adjugate.mulVec w) hg
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_single] at hrow
  have h := congrFun hrow ell
  change M.det * firstNumerator pre ell.val =
    M.adjugate ell e * cont pre - M.adjugate ell i * directedProduct pre at h
  have hsym : M.adjugate.transpose = M.adjugate := by
    rw [Matrix.adjugate_transpose]; exact congrArg Matrix.adjugate hs
  have he : M.adjugate ell e = M.adjugate e ell := congrFun (congrFun hsym e) ell
  have hi : M.adjugate ell i = M.adjugate i ell := congrFun (congrFun hsym i) ell
  rw [he, hi] at h
  linear_combination h

end Adjugate

/-- Обычная производная отношения фактических кофакторов при произвольном
    полиномиальном возмущении трёхдиагональной матрицы. При неподвижном
    в первом порядке корне она равна производной ведущего определителя. -/
theorem adjugate_gain_hasDerivAt (pre post : List (PathSite ℝ[X])) (v : PathSite ℝ[X])
    (ell : Fin (pre ++ v :: post).length) (t : ℝ)
    (hs : (pathMatrix (pre ++ v :: post)).transpose = pathMatrix (pre ++ v :: post)) :
    let M := pathMatrix (pre ++ v :: post)
    let i : Fin (pre ++ v :: post).length := ⟨pre.length, by simp⟩
    let e : Fin (pre ++ v :: post).length := ⟨0, by simp⟩
    let Y := directedProduct pre * M.adjugate i ell
    let Q := M.adjugate e ell
    M.det.eval t = 0 → M.det.derivative.eval t = 0 → Q.eval t ≠ 0 →
    HasDerivAt (fun u => Y.eval u / Q.eval u) ((cont pre).derivative.eval t) t := by
  intro M i e Y Q hD hdD hQ
  let A := -firstNumerator pre ell.val
  have hbase : Y = Q * cont pre + M.det * A := adjugate_prefix_identity pre post v ell hs
  have hd := congrArg derivative hbase
  simp only [derivative_add, derivative_mul, add_assoc] at hd
  have hv := gain_quotient_derivative_at_root (Q := Q) (L := cont pre) (A := A)
    (Y := Y) (dQ := Q.derivative) (dL := (cont pre).derivative) (dA := A.derivative)
    (dY := Y.derivative) t hQ hD hdD hbase (by simpa only [add_assoc] using hd)
  rw [← hv]
  exact (Y.hasDerivAt t).div (Q.hasDerivAt t) hQ

/-- Специализация на спектральной точке: знаменатель отношения ненулевой и
    det M(t)=0 автоматически следуют из равенства базовой матрицы zI−J₀ и
    выбора её собственного значения. Единственная дифференциальная предпосылка —
    нулевая первая вариация полного характеристического определителя. -/
theorem witness_gain_hasDerivAt (pre post : List (PathSite ℝ[X])) (v : PathSite ℝ[X])
    (ell : Fin (pre ++ v :: post).length) (t z : ℝ) (a : ℕ) (xs : List ℕ)
    (hd : (a :: xs).Nodup) (hz : (Spectral.block (a :: xs)).eval z = 0)
    (e : Fin (pre ++ v :: post).length ≃ Fin ((a :: xs).map (Spectral.shiftedSite z)).length)
    (hhead : e ⟨0, by simp⟩ = ⟨0, by simp⟩)
    (hs : (pathMatrix (pre ++ v :: post)).transpose = pathMatrix (pre ++ v :: post)) :
    let M := pathMatrix (pre ++ v :: post)
    let i : Fin (pre ++ v :: post).length := ⟨pre.length, by simp⟩
    let i₀ : Fin (pre ++ v :: post).length := ⟨0, by simp⟩
    let Y := directedProduct pre * M.adjugate i ell
    let Q := M.adjugate i₀ ell
    (evalRingHom t).mapMatrix M =
      (pathMatrix ((a :: xs).map (Spectral.shiftedSite z))).submatrix e e →
    M.det.derivative.eval t = 0 →
    HasDerivAt (fun u => Y.eval u / Q.eval u) ((cont pre).derivative.eval t) t := by
  intro M i i₀ Y Q hbase hdD
  have hdet : M.det.eval t = 0 := by
    change (evalRingHom t) M.det = 0
    rw [RingHom.map_det, hbase, Matrix.det_submatrix_equiv_self, det_eq_cont, ← Spectral.eval_as_cont]
    exact hz
  have hQ : Q.eval t ≠ 0 := by
    have heq := congrFun (congrFun ((evalRingHom t).map_adjugate M) i₀) ell
    rw [hbase, Matrix.adjugate_submatrix_equiv_self] at heq
    have ham : Q.eval t =
        (pathMatrix ((a :: xs).map (Spectral.shiftedSite z))).adjugate (e i₀) (e ell) := heq
    rw [show e i₀ = ⟨0, by simp⟩ from hhead] at ham
    exact ham.trans_ne (witness_cofactor_ne_zero a xs hd z hz (e ell))
  exact adjugate_gain_hasDerivAt pre post v ell t hs hdet hdD hQ

end Catenary.SpectralGain
