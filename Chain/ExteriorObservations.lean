import Chain.EndpointExterior
import Chain.ClosedDifferential

/-!
# Две кривые при подаче слева от обоих датчиков

В окрестности положительной точки одна приведённая передаточная дробь
определяет полный знаменатель, произведение двух внешних определителей и
первый коэффициент усиления. Локальная единственность монического делителя
выделяет общий левый фактор. Вторая кривая затем даёт оставшиеся компоненты.
-/

noncomputable section
namespace Catenary.ExteriorObservations

open Polynomial Continuant Obstruction
open Filter
open scoped Polynomial Topology

def gain {m : ℕ} (ℓ i v : Chamber m) (x : Params m) : ℝ :=
  pathGain (((physicalSites ℓ x).drop i.val).take (v.val - i.val))

def numerator {m : ℕ} (ℓ i v : Chamber m) (x : Params m) : ℝ[X] :=
  Middle.prefix ℓ x i.val * Middle.suffix ℓ x v.val

theorem monic_numerator {m : ℕ} (ℓ i v : Chamber m) (x : Params m) :
    (numerator ℓ i v x).Monic := (Matrix.charpoly_monic _).mul (Matrix.charpoly_monic _)

theorem gain_ne_zero {m : ℕ} (ℓ i v : Chamber m) (x : Params m) (hx : Positive x)
    (hiv : i ≤ v) : gain ℓ i v x ≠ 0 := by
  have hi := i.isLt
  have hv := v.isLt
  have huv : i.val ≤ v.val := hiv
  unfold gain physicalSites
  rw [Middle.drop_from _ 0 (m+1) i.val hi.le, Nat.zero_add,
    sitesFrom_take _ _ _ _ (by omega), ← directedProduct_shift 0, sitesFrom_map]
  apply directedProduct_ne_zero
  intro t _ ht
  have hm : t < m := by omega
  simp [shiftedSite, physicalSite, hm, (hx (fwd ⟨t, hm⟩)).ne']

theorem transfer {m : ℕ} (ℓ i v : Chamber m) (x : Params m) (hx : Positive x)
    (hiv : i ≤ v) (s : ℝ) (hs : (s • 1 - generator ℓ x).det ≠ 0) :
    (s • (1 : Mat m) - generator ℓ x)⁻¹ v i =
      gain ℓ i v x * (numerator ℓ i v x).eval s / (Middle.full ℓ x).eval s := by
  simpa only [gain, numerator, Middle.prefix, Middle.suffix, Middle.full, eval_mul, interval_eval,
    ← List.map_take, ← List.map_drop, directedProduct_shift, mul_left_comm] using
    (physical_transfer_formula ℓ i v x s hx hiv hs).1

private theorem cross {m : ℕ} (ℓ i v : Chamber m) (x y : Params m) (hx : Positive x) (hy : Positive y)
    (hiv : i ≤ v)
    (hf : ∀ s : ℝ, (s • 1 - generator ℓ x).det ≠ 0 → (s • 1 - generator ℓ y).det ≠ 0 →
      (s • (1 : Mat m) - generator ℓ x)⁻¹ v i = (s • (1 : Mat m) - generator ℓ y)⁻¹ v i) :
    C (gain ℓ i v x) * numerator ℓ i v x * Middle.full ℓ y =
      C (gain ℓ i v y) * numerator ℓ i v y * Middle.full ℓ x := by
  apply eq_of_infinite_eval_eq
  apply (TransferData.common_regular_infinite (generator ℓ x) (generator ℓ y)).mono
  intro s hs
  have e := hf s hs.1 hs.2
  rw [transfer ℓ i v x hx hiv s hs.1, transfer ℓ i v y hy hiv s hs.2] at e
  have ez := (div_eq_div_iff (by rw [EndpointExterior.full_eval]; exact hs.1)
    (by rw [EndpointExterior.full_eval]; exact hs.2)).mp e
  simpa only [Set.mem_setOf_eq, eval_mul, eval_C] using ez

/-- До локального выбора монического делителя оба произведения внешних
    определителей и оба усиления уже совпадают глобально. -/
theorem products_of_curves {m : ℕ} (ℓ i j k : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) (hij : i ≤ j) (hik : i ≤ k)
    (hc : IsCoprime (Middle.full ℓ x) (numerator ℓ i j x)) (he : SameCurves i j k ℓ x y) :
    Middle.full ℓ x = Middle.full ℓ y ∧ numerator ℓ i j x = numerator ℓ i j y ∧
      numerator ℓ i k x = numerator ℓ i k y ∧ gain ℓ i j x = gain ℓ i j y ∧
      gain ℓ i k x = gain ℓ i k y := by
  have h := (sameCurves_iff_common_regular i j k ℓ x y).mp he
  have e₁ := cross ℓ i j x y hx hy hij (fun s u v => (h s u v).1)
  have e₂ := cross ℓ i k x y hx hy hik (fun s u v => (h s u v).2)
  have hD (a : Params m) : (Middle.full ℓ a).Monic := Matrix.charpoly_monic _
  have hdg : (Middle.full ℓ y).natDegree ≤ (Middle.full ℓ x).natDegree := by
    simp only [Middle.full, intervalCharpoly_natDegree, physicalSites_length, le_refl]
  obtain ⟨hd, hn, hgj⟩ := Middle.scaled_fraction_of_cross (hD x) (hD y)
    (monic_numerator ℓ i j x) (monic_numerator ℓ i j y) hdg hc (gain_ne_zero ℓ i j x hx hij) e₁
  rw [hd] at e₂
  have eqn := mul_right_cancel₀ (hD x).ne_zero e₂
  have hgk : gain ℓ i k x = gain ℓ i k y := by
    simpa only [leadingCoeff_mul, leadingCoeff_C, (monic_numerator ℓ i k x).leadingCoeff,
      (monic_numerator ℓ i k y).leadingCoeff, mul_one] using congrArg leadingCoeff eqn
  rw [← hgk] at eqn
  exact ⟨hd.symm, hn.symm, mul_left_cancel₀ (C_ne_zero.mpr (gain_ne_zero ℓ i k x hx hik)) eqn,
    hgj.symm, hgk⟩

/-- Локальное считывание всех коэффициентов D,S,W,U и двух усилений из
    двух наблюдаемых кривых. Обе наблюдаемые вершины могут совпадать со входом. -/
theorem local_physicalData_of_curves {m : ℕ} (ℓ i j k : Chamber m) (x : Params m)
    (hx : Positive x) (hij : i ≤ j) (hik : i ≤ k)
    (hc : IsCoprime (Middle.full ℓ x) (numerator ℓ i j x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Params m, Positive y → dist y x < ε →
      SameCurves i j k ℓ x y → physicalData ℓ i j k x = physicalData ℓ i j k y := by
  have hP (a : Params m) : (Middle.prefix ℓ a i.val).Monic := Matrix.charpoly_monic _
  have hW : (Middle.suffix ℓ x j.val).Monic := Matrix.charpoly_monic _
  have split := Middle.locally_split_product (fun a => Middle.prefix ℓ a i.val)
    (fun a => Middle.suffix ℓ a j.val) (hP x) hW.ne_zero
    (fun n => (Middle.prefix_coeff_continuous ℓ i n).continuousAt)
  have near : ∀ᶠ y in 𝓝 x, Positive y → SameCurves i j k ℓ x y →
      physicalData ℓ i j k x = physicalData ℓ i j k y := by
    filter_upwards [split] with y hsplit hp hcurves
    obtain ⟨hd, hj, hk, gj, gk⟩ := products_of_curves ℓ i j k x y hx hp hij hik hc hcurves
    obtain ⟨hS, hW'⟩ := hsplit (hP y) hj.symm
    have hU : Middle.suffix ℓ x k.val = Middle.suffix ℓ y k.val := by
      unfold numerator at hk
      rw [hS] at hk
      exact mul_left_cancel₀ (hP x).ne_zero hk
    have coeffs {d : ℕ} {xs ys : List (PathSite ℝ)} (h : intervalCharpoly xs = intervalCharpoly ys) :
        lowerCoefficients d xs = lowerCoefficients d ys :=
      funext fun t => congrArg (fun p : ℝ[X] => p.coeff t.val) h
    dsimp only [Middle.full, Middle.prefix, Middle.suffix] at hd hS hW' hU
    dsimp only [gain] at gj gk
    simp only [physicalData, siteData, coeffs hd, coeffs hS.symm, coeffs hW'.symm, coeffs hU, gj, gk]
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff_ball.mp near
  exact ⟨ε, hε, fun y hy hd he => hall y hd hy he⟩

theorem no_cancellation_certificate {m : ℕ} (ℓ i j : Chamber m) :
    ∃ q : RatePoly m, MvPolynomial.eval (SpectralPhysical.rates ℓ) q = 1 ∧
      ∀ x : Params m, MvPolynomial.eval x q ≠ 0 →
        IsCoprime (Middle.full ℓ x) (numerator ℓ i j x) := by
  obtain ⟨q, hq, h⟩ := CoprimeWitness.monic_pair_certificate
    (Middle.symbolicFull ℓ) (Middle.symbolicPrefix ℓ i.val * Middle.symbolicSuffix ℓ j.val)
    (Matrix.charpoly_monic _) (SpectralPhysical.rates ℓ)
    (by simpa using SpectralPhysical.no_cancellation ℓ i j)
  exact ⟨q, hq, fun x hx => by simpa [numerator] using h x hx⟩

private theorem gain_from {m : ℕ} (ℓ : Chamber m) (x : Params m) (u n : ℕ) :
    pathGain (sitesFrom (physicalSite ℓ x) u n) =
      ∏ r ∈ Finset.range n, PhysicalInverse.a x (u + r) := by
  induction n generalizing u with
  | zero => simp [sitesFrom, pathGain]
  | succ n ih =>
    rw [Finset.prod_range_succ']
    change PhysicalInverse.a x u * pathGain (sitesFrom (physicalSite ℓ x) (u+1) n) = _
    rw [ih]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1, mul_comm]

/-- Настоящий физический скаляр усиления — произведение именно рёбер
    между i и v, в том числе при отрицательных и нулевых скоростях. -/
theorem gain_eq_range {m : ℕ} (ℓ i v : Chamber m) (x : Params m) (hiv : i ≤ v) :
    gain ℓ i v x = ∏ r ∈ Finset.range (v.val-i.val), PhysicalInverse.a x (i.val+r) := by
  have hi := i.isLt
  have hv := v.isLt
  have huv : i.val ≤ v.val := hiv
  unfold gain physicalSites
  rw [Middle.drop_from _ _ _ _ hi.le, Nat.zero_add, sitesFrom_take _ _ _ _ (by omega)]
  exact gain_from ℓ x _ _

/-- В замкнутой цепи ведущий определитель до датчика v равен ведущему
    определителю до входа i, умноженному на измеряемое направленное усиление i→v. -/
theorem closed_gain_factor {m : ℕ} (ℓ i v : Chamber m) (x : Params m)
    (hx : x (loss m) = 0) (hiv : i ≤ v) :
    Closed.pref ℓ x v.val = Closed.pref ℓ x i.val * gain ℓ i v x := by
  rw [Closed.prefix_closed ℓ x hx _ v.isLt.le, Closed.prefix_closed ℓ x hx _ i.isLt.le,
    gain_eq_range ℓ i v x hiv]
  have huv : i.val ≤ v.val := hiv
  calc
    _ = ∏ r ∈ Finset.range (i.val + (v.val-i.val)), PhysicalInverse.a x r := by
      rw [Nat.add_sub_of_le huv]
    _ = _ := Finset.prod_range_add _ _ _

theorem closed_gain_prefix_variation {m : ℕ} (ℓ i v : Chamber m) (x dir : Params m)
    (hx : x (loss m) = 0) (hd : dir (loss m) = 0) (hiv : i ≤ v)
    (hS : HasDerivAt (fun t : ℝ => Closed.pref ℓ (x + t • dir) i.val) 0 0)
    (hG : HasDerivAt (fun t : ℝ => gain ℓ i v (x + t • dir)) 0 0) :
    HasDerivAt (fun t : ℝ => Closed.pref ℓ (x + t • dir) v.val) 0 0 := by
  have hf : (fun t : ℝ => Closed.pref ℓ (x + t • dir) v.val) =
      (fun t : ℝ => Closed.pref ℓ (x + t • dir) i.val * gain ℓ i v (x + t • dir)) :=
    funext fun t => closed_gain_factor ℓ i v _ (by simp [hx, hd]) hiv
  rw [hf]
  simpa using hS.mul hG

/-- При нулевой базовой утечке уже δD(0)=0 обнуляет её вариацию.
    Если неподвижны δS(0) и оба физических усиления, исчезают обе
    нужные в §7 производные ведущих определителей, с одним и тем же входом. -/
theorem closed_exterior_variations {m : ℕ} (ℓ i j k : Chamber m) (x dir : Params m)
    (hx : x (loss m) = 0) (hab : ∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0)
    (hij : i ≤ j) (hik : i ≤ k)
    (hD : HasDerivAt (fun t : ℝ => Closed.pref ℓ (x + t • dir) (m+1)) 0 0)
    (hS : HasDerivAt (fun t : ℝ => Closed.pref ℓ (x + t • dir) i.val) 0 0)
    (hJ : HasDerivAt (fun t : ℝ => gain ℓ i j (x + t • dir)) 0 0)
    (hK : HasDerivAt (fun t : ℝ => gain ℓ i k (x + t • dir)) 0 0) :
    dir (loss m) = 0 ∧
      HasDerivAt (fun t : ℝ => Closed.pref ℓ (x + t • dir) j.val) 0 0 ∧
      HasDerivAt (fun t : ℝ => Closed.pref ℓ (x + t • dir) k.val) 0 0 := by
  have hd := Closed.loss_variation ℓ x dir hx hab hD
  exact ⟨hd, closed_gain_prefix_variation ℓ i j x dir hx hd hij hS hJ,
    closed_gain_prefix_variation ℓ i k x dir hx hd hik hS hK⟩

/-- Нулевой вектор образа настоящего якобиана зануляет производную каждого
    сохранённого коэффициента и каждого усиления вдоль прямой x+t·dir. -/
theorem physicalData_kernel_derivative {m : ℕ} (ℓ i j k : Chamber m) (x dir : Params m)
    (hker : fderiv ℝ (polynomialValues (coordinatePolynomial ℓ i j k)) x dir = 0) :
    ∀ s, HasDerivAt (fun t : ℝ => flatten (physicalData ℓ i j k (x+t • dir)) s) 0 0 := by
  let P := coordinatePolynomial ℓ i j k
  have hline : HasDerivAt (fun t : ℝ => x + t • dir) dir 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const dir).const_add x)
  have hf : DifferentiableAt ℝ (polynomialValues P) x := by
    apply differentiableAt_pi.mpr
    intro s
    obtain ⟨_, hp, _⟩ := polynomial_strict_jet (P s) x
    exact hp.hasFDerivAt.differentiableAt
  have hx : HasFDerivAt (polynomialValues P) (fderiv ℝ (polynomialValues P) x) (x+(0 : ℝ) • dir) := by
    simpa using hf.hasFDerivAt
  have h : HasDerivAt (fun t : ℝ => polynomialValues P (x+t • dir))
      (fderiv ℝ (polynomialValues P) x dir) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => x+t • dir) (0 : ℝ) hx hline
  rw [show fderiv ℝ (polynomialValues P) x dir = 0 from hker] at h
  have eqread (y : Params m) : polynomialValues P y = flatten (physicalData ℓ i j k y) :=
    eval_coordinatePolynomial ℓ i j k y
  intro s
  simpa only [eqread, Pi.zero_apply] using hasDerivAt_pi.mp h s

private theorem finite_coeff_derivative {d : ℕ} (f : ℝ → ℝ[X]) (z : ℝ)
    (hm : ∀ t, (f t).Monic) (hd : ∀ t, (f t).natDegree = d)
    (h : ∀ r : Fin d, HasDerivAt (fun t : ℝ => (f t).coeff r.val) 0 0) :
    HasDerivAt (fun t : ℝ => (f t).eval z) 0 0 := by
  have he (t : ℝ) : (f t).eval z = z^d + ∑ r : Fin d, (f t).coeff r.val * z^r.val := by
    have e := congrArg (Polynomial.eval z) (restore_coefficients (f t) (hm t) (hd t))
    simpa only [restore, eval_add, eval_pow, eval_X, eval_finset_sum, eval_mul, eval_C] using e.symm
  have hc (r : Fin d) : HasDerivAt (fun t : ℝ => (f t).coeff r.val * z^r.val) 0 0 := by
    simpa using (h r).mul_const (z^r.val)
  have hs := HasDerivAt.sum (u := Finset.univ) (fun r _ => hc r)
  simpa only [he, Finset.sum_const_zero] using hs.const_add (z^d)

/-- У любого направления в ядре якобиана все четыре интервальных полинома
    имеют нулевые производные при любом фиксированном спектральном аргументе. -/
theorem physicalData_kernel_evaluations {m : ℕ} (ℓ i j k : Chamber m) (x dir : Params m)
    (hker : fderiv ℝ (polynomialValues (coordinatePolynomial ℓ i j k)) x dir = 0) (z : ℝ) :
    HasDerivAt (fun t : ℝ => (Middle.full ℓ (x+t • dir)).eval z) 0 0 ∧
    HasDerivAt (fun t : ℝ => (Middle.prefix ℓ (x+t • dir) i.val).eval z) 0 0 ∧
    HasDerivAt (fun t : ℝ => (Middle.suffix ℓ (x+t • dir) j.val).eval z) 0 0 ∧
    HasDerivAt (fun t : ℝ => (Middle.suffix ℓ (x+t • dir) k.val).eval z) 0 0 := by
  have h := physicalData_kernel_derivative ℓ i j k x dir hker
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply finite_coeff_derivative (d := m+1) _ z (fun _ => Matrix.charpoly_monic _)
    · intro t; simp [Middle.full, intervalCharpoly_natDegree]
    · exact fun r => h (.inl r)
  · apply finite_coeff_derivative (d := i.val) _ z (fun _ => Matrix.charpoly_monic _)
    · intro t; simp [Middle.prefix, intervalCharpoly_natDegree, Nat.min_eq_left i.isLt.le]
    · exact fun r => h (.inr (.inl r))
  · apply finite_coeff_derivative (d := m+1-(j.val+1)) _ z (fun _ => Matrix.charpoly_monic _)
    · intro t; simp [Middle.suffix, intervalCharpoly_natDegree]
    · exact fun r => h (.inr (.inr (.inl r)))
  · apply finite_coeff_derivative (d := m+1-(k.val+1)) _ z (fun _ => Matrix.charpoly_monic _)
    · intro t; simp [Middle.suffix, intervalCharpoly_natDegree]
    · exact fun r => h (.inr (.inr (.inr (.inl r))))

/-- Чтение подсистемы доказательства §7 непосредственно из ядра физического
    якобиана при нулевой утечке и произвольном входе слева от двух выходов. -/
theorem closed_exterior_kernel {m : ℕ} (ℓ i j k : Chamber m) (x dir : Params m)
    (hx : x (loss m) = 0) (hab : ∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0)
    (hij : i ≤ j) (hik : i ≤ k)
    (hker : fderiv ℝ (polynomialValues (coordinatePolynomial ℓ i j k)) x dir = 0) :
    dir (loss m) = 0 ∧
      HasDerivAt (fun t : ℝ => Closed.pref ℓ (x + t • dir) j.val) 0 0 ∧
      HasDerivAt (fun t : ℝ => Closed.pref ℓ (x + t • dir) k.val) 0 0 := by
  have read := physicalData_kernel_derivative ℓ i j k x dir hker
  apply closed_exterior_variations ℓ i j k x dir hx hab hij hik
  · have h := read (.inl ⟨0, by omega⟩)
    change HasDerivAt (fun t : ℝ => (intervalCharpoly (physicalSites ℓ (x+t • dir))).coeff 0) 0 0 at h
    simpa only [coeff_zero_eq_eval_zero, physicalSites, Closed.pref] using h
  · by_cases hpos : 0 < i.val
    · have h := read (.inr (.inl ⟨0, hpos⟩))
      change HasDerivAt (fun t : ℝ =>
        (intervalCharpoly ((physicalSites ℓ (x+t • dir)).take i.val)).coeff 0) 0 0 at h
      simpa only [coeff_zero_eq_eval_zero, physicalSites, sitesFrom_take _ _ _ _ i.isLt.le,
        Closed.pref] using h
    · have hi : i.val = 0 := by omega
      have e : (fun t : ℝ => Closed.pref ℓ (x+t • dir) i.val) = fun _ : ℝ => (1 : ℝ) := by
        funext t
        simp [Closed.pref, hi, sitesFrom, intervalCharpoly, charpoly_eq_cont]
      rw [e]
      exact hasDerivAt_const 0 1
  · exact read (.inr (.inr (.inr (.inr false))))
  · exact read (.inr (.inr (.inr (.inr true))))

end Catenary.ExteriorObservations

namespace Catenary

open Obstruction

/-- Для входа слева от обоих выходов полный столбцовый ранг полиномиальной
    карты физических данных в произвольной вещественной точке достаточен
    для типичной локальной идентифицируемости по двум исходным кривым. -/
theorem generic_of_exterior_signed_rank {m : ℕ} (i j k ℓ : Chamber m) (a : Params m)
    (hij : i ≤ j) (hik : i ≤ k)
    (hr : Function.Injective (fderiv ℝ (polynomialValues (coordinatePolynomial ℓ i j k)) a)) :
    GenericLocalID i j k ℓ := by
  obtain ⟨q, hq, hcert⟩ := ExteriorObservations.no_cancellation_certificate ℓ i j
  apply generic_of_full_rank_somewhere i j k ℓ (coordinatePolynomial ℓ i j k) q a
    (by intro eq; simp [eq] at hq) hr
  intro x hx hxq
  obtain ⟨ε, hε, hall⟩ := ExteriorObservations.local_physicalData_of_curves
    ℓ i j k x hx hij hik (hcert x hxq)
  refine ⟨ε, hε, fun y hy hd he => ?_⟩
  change (fun s => MvPolynomial.eval x (coordinatePolynomial ℓ i j k s)) = _
  rw [eval_coordinatePolynomial]
  change _ = fun s => MvPolynomial.eval y (coordinatePolynomial ℓ i j k s)
  rw [eval_coordinatePolynomial, hall y hy hd he]

end Catenary
