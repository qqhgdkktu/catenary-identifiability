import ThirdGeneric
import ThirdTerminalWitness
import Mathlib.Algebra.Polynomial.ofFn
import Mathlib.Algebra.Polynomial.RingDivision

/-! Generic recovery from the third, penultimate and last chambers. Indices
are zero-based. The square certificate keeps the coefficients of degrees
3 through n−1 of the remainder of W times an unknown of degree < n−3. -/
noncomputable section
namespace Catenary.ThirdTerminal
open Polynomial Continuant Middle EndpointExterior
open scoped Polynomial

def testMatrix {R : Type*} [CommRing R] (k : ℕ) (D W : R[X]) :
    Matrix (Fin k) (Fin k) R :=
  fun i j => ((W * X^j.val) %ₘ D).coeff (i.val+3)

private theorem rows (k : ℕ) (D W : ℝ[X]) (v : Fin k → ℝ) (i : Fin k) :
    (testMatrix k D W).mulVec v i = ((W * ofFn k v) %ₘ D).coeff (i.val+3) := by
  have eq : W * ofFn k v = ∑ j : Fin k, v j • (W*X^j.val) := by
    rw [ofFn_eq_sum_monomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← C_mul_X_pow_eq_monomial,smul_eq_C_mul]
    ring
  rw [eq]
  change _ = (modByMonicHom D (∑ j : Fin k, v j • (W*X^j.val))).coeff _
  simp only [map_sum,map_smul,finset_sum_coeff,coeff_smul,smul_eq_mul]
  simp only [Matrix.mulVec,dotProduct,testMatrix,modByMonicHom_apply,mul_comm]

/-- The certificate is equivalently a polynomial uniqueness criterion on the
physical denominator D and third-output suffix W. -/
theorem det_criterion (k : ℕ) (D W : ℝ[X]) (hm : D.Monic) (hd : D.natDegree=k+3) :
    (testMatrix k D W).det ≠ 0 ↔
    ∀ H U : ℝ[X], H.degree < k → U.degree < (3:ℕ) → D ∣ W*H-U → H=0 := by
  rw [← isUnit_iff_ne_zero,← Matrix.isUnit_iff_isUnit_det,← Matrix.mulVec_injective_iff_isUnit]
  have dd : D.degree = (k+3 : ℕ) := (degree_eq_natDegree hm.ne_zero).trans (congrArg _ hd)
  constructor
  · intro inj H U hh hu hdiv
    let v : Fin k → ℝ := fun i => H.coeff i.val
    have hv : ofFn k v = H := by
      apply Polynomial.ext
      intro i
      by_cases hi : i<k
      · simp [v,hi]
      · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_lt hi),
          (degree_lt_iff_coeff_zero _ _).mp hh _ (Nat.le_of_not_lt hi)]
    have e : (W*H)%ₘ D = U := by
      rw [modByMonic_eq_of_dvd_sub hm hdiv, (modByMonic_eq_self_iff hm).mpr]
      rw [dd]
      exact hu.trans_le (WithBot.coe_le_coe.mpr (by omega : 3 ≤ k+3))
    have z : v = 0 := by
      apply inj
      rw [Matrix.mulVec_zero]
      funext i
      rw [rows,hv,e]
      exact (degree_lt_iff_coeff_zero _ _).mp hu _ (by omega)
    rw [← hv,z,ofFn_zero]
  · intro ker
    rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot,Submodule.eq_bot_iff]
    intro v hv
    change (testMatrix k D W).mulVec v = 0 at hv
    let H := ofFn k v
    let U := (W*H)%ₘ D
    have hU : U.degree < (3:ℕ) := by
      apply (degree_lt_iff_coeff_zero _ _).mpr
      intro j hj
      by_cases bound : j < k+3
      · let i : Fin k := ⟨j-3,by omega⟩
        have e := congrFun hv i
        rw [rows] at e
        simpa only [i,H,U,show j-3+3=j by omega,Pi.zero_apply] using e
      · apply coeff_eq_zero_of_degree_lt
        exact (degree_modByMonic_lt _ hm).trans_le (dd.trans_le
          (WithBot.coe_le_coe.mpr (Nat.le_of_not_lt bound)))
    have dv : D ∣ W*H-U := ⟨(W*H)/ₘ D,by
      have h := modByMonic_add_div (W*H) hm
      dsimp [U]
      linear_combination -h⟩
    have he := ker H U (ofFn_degree_lt _) hU dv
    exact (injective_ofFn k) (he.trans (ofFn_zero k).symm)

/-- At a boundary chain with three inert last chambers, the test determinant
is nonzero whenever the shortened denominator and suffix are coprime. -/
theorem det_at_cut (k : ℕ) (D₀ W₀ : ℝ[X]) (hm : D₀.Monic) (hd : D₀.natDegree=k)
    (hc : IsCoprime D₀ W₀) : (testMatrix k (X^3*D₀) (X^3*W₀)).det ≠ 0 := by
  apply (det_criterion _ _ _ ((monic_X_pow 3).mul hm) (by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hm.ne_zero,natDegree_X_pow,hd,Nat.add_comm])).2
  intro H U hh hu hdiv
  obtain ⟨b,hb⟩ := hdiv
  have du : (X:ℝ[X])^3 ∣ U := ⟨W₀*H-D₀*b,by linear_combination -hb⟩
  have uz : U=0 := eq_zero_of_dvd_of_degree_lt du (by simpa only [degree_X_pow] using hu)
  rw [uz,sub_zero] at hb
  have dz : D₀ ∣ W₀*H := ⟨b,mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero (R:=ℝ))) (by
    simpa only [mul_assoc] using hb)⟩
  exact eq_zero_of_dvd_of_degree_lt (hc.dvd_of_dvd_mul_left dz)
    (by simpa only [degree_eq_natDegree hm.ne_zero,hd] using hh)

/-- The entries of the explicit determinant are polynomials in the directed
rates, including at points with zero transfer rates or with cancellations. -/
def certificate {m} (ℓ : Chamber m) : Obstruction.RatePoly m :=
  (testMatrix (m-2) (symbolicFull ℓ) (symbolicSuffix ℓ 2)).det

theorem eval_certificate {m} (ℓ : Chamber m) (x : Params m) :
    MvPolynomial.eval x (certificate ℓ) = (testMatrix (m-2) (full ℓ x) (suffix ℓ x 2)).det := by
  unfold certificate
  rw [RingHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.eval x (((symbolicSuffix ℓ 2 * X^j.val)%ₘ symbolicFull ℓ).coeff _) = _
  have hm : (symbolicFull ℓ).Monic := Matrix.charpoly_monic _
  rw [← coeff_map,map_modByMonic _ hm,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X,eval_symbolicFull,eval_symbolicSuffix]
  rfl

private theorem last_entries {m} (ℓ v : Chamber m) (x y : Params m) (hx : Positive x)
    (hv : v.val+1=m) (hd : full ℓ x=full ℓ y) (hs : suffix ℓ x v.val=suffix ℓ y v.val)
    (hg : gain ℓ (Fin.last m) x=gain ℓ (Fin.last m) y) (hi : gain ℓ v x=gain ℓ v y) :
    (physicalSite ℓ x m).diag=(physicalSite ℓ y m).diag ∧
    (physicalSite ℓ x v.val).weight=(physicalSite ℓ y v.val).weight := by
  have form (z : Params m) : suffix ℓ z v.val = X-C (physicalSite ℓ z m).diag := by
    unfold suffix physicalSites
    rw [drop_from _ _ _ _ v.isLt, Nat.zero_add]
    change intervalCharpoly (sitesFrom (physicalSite ℓ z) (v.val+1) (m+1-(v.val+1))) = _
    rw [hv,show m+1-m=1 by omega]
    exact (charpoly_eq_cont _).trans (cont_singleton _)
  rw [form,form] at hs
  have d : (physicalSite ℓ x m).diag=(physicalSite ℓ y m).diag :=
    C_injective (by linear_combination -hs)
  have pos (i : Chamber m) : 0 < gain ℓ i x := by
    rw [EndpointThreshold.gain_prod]
    apply Finset.prod_pos
    intro r hr
    have h : r<m := by have := i.isLt; have := Finset.mem_range.mp hr; omega
    simpa [PhysicalInverse.a,h] using hx (fwd ⟨r,h⟩)
  have step (z : Params m) : gain ℓ (Fin.last m) z = gain ℓ v z * PhysicalInverse.a z v.val := by
    rw [EndpointThreshold.gain_prod,EndpointThreshold.gain_prod,Fin.val_last]
    simpa only [hv] using Finset.prod_range_succ (PhysicalInverse.a z) v.val
  have a := hg
  rw [step,step,← hi] at a
  have ea := mul_left_cancel₀ (pos v).ne' a
  have el : (if m=ℓ.val then x (loss m) else 0) = (if m=ℓ.val then y (loss m) else 0) := by
    split_ifs with h
    · have dc (z : Params m) : (full ℓ z).eval 0 = z (loss m) * gain ℓ (Fin.last m) z := by
        have e := Closed.determinant_at_zero ℓ z
        rw [← h] at e
        simpa [full,physicalSites,Closed.pref,EndpointThreshold.gain_prod] using e
      have e := congrArg (Polynomial.eval (0:ℝ)) hd
      rw [dc,dc,← hg] at e
      exact mul_right_cancel₀ (pos _).ne' e
    · rfl
  have diag (z : Params m) : -(physicalSite ℓ z m).diag = PhysicalInverse.b z v.val +
      (if m=ℓ.val then z (loss m) else 0) := by
    have e := PhysicalInverse.diag_total ℓ (Fin.last m) z
    have hprev : PhysicalInverse.prev z m = PhysicalInverse.b z v.val :=
      (congrArg (PhysicalInverse.prev z) hv).symm
    simpa [physicalSite,PhysicalInverse.a,Fin.val_last,hprev] using e
  have eqb := diag x
  rw [d,diag,← el] at eqb
  refine ⟨d,?_⟩
  change PhysicalInverse.b x v.val * PhysicalInverse.a x v.val =
    PhysicalInverse.b y v.val * PhysicalInverse.a y v.val
  rw [ea,(add_right_cancel eqb).symm]

private theorem differential_degree {m} (ℓ v : Chamber m) (x y : Params m)
    (hv : v.val+1=m) (hm : 2 ≤ m) (hd : full ℓ x=full ℓ y)
    (he : (physicalSite ℓ x m).diag=(physicalSite ℓ y m).diag)
    (hb : (physicalSite ℓ x v.val).weight=(physicalSite ℓ y v.val).weight)
    (hx : Positive x) :
    (Middle.prefix ℓ x m-Middle.prefix ℓ y m).degree < (m-2:ℕ) := by
  let J (z : Params m) := PrefixPhysical.leading (physicalSite ℓ z) v.val
  let H (z : Params m) := Middle.prefix ℓ z m
  have recurrence (z : Params m) : full ℓ z = (X-C (physicalSite ℓ z m).diag)*H z -
      C (physicalSite ℓ z v.val).weight*J z := by
    have eq := Closed.prefix_recurrence (physicalSite ℓ z) v.val
    rw [show v.val+2=m+1 by omega,hv] at eq
    simpa only [full,physicalSites,H,Middle.prefix,sitesFrom_take _ _ _ _ (Nat.le_succ _),
      J,PrefixPhysical.leading] using eq
  have same := hd
  rw [recurrence,recurrence,← he,← hb] at same
  have eq : (X-C (physicalSite ℓ x m).diag)*(H x-H y) =
      C (physicalSite ℓ x v.val).weight*(J x-J y) := by linear_combination same
  have degJ (z : Params m) : (J z).degree = (v.val : ℕ) := by
    rw [degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero]
    simp [J,PrefixPhysical.leading,intervalCharpoly_natDegree]
  have low : (J x-J y).degree < (v.val:ℕ) := by
    rw [← degJ x]
    exact degree_sub_lt ((degJ x).trans (degJ y).symm) (Matrix.charpoly_monic _).ne_zero
      ((Matrix.charpoly_monic _).leadingCoeff.trans (Matrix.charpoly_monic _).leadingCoeff.symm)
  have w : (physicalSite ℓ x v.val).weight ≠ 0 := by
    have h : v.val<m := by omega
    simp [physicalSite,PathSite.weight,h,(hx _).ne']
  by_cases h : H x-H y = 0
  · change (H x-H y).degree < _
    rw [h,degree_zero]
    exact WithBot.bot_lt_coe _
  have de := congrArg degree eq
  rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr w),degree_mul,degree_X_sub_C,
    degree_eq_natDegree h] at de
  have lt : 1+(H x-H y).natDegree < v.val := by exact_mod_cast de.trans_lt low
  change (H x-H y).degree < _
  rw [degree_eq_natDegree h]
  exact_mod_cast (by omega : (H x-H y).natDegree < m-2)

/-- For a chain on the nonzero locus of the explicit certificate, equality
of the three actual curves determines every physical rate. No condition is
placed on the competing positive parameter vector. -/
theorem physical_unique {m} (ℓ j v : Chamber m) (x y : Params m) (hx : Positive x)
    (hy : Positive y) (hm : 3 ≤ m) (hj : j.val=2) (hv : v.val+1=m)
    (hc : MvPolynomial.eval x (certificate ℓ) ≠ 0)
    (h₃ : SameCurves 0 (Fin.last m) j ℓ x y) (hpen : SameCurves 0 (Fin.last m) v ℓ x y) :
    x=y := by
  obtain ⟨hd,hw,_,_⟩ := ThirdAdjacent.terminal_and_sensor ℓ j x y hx hy h₃
  obtain ⟨_,hs,hg,hi⟩ := ThirdAdjacent.terminal_and_sensor ℓ v x y hx hy hpen
  obtain ⟨he,hb⟩ := last_entries ℓ v x y hx hv hd hs hg hi
  have low := differential_degree ℓ v x y hv (by omega) hd he hb hx
  let U (z : Params m) := C (weightProduct ℓ j (Fin.last m) z) * Middle.prefix ℓ z j.val
  have du (z : Params m) (hz : Positive z) : (U z).degree < (3:ℕ) := by
    dsimp only [U]
    rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr
      (weightProduct_ne_zero _ _ _ _ hz (show j<Fin.last m from (by change j.val<m; omega)))),
      degree_eq_natDegree (show (Middle.prefix ℓ z j.val).Monic from Matrix.charpoly_monic _).ne_zero]
    simp [Middle.prefix,intervalCharpoly_natDegree,physicalSites_length,hj,show 2≤m+1 by omega]
    decide
  have ident (z : Params m) := GlobalCofactors.endpoint_condensation ℓ j z (by omega)
  have ez := ident y
  rw [← hd,← hw] at ez
  have dv : full ℓ x ∣ suffix ℓ x 2 * (Middle.prefix ℓ x m-Middle.prefix ℓ y m) - (U x-U y) := by
    refine ⟨middlePolynomial ℓ j (Fin.last m) x-middlePolynomial ℓ j (Fin.last m) y,?_⟩
    dsimp [U]
    rw [← hj]
    linear_combination ez - ident x
  rw [eval_certificate] at hc
  have mn : (full ℓ x).natDegree=m-2+3 := by
    simp [full,intervalCharpoly_natDegree,physicalSites_length,show m-2+3=m+1 by omega]
  have z := (det_criterion _ _ _ (Matrix.charpoly_monic _) mn).mp hc _ _ low
    ((degree_sub_le _ _).trans_lt (max_lt (du x hx) (du y hy))) dv
  exact ThirdGeneric.rates_of_leading_pair ℓ x y hx hy hd (sub_eq_zero.mp z)

/-- A single factorized boundary point certifies a nonempty positive
nonzero locus by polynomial density in the directed rates. -/
theorem positive_witness_of_cut {m} (ℓ : Chamber m)
    (cut : ∃ (z : Params m) (D₀ W₀ : ℝ[X]), full ℓ z=X^3*D₀ ∧ suffix ℓ z 2=X^3*W₀ ∧
      D₀.Monic ∧ D₀.natDegree=m-2 ∧ IsCoprime D₀ W₀) :
    ∃ x : Params m, Positive x ∧ MvPolynomial.eval x (certificate ℓ) ≠ 0 := by
  obtain ⟨z,D₀,W₀,hd,hw,hm,hdeg,hc⟩ := cut
  have nz : certificate ℓ ≠ 0 := by
    intro zero
    have e := eval_certificate ℓ z
    rw [zero,map_zero,hd,hw] at e
    exact det_at_cut _ _ _ hm hdeg hc e.symm
  obtain ⟨x,hx,ha,_⟩ := Obstruction.positive_common_witness (certificate ℓ) 1 nz one_ne_zero
  exact ⟨x,hx,ha⟩

/-- For every chain length n≥7 and every fixed leak location, the
certificate takes a nonzero value on the positive physical orthant. -/
theorem positive_witness {m} (ℓ : Chamber m) (hm : 6≤m) :
    ∃ x : Params m, Positive x ∧ MvPolynomial.eval x (certificate ℓ) ≠ 0 :=
  positive_witness_of_cut ℓ (ThirdTerminalWitness.three_inert_chambers ℓ hm)

#print axioms positive_witness
#print axioms physical_unique
#print axioms positive_witness_of_cut
end Catenary.ThirdTerminal
