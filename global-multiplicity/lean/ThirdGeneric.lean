import GlobalCofactors
import ThirdAdjacent

/-! Recovery from an endpoint input and two nonterminal sensors.  All chamber
indices in this file start at zero. The two coprimality conditions are imposed
on the original chain only. -/
noncomputable section
namespace Catenary.ThirdGeneric
open Polynomial Continuant Middle EndpointExterior
open scoped Polynomial

/-- Two small polynomial numerators give the endpoint cofactor uniquely. The
sensor cofactors `W,E` and the measured denominator `D` are shared. -/
theorem endpoint_cofactor_of_two_sensors {K : Type*} [Field K]
    {D W E H₁ H₂ U₁ U₂ V₁ V₂ : K[X]} (hD : D ≠ 0)
    (hDW : IsCoprime D W) (hUV : IsCoprime U₁ V₁)
    (hu₁ : U₁ ≠ 0) (hu₂ : U₂ ≠ 0) (hu : U₂.natDegree ≤ U₁.natDegree)
    (hs₁ : U₁.natDegree + V₂.natDegree < D.natDegree)
    (hs₂ : U₂.natDegree + V₁.natDegree < D.natDegree)
    (hm₁ : H₁.Monic) (hm₂ : H₂.Monic)
    (hh₁ : H₁.natDegree < D.natDegree) (hh₂ : H₂.natDegree < D.natDegree)
    (a₁ : D ∣ W*H₁-U₁) (a₂ : D ∣ W*H₂-U₂)
    (b₁ : D ∣ E*H₁-V₁) (b₂ : D ∣ E*H₂-V₂) : H₁ = H₂ := by
  obtain ⟨A₁, ha₁⟩ := a₁
  obtain ⟨A₂, ha₂⟩ := a₂
  obtain ⟨B₁, hb₁⟩ := b₁
  obtain ⟨B₂, hb₂⟩ := b₂
  have vanishes {p : K[X]} (hp : D ∣ p) (hdeg : p.natDegree < D.natDegree) : p = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hp
    exact degree_le_natDegree.trans_lt (by rw [degree_eq_natDegree hD]; exact_mod_cast hdeg)
  have cross : U₁*V₂ = U₂*V₁ := by
    apply sub_eq_zero.mp
    apply vanishes
    · refine ⟨A₂*V₁-A₁*V₂+W*(H₂*B₁-H₁*B₂), ?_⟩
      linear_combination -V₂*ha₁ + V₁*ha₂ + W*H₂*hb₁ - W*H₁*hb₂
    · exact (natDegree_sub_le _ _).trans_lt (max_lt
        (natDegree_mul_le.trans_lt hs₁) (natDegree_mul_le.trans_lt hs₂))
  have divU : U₁ ∣ U₂ := hUV.dvd_of_dvd_mul_right ⟨V₂, cross.symm⟩
  obtain ⟨q, hq⟩ := divU
  have hq₀ : q ≠ 0 := by rintro rfl; simp [hq] at hu₂
  have hconst : q.natDegree = 0 := by
    rw [hq, natDegree_mul hu₁ hq₀] at hu
    omega
  let c := q.coeff 0
  have hqC : q = C c := eq_C_of_natDegree_eq_zero hconst
  have divH : D ∣ W*(H₂-C c*H₁) := by
    refine ⟨A₂-C c*A₁, ?_⟩
    rw [hq, hqC] at ha₂
    linear_combination ha₂ - C c * ha₁
  have eqH : H₂ = C c*H₁ := sub_eq_zero.mp (vanishes (hDW.dvd_of_dvd_mul_left divH)
    ((natDegree_sub_le _ _).trans_lt (max_lt hh₂ ((natDegree_C_mul_le _ _).trans_lt hh₁))))
  have hc : (1 : K) = c := by
    simpa only [hm₂.leadingCoeff, leadingCoeff_mul, leadingCoeff_C, hm₁.leadingCoeff, mul_one]
      using congrArg leadingCoeff eqH
  simpa only [← hc, map_one, one_mul] using eqH.symm

/-- The characteristic polynomial and its degree-one-shorter leading minor
recover every positive physical rate at the specified leak location. -/
theorem rates_of_leading_pair {m} (ℓ : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) (hd : full ℓ x = full ℓ y)
    (hh : Middle.prefix ℓ x m = Middle.prefix ℓ y m) : x = y := by
  let code (z : Params m) (hz : Positive z) :=
    leftCode (fun i => (physicalSite ℓ z i).diag) (physicalEdge ℓ z hz) 0 m
  have pair (z : Params m) (hz : Positive z) :
      (code z hz).boundaryPair = (full ℓ z, Middle.prefix ℓ z m) := by
    rw [show Middle.prefix ℓ z m = intervalCharpoly (sitesFrom (physicalSite ℓ z) 0 m) by
      unfold Middle.prefix physicalSites
      rw [sitesFrom_take _ _ _ _ (by omega)]]
    exact left_pair _ _ _ _ (fun i _ hi => edge_value _ _ _ _ (by omega))
  have hc := JacobiData.boundaryPair_injective m
    ((pair x hx).trans ((Prod.ext hd hh).trans (pair y hy).symm))
  obtain ⟨diag, prod⟩ := left_inj _ _ _ _ _ _ hc
  apply PhysicalInverse.rates_of_diagonal_and_products ℓ x y hx hy
  · intro i
    simpa [physicalSite,i.isLt] using diag i.val (by have := i.isLt; omega)
  · intro i
    have e := congrArg (fun a : ℝˣ => (a : ℝ)) (prod i.val i.isLt)
    simpa [edge_value,physicalSite,PathSite.weight,i.isLt,mul_comm] using e

/-- For physical chambers `j+1` and `k+1` with `j+k<n`, equality of the
three output curves (including chamber `n`) forces equality of all rates if
the original denominator and first tail, and the two original leading minors,
are respectively coprime. For `j=2` this includes each `4 ≤ r ≤ n−2`. -/
theorem physical_unique_of_coprime {m} (ℓ j k : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) (hj : j.val < m) (hk : k.val < m)
    (hsize : j.val + k.val < m+1)
    (hDW : IsCoprime (full ℓ x) (suffix ℓ x j.val))
    (hcop : IsCoprime (Middle.prefix ℓ x j.val) (Middle.prefix ℓ x k.val))
    (hjcurves : SameCurves 0 (Fin.last m) j ℓ x y)
    (hkcurves : SameCurves 0 (Fin.last m) k ℓ x y) : x = y := by
  obtain ⟨hd,hw,_,_⟩ := ThirdAdjacent.terminal_and_sensor ℓ j x y hx hy hjcurves
  obtain ⟨_,he,_,_⟩ := ThirdAdjacent.terminal_and_sensor ℓ k x y hx hy hkcurves
  let U (v : Chamber m) (z : Params m) :=
    C (weightProduct ℓ v (Fin.last m) z) * Middle.prefix ℓ z v.val
  have nonzero (v : Chamber m) (hv : v.val < m) (z : Params m) (hz : Positive z) :
      weightProduct ℓ v (Fin.last m) z ≠ 0 := weightProduct_ne_zero _ _ _ _ hz hv
  have degU (v : Chamber m) (hv : v.val < m) (z : Params m) (hz : Positive z) :
      (U v z).natDegree = v.val := by
    simp only [U, natDegree_C_mul (nonzero v hv z hz), Middle.prefix, intervalCharpoly_natDegree,
      List.length_take,physicalSites_length,Nat.min_eq_left v.isLt.le]
  have cond (v : Chamber m) (hv : v.val < m) (z : Params m) :
      full ℓ z ∣ suffix ℓ z v.val * Middle.prefix ℓ z m - U v z :=
    ⟨_, (GlobalCofactors.endpoint_condensation ℓ v z hv).symm⟩
  have yj := cond j hj y
  have yk := cond k hk y
  rw [← hd, ← hw] at yj
  rw [← hd, ← he] at yk
  have ddeg : (full ℓ x).natDegree = m+1 := by
    simp [full,intervalCharpoly_natDegree,physicalSites_length]
  have hdeg (z : Params m) : (Middle.prefix ℓ z m).natDegree = m := by
    simp [Middle.prefix,intervalCharpoly_natDegree,physicalSites_length]
  have hu₁ (z : Params m) (hz : Positive z) : U j z ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr (nonzero j hj z hz)) (Matrix.charpoly_monic _).ne_zero
  have uv : IsCoprime (U j x) (U k x) :=
    (isCoprime_mul_units_left ((isUnit_iff_ne_zero.mpr (nonzero j hj x hx)).map C)
      ((isUnit_iff_ne_zero.mpr (nonzero k hk x hx)).map C) _ _).mpr hcop
  apply rates_of_leading_pair ℓ x y hx hy hd
  exact endpoint_cofactor_of_two_sensors (D := full ℓ x) (H₁ := Middle.prefix ℓ x m)
    (H₂ := Middle.prefix ℓ y m) (Matrix.charpoly_monic _).ne_zero hDW uv
    (hu₁ x hx) (hu₁ y hy) (by rw [degU j hj y hy,degU j hj x hx])
    (by rwa [degU j hj x hx,degU k hk y hy,ddeg])
    (by rwa [degU j hj y hy,degU k hk x hx,ddeg])
    (Matrix.charpoly_monic _) (Matrix.charpoly_monic _)
    (by rw [hdeg,ddeg]; omega) (by rw [hdeg,ddeg]; omega)
    (cond j hj x) yj (cond k hk x) yk

/-- The separated physical Jacobi chain simultaneously witnesses coprimality
of the two leading minors at any two distinct ordered cuts. -/
private theorem witness_prefixes {m} (ℓ j k : Chamber m) (hjk : j < k) :
    IsCoprime (Middle.prefix ℓ (SpectralPhysical.rates ℓ) j.val)
      (Middle.prefix ℓ (SpectralPhysical.rates ℓ) k.val) := by
  rw [SpectralPhysical.prefix_eq, SpectralPhysical.prefix_eq]
  have hlt : j.val < k.val := hjk
  let u : Chamber (k.val-1) := ⟨j.val, by omega⟩
  have len : k.val-1+1 = k.val := by omega
  apply IsCoprime.symm
  apply Spectral.coprime_of_distinct_zeros (List.nodup_range' (s:=1) (n:=k.val))
  intro z h
  have split := SpectralPhysical.split_tags u
  have split' := (congrArg (List.range' 1) len.symm).trans split
  rw [split'] at h
  exact Spectral.full_root_prefix_ne (SpectralPhysical.disjoint_tags u) h

/-- A single exceptional polynomial, equal to one at an explicit positive
physical vector, works against every positive competitor, including exceptional
competitors. This covers the third sensor at `4 ≤ r ≤ n−2`. -/
theorem generic_physical_unique {m} (ℓ j k : Chamber m) (hjk : j < k) (hk : k.val < m)
    (hsize : j.val + k.val < m+1) :
    ∃ q : Obstruction.RatePoly m, MvPolynomial.eval (SpectralPhysical.rates ℓ) q = 1 ∧
      ∀ x y : Params m, Positive x → Positive y → MvPolynomial.eval x q ≠ 0 →
        SameCurves 0 (Fin.last m) j ℓ x y → SameCurves 0 (Fin.last m) k ℓ x y → x = y := by
  let a := SpectralPhysical.rates ℓ
  obtain ⟨u,hu,cu⟩ := CoprimeWitness.monic_pair_certificate
    (symbolicFull ℓ) (symbolicSuffix ℓ j.val) (Matrix.charpoly_monic _) a
    (by simpa only [eval_symbolicFull,eval_symbolicSuffix] using
      (SpectralPhysical.no_cancellation ℓ 0 j).of_mul_right_right)
  obtain ⟨v,hv,cv⟩ := CoprimeWitness.monic_pair_certificate
    (symbolicPrefix ℓ j.val) (symbolicPrefix ℓ k.val) (Matrix.charpoly_monic _) a
    (by simpa only [eval_symbolicPrefix] using witness_prefixes ℓ j k hjk)
  refine ⟨u*v, by change MvPolynomial.eval a (u*v) = 1; simp only [map_mul,hu,hv,mul_one], ?_⟩
  intro x y hx hy h hjc hkc
  rw [map_mul,mul_ne_zero_iff] at h
  exact physical_unique_of_coprime ℓ j k x y hx hy (lt_trans hjk hk) hk hsize
    (by simpa using cu x h.1) (by simpa using cv x h.2) hjc hkc

end Catenary.ThirdGeneric

#print axioms Catenary.ThirdGeneric.endpoint_cofactor_of_two_sensors
#print axioms Catenary.ThirdGeneric.physical_unique_of_coprime

#print axioms Catenary.ThirdGeneric.generic_physical_unique
