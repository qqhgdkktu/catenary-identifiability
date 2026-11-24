import Chain.CoprimeWitness
import Chain.SeparatedWitness
import Chain.FullRank

/-! Information contained in the two output curves at an end inlet. -/
noncomputable section
namespace Catenary.EndpointExterior
open Polynomial Continuant Obstruction
open scoped Polynomial Matrix

def gain {m} (ℓ v : Chamber m) (x : Params m) : ℝ :=
  pathGain ((physicalSites ℓ x).take v.val)

theorem full_eval {m} (ℓ : Chamber m) (x : Params m) (s : ℝ) :
    (Middle.full ℓ x).eval s = (s • 1 - generator ℓ x).det := by
  rw [← TransferData.eval_charpoly_eq_det, physical_charpoly_eq_cont]
  exact congrArg (Polynomial.eval s) (charpoly_eq_cont _)

/-- Exact transfer numerator, denominator and leading scalar in the physical coordinates. -/
theorem endpoint_transfer {m} (ℓ v : Chamber m) (x : Params m) (hx : Positive x)
    (s : ℝ) (hs : (s • 1 - generator ℓ x).det ≠ 0) :
    (s • (1 : Mat m) - generator ℓ x)⁻¹ v 0 =
      gain ℓ v x * (Middle.suffix ℓ x v.val).eval s / (Middle.full ℓ x).eval s := by
  have e := (physical_transfer_formula ℓ 0 v x s hx (Fin.zero_le _) hs).1
  simpa only [Fin.val_zero, List.take_zero, List.drop_zero, List.map_nil, Nat.sub_zero, cont_nil,
    one_mul, gain, Middle.suffix, Middle.full, interval_eval, ← List.map_take,
    ← List.map_drop, directedProduct_shift] using e

private theorem gain_ne_zero {m} (ℓ v : Chamber m) (x : Params m) (hx : Positive x) :
    gain ℓ v x ≠ 0 := by
  unfold gain physicalSites
  rw [sitesFrom_take _ _ _ _ v.isLt.le, ← directedProduct_shift 0, sitesFrom_map]
  apply directedProduct_ne_zero
  intro t _ ht
  have hv := v.isLt
  have hm : t < m := by omega
  simp [shiftedSite,physicalSite,hm,(hx (fwd ⟨t,hm⟩)).ne']

private theorem cross {m} (ℓ v : Chamber m) (x y : Params m) (hx : Positive x) (hy : Positive y)
    (hf : ∀ s : ℝ, (s • 1 - generator ℓ x).det ≠ 0 → (s • 1 - generator ℓ y).det ≠ 0 →
       (s • (1 : Mat m) - generator ℓ x)⁻¹ v 0 = (s • (1 : Mat m) - generator ℓ y)⁻¹ v 0) :
    C (gain ℓ v x) * Middle.suffix ℓ x v.val * Middle.full ℓ y =
      C (gain ℓ v y) * Middle.suffix ℓ y v.val * Middle.full ℓ x := by
  apply eq_of_infinite_eval_eq
  apply (TransferData.common_regular_infinite (generator ℓ x) (generator ℓ y)).mono
  intro s hs
  have he := hf s hs.1 hs.2
  rw [endpoint_transfer ℓ v x hx s hs.1, endpoint_transfer ℓ v y hy s hs.2] at he
  have ez := (div_eq_div_iff (by rw [full_eval]; exact hs.1) (by rw [full_eval]; exact hs.2)).mp he
  simpa only [Set.mem_setOf_eq,eval_mul,eval_C] using ez

/-- One reduced transfer is enough. The second output and the competing
parameter need not satisfy any extra coprimality condition. -/
theorem spectra_and_gains_of_curves {m} (ℓ j k : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y)
    (hc : IsCoprime (Middle.full ℓ x) (Middle.suffix ℓ x j.val))
    (he : SameCurves 0 j k ℓ x y) :
    Middle.full ℓ x = Middle.full ℓ y ∧
      Middle.suffix ℓ x j.val = Middle.suffix ℓ y j.val ∧
      Middle.suffix ℓ x k.val = Middle.suffix ℓ y k.val ∧
      gain ℓ j x = gain ℓ j y ∧ gain ℓ k x = gain ℓ k y := by
  have h := (sameCurves_iff_common_regular 0 j k ℓ x y).mp he
  have e₁ := cross ℓ j x y hx hy (fun s u v => (h s u v).1)
  have e₂ := cross ℓ k x y hx hy (fun s u v => (h s u v).2)
  have hD (x : Params m) : (Middle.full ℓ x).Monic := Matrix.charpoly_monic _
  have hS (x : Params m) (u : Chamber m) : (Middle.suffix ℓ x u.val).Monic := Matrix.charpoly_monic _
  have deg : (Middle.full ℓ y).natDegree ≤ (Middle.full ℓ x).natDegree := by
    simp only [Middle.full,intervalCharpoly_natDegree,physicalSites_length,le_refl]
  obtain ⟨hd, hw, hgj⟩ := Middle.scaled_fraction_of_cross (hD x) (hD y)
    (hS x j) (hS y j) deg hc (gain_ne_zero ℓ j x hx) e₁
  rw [hd] at e₂
  have eqn := mul_right_cancel₀ (hD x).ne_zero e₂
  have hgk : gain ℓ k x = gain ℓ k y := by
    simpa only [leadingCoeff_mul, leadingCoeff_C, (hS x k).leadingCoeff, (hS y k).leadingCoeff,
      mul_one] using congrArg leadingCoeff eqn
  rw [← hgk] at eqn
  exact ⟨hd.symm, hw.symm, mul_left_cancel₀ (C_ne_zero.mpr (gain_ne_zero ℓ k x hx)) eqn,
    hgj.symm, hgk⟩

theorem physicalData_of_curves {m} (ℓ j k : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y)
    (hc : IsCoprime (Middle.full ℓ x) (Middle.suffix ℓ x j.val))
    (he : SameCurves 0 j k ℓ x y) :
    physicalData ℓ 0 j k x = physicalData ℓ 0 j k y := by
  obtain ⟨hd,hw,hu,hj,hk⟩ := spectra_and_gains_of_curves ℓ j k x y hx hy hc he
  have hh {t : ℕ} {xs ys : List (PathSite ℝ)} (h : intervalCharpoly xs = intervalCharpoly ys) :
      lowerCoefficients t xs = lowerCoefficients t ys :=
    funext fun i => congrArg (fun p : ℝ[X] => p.coeff i.val) h
  dsimp only [Middle.full, Middle.suffix] at hd hw hu
  dsimp only [gain] at hj hk
  simp only [physicalData, siteData, Fin.val_zero, List.take_zero, List.drop_zero,
    Nat.sub_zero, hh hd, hh hw, hh hu, hj, hk]

theorem no_cancellation_certificate {m} (ℓ j : Chamber m) :
    ∃ q : RatePoly m, MvPolynomial.eval (SpectralPhysical.rates ℓ) q = 1 ∧
      ∀ x : Params m, MvPolynomial.eval x q ≠ 0 →
        IsCoprime (Middle.full ℓ x) (Middle.suffix ℓ x j.val) := by
  have hx := (SpectralPhysical.no_cancellation ℓ 0 j).of_mul_right_right
  obtain ⟨q,hq,h⟩ := CoprimeWitness.monic_pair_certificate
    (Middle.symbolicFull ℓ) (Middle.symbolicSuffix ℓ j.val)
    (Matrix.charpoly_monic _) (SpectralPhysical.rates ℓ) (by simpa using hx)
  exact ⟨q,hq,fun x he => by simpa using h x he⟩

theorem generic_of_observed_rank_somewhere {m} (ℓ j k : Chamber m) (a : Params m)
    (hr : Function.Injective
      (fderiv ℝ (polynomialValues (coordinatePolynomial ℓ 0 j k)) a)) :
    GenericLocalID 0 j k ℓ := by
  obtain ⟨q,hq,hcert⟩ := no_cancellation_certificate ℓ j
  apply generic_of_full_rank_somewhere 0 j k ℓ (coordinatePolynomial ℓ 0 j k) q a
    (by intro eq; simp [eq] at hq) hr
  intro x hx hxq
  refine ⟨1,zero_lt_one, fun y hy _ h => ?_⟩
  change (fun s => MvPolynomial.eval x (coordinatePolynomial ℓ 0 j k s)) = _
  rw [eval_coordinatePolynomial]
  change _ = fun s => MvPolynomial.eval y (coordinatePolynomial ℓ 0 j k s)
  rw [eval_coordinatePolynomial, physicalData_of_curves ℓ j k x y hx hy (hcert x hxq) h]

theorem generic_of_observed_rank {m} (ℓ j k : Chamber m)
    (hr : Function.Injective
      (fderiv ℝ (polynomialValues (coordinatePolynomial ℓ 0 j k)) (SpectralPhysical.rates ℓ))) :
    GenericLocalID 0 j k ℓ := generic_of_observed_rank_somewhere ℓ j k _ hr

/-- The cross-difference vanishes by degree when d≤r. This argument compares
two arbitrary chains and does not pass to infinitesimal variations. -/
theorem small_polynomial_recovery {F : Type*} [Field F]
    {D W U B B' P P' H H' : F[X]} (hw : W ≠ 0) (hwu : IsCoprime W U)
    (hbe : IsCoprime B P) (hb : B.Monic) (hb' : B'.Monic) (hdeg : B'.natDegree ≤ B.natDegree)
    (hs : B.natDegree + P'.natDegree < W.natDegree)
    (hs' : B'.natDegree + P.natDegree < W.natDegree)
    (h₁ : D*B = W*H-U*P) (h₂ : D*B' = W*H'-U*P') : B = B' ∧ P = P' := by
  obtain ⟨z, hz, _⟩ := existsUnique_tangent_quotient hw hwu h₁ h₂
  have dn : (B*P'-P*B').natDegree < W.natDegree :=
    (natDegree_sub_le _ _).trans_lt (max_lt (natDegree_mul_le.trans_lt hs)
      (natDegree_mul_le.trans_lt (by simpa [Nat.add_comm] using hs')))
  have hz' : B*P'-P*B' = 0 := eq_zero_of_dvd_of_degree_lt ⟨z,hz.1⟩
    (degree_le_natDegree.trans_lt (by rw [degree_eq_natDegree hw]; exact_mod_cast dn))
  have he := sub_eq_zero.mp hz'
  have hd : B ∣ B' := hbe.dvd_of_dvd_mul_left ⟨P',he.symm⟩
  have eq := eq_of_monic_of_dvd_of_natDegree_le hb hb' hd hdeg
  rw [eq, mul_comm P B] at he
  exact ⟨eq.symm,(mul_left_cancel₀ hb.ne_zero he).symm⟩

def middlePolynomial {m} (ℓ j k : Chamber m) (x : Params m) : ℝ[X] :=
  intervalCharpoly (sitesFrom (physicalSite ℓ x) (j.val+1) (k.val-(j.val+1)))

def symbolicMiddle {m} (ℓ j k : Chamber m) : (RatePoly m)[X] :=
  intervalCharpoly (sitesFrom (symbolicSite ℓ) (j.val+1) (k.val-(j.val+1)))

@[simp] theorem eval_symbolicMiddle {m} (ℓ j k : Chamber m) (x : Params m) :
    (symbolicMiddle ℓ j k).map (MvPolynomial.eval x) = middlePolynomial ℓ j k x := by
  simp only [symbolicMiddle, middlePolynomial, map_interval, sitesFrom_map, eval_symbolicSite]

def weightProduct {m} (ℓ j k : Chamber m) (x : Params m) : ℝ :=
  (physicalSite ℓ x j.val).weight *
    edgeProduct (sitesFrom (physicalSite ℓ x) (j.val+1) (k.val-(j.val+1)))

theorem weightProduct_ne_zero {m} (ℓ j k : Chamber m) (x : Params m) (hx : Positive x)
    (hjk : j < k) : weightProduct ℓ j k x ≠ 0 := by
  have hj : j.val < k.val := hjk
  have hk := k.isLt
  have unit (u : ℕ) (hu : u < m) : (physicalSite ℓ x u).weight ≠ 0 := by
    simp [PathSite.weight,physicalSite,hu,(hx (back ⟨u,hu⟩)).ne',(hx (fwd ⟨u,hu⟩)).ne']
  have prod (u n : ℕ) (h : u+n ≤ m) :
      edgeProduct (sitesFrom (physicalSite ℓ x) u n) ≠ 0 := by
    induction n generalizing u with
    | zero => simp [sitesFrom,edgeProduct]
    | succ n ih =>
      change (physicalSite ℓ x u).weight * edgeProduct (sitesFrom (physicalSite ℓ x) (u+1) n) ≠ 0
      exact mul_ne_zero (unit u (by omega)) (ih (u+1) (by omega))
  exact mul_ne_zero (unit j.val (by omega)) (prod _ _ (by omega))

private theorem full_split {m} (ℓ j k : Chamber m) (x : Params m) (hjk : j < k) :
    Middle.full ℓ x * middlePolynomial ℓ j k x =
      Middle.suffix ℓ x j.val * Middle.prefix ℓ x k.val -
      Middle.suffix ℓ x k.val * (C (weightProduct ℓ j k x) * Middle.prefix ℓ x j.val) := by
  let f := physicalSite ℓ x
  let d := j.val
  let g := k.val-(j.val+1)
  let r := m-k.val
  have hj : j.val < k.val := hjk
  have hk := k.isLt
  have hkg : d+1+g=k.val := by dsimp [d,g]; omega
  have hm : d + (m-d+1) = m+1 := by dsimp [d]; omega
  have hw : g+(r+1)=m-d := by dsimp [g,r,d]; omega
  have hp : d+(g+1)=k.val := by omega
  let L := sitesFrom f 0 d
  let M := sitesFrom f (d+1) g
  let T := sitesFrom f (k.val+1) r
  have rr (v : Chamber m) : Middle.suffix ℓ x v.val =
      intervalCharpoly (sitesFrom f (v.val+1) (m-v.val)) := by
    unfold Middle.suffix physicalSites
    rw [Middle.drop_from _ _ _ _ v.isLt]
    simp [f]
  have pp (v : Chamber m) : Middle.prefix ℓ x v.val = intervalCharpoly (sitesFrom f 0 v.val) := by
    unfold Middle.prefix physicalSites
    rw [sitesFrom_take _ _ _ _ v.isLt.le]
  have hW : sitesFrom f (d+1) (m-d) = M ++ f k.val :: T := by
    rw [← hw, Middle.from_append, hkg]
    rfl
  have hD : physicalSites ℓ x = L ++ f d :: (M ++ f k.val :: T) := by
    change sitesFrom f 0 (m+1) = _
    calc
      _ = sitesFrom f 0 (d+(m-d+1)) := congrArg (sitesFrom f 0) hm.symm
      _ = _ := by rw [Middle.from_append, Nat.zero_add]; simp only [sitesFrom,hW]; rfl
  have hH : sitesFrom f 0 k.val = L ++ f d :: M := by
    rw [← hp, Middle.from_append, Nat.zero_add]
    rfl
  rw [Middle.full,hD, rr j, rr k, pp k, pp j, hH]
  change _ = intervalCharpoly (sitesFrom f (d+1) (m-d)) * _ - _
  rw [hW]
  exact charpoly_condensation L M T (f d) (f k.val)

structure Good {m} (ℓ j k : Chamber m) (x : Params m) : Prop where
  reduced : IsCoprime (Middle.full ℓ x) (Middle.suffix ℓ x j.val)
  trailing : IsCoprime (Middle.suffix ℓ x j.val) (Middle.suffix ℓ x k.val)
  interior : IsCoprime (middlePolynomial ℓ j k x) (Middle.prefix ℓ x j.val)
  arms : IsCoprime (Middle.prefix ℓ x j.val) (Middle.suffix ℓ x j.val)

/-- In the range j−1≤n−k, the three spectra determine the entire physical
vector at every good reference parameter, even among remote positive competitors. -/
theorem rates_of_three_spectra {m} (ℓ j k : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) (hj : 0 < j.val) (hjk : j < k)
    (small : j.val ≤ m-k.val) (good : Good ℓ j k x)
    (hD : Middle.full ℓ x = Middle.full ℓ y)
    (hW : Middle.suffix ℓ x j.val = Middle.suffix ℓ y j.val)
    (hU : Middle.suffix ℓ x k.val = Middle.suffix ℓ y k.val) : x = y := by
  let B (z : Params m) := middlePolynomial ℓ j k z
  let E (z : Params m) := Middle.prefix ℓ z j.val
  let W (z : Params m) := Middle.suffix ℓ z j.val
  let P (z : Params m) := C (weightProduct ℓ j k z) * E z
  have bdeg (z : Params m) : (B z).natDegree = k.val-(j.val+1) := by
    simp only [B,middlePolynomial,intervalCharpoly_natDegree,sitesFrom_length]
  have edeg (z : Params m) : (E z).natDegree = j.val := by
    simp [E,Middle.prefix,intervalCharpoly_natDegree,physicalSites_length,Nat.min_eq_left j.isLt.le]
  have wdeg (z : Params m) : (W z).natDegree = m-j.val := by
    simp [W,Middle.suffix,intervalCharpoly_natDegree,physicalSites_length]
  have pdeg (z : Params m) : (P z).natDegree ≤ j.val :=
    (natDegree_C_mul_le _ _).trans_eq (edeg z)
  have kx := weightProduct_ne_zero ℓ j k x hx hjk
  have hcop : IsCoprime (B x) (P x) :=
    (isCoprime_mul_unit_left_right ((isUnit_iff_ne_zero.mpr kx).map (C : ℝ →+* ℝ[X])) _ _).mpr
      good.interior
  have e₁ := full_split ℓ j k x hjk
  have e₂ := full_split ℓ j k y hjk
  rw [← hD, ← hW, ← hU] at e₂
  have size (z t : Params m) : (B z).natDegree + (P t).natDegree < (W x).natDegree := by
    rw [bdeg,wdeg]
    have hk := k.isLt
    have hjk' : j.val < k.val := hjk
    have := pdeg t
    omega
  obtain ⟨_,hp⟩ := small_polynomial_recovery
    (W := W x) (B := B x) (B' := B y) (P := P x) (P' := P y)
    (Matrix.charpoly_monic _).ne_zero good.trailing hcop (Matrix.charpoly_monic _)
    (Matrix.charpoly_monic _) (by rw [bdeg,bdeg]) (size x y) (size y x) e₁ e₂
  have hE (z : Params m) : (E z).Monic := Matrix.charpoly_monic _
  have heK : weightProduct ℓ j k x = weightProduct ℓ j k y := by
    simpa only [P,leadingCoeff_mul,leadingCoeff_C,(hE x).leadingCoeff,(hE y).leadingCoeff,mul_one]
      using congrArg leadingCoeff hp
  change C (weightProduct ℓ j k x) * E x = C (weightProduct ℓ j k y) * E y at hp
  rw [← heK] at hp
  have he := mul_left_cancel₀ (C_ne_zero.mpr kx) hp
  let l := j.val-1
  let r := m-(j.val+1)
  have hk := k.isLt
  have hjk' : j.val < k.val := hjk
  have hn : l+r+2 = m := by dsimp [l,r]; omega
  have hjl : j.val = l+1 := by dsimp [l]; omega
  obtain ⟨xl,xr⟩ := Middle.joined_parts ℓ j x hx l r hn hjl
  obtain ⟨yl,yr⟩ := Middle.joined_parts ℓ j y hy l r hn hjl
  apply Middle.rates_of_physicalJoined ℓ x y hx hy l r hn
  apply Middle.Joined.eq_of_determinant_and_branches
  · rw [xl,xr]
    exact good.arms
  · rw [Middle.physicalJoined_determinant _ _ _ _ _ hn,
      Middle.physicalJoined_determinant _ _ _ _ _ hn]
    exact hD
  · exact xl.trans (he.trans yl.symm)
  · exact xr.trans (hW.trans yr.symm)

theorem good_at_separated {m} (ℓ j k : Chamber m) (hjk : j < k) :
    Good ℓ j k (SpectralPhysical.rates ℓ) := by
  have h₁ : j.val < k.val := hjk
  have h₂ := k.isLt
  let g := k.val-(j.val+1)
  let r := m-k.val
  let T := List.range' (k.val+2) r
  let M := List.range' (j.val+2) g
  have hm : j.val+2+g=k.val+1 := by dsimp [g]; omega
  have hlen : g+(r+1)=m-j.val := by dsimp [g,r]; omega
  have decomp : List.range' (j.val+2) (m-j.val) = M ++ (k.val+1)::T := by
    rw [← hlen, ← List.range'_append_1, hm]
    simp only [List.range'_succ, M, T]
  have inner : middlePolynomial ℓ j k (SpectralPhysical.rates ℓ) = Spectral.block M :=
    SpectralPhysical.segment ℓ (j.val+1) g (by dsimp [g]; omega)
  refine ⟨(SpectralPhysical.no_cancellation ℓ 0 j).of_mul_right_right, ?_, ?_,
    SpectralPhysical.separated_branches ℓ j⟩
  · rw [SpectralPhysical.suffix_eq,SpectralPhysical.suffix_eq,decomp]
    apply Spectral.nested_coprime _ (List.nodup_range' (s:=k.val+2) (n:=r))
    intro t ht hu
    simp only [M,T,List.mem_range'_1] at ht hu
    omega
  · rw [inner,SpectralPhysical.prefix_eq]
    apply Spectral.separated_coprime (List.nodup_range' (s:=j.val+2) (n:=g))
    intro t ht hu
    simp only [M,List.mem_range'_1] at ht hu
    omega

theorem good_certificate {m} (ℓ j k : Chamber m) (a : Params m) (ha : Good ℓ j k a) :
    ∃ q : RatePoly m, MvPolynomial.eval a q = 1 ∧
      ∀ x : Params m, MvPolynomial.eval x q ≠ 0 → Good ℓ j k x := by
  obtain ⟨u,hu,cu⟩ := CoprimeWitness.monic_pair_certificate
    (Middle.symbolicFull ℓ) (Middle.symbolicSuffix ℓ j.val)
    (Matrix.charpoly_monic _) a (by simpa using ha.reduced)
  obtain ⟨v,hv,cv⟩ := CoprimeWitness.monic_pair_certificate
    (Middle.symbolicSuffix ℓ j.val) (Middle.symbolicSuffix ℓ k.val)
    (Matrix.charpoly_monic _) a (by simpa using ha.trailing)
  obtain ⟨w,hw,cw⟩ := CoprimeWitness.monic_pair_certificate
    (symbolicMiddle ℓ j k) (Middle.symbolicPrefix ℓ j.val)
    (Matrix.charpoly_monic _) a (by simpa using ha.interior)
  obtain ⟨t,ht,ct⟩ := CoprimeWitness.monic_pair_certificate
    (Middle.symbolicPrefix ℓ j.val) (Middle.symbolicSuffix ℓ j.val)
    (Matrix.charpoly_monic _) a (by simpa using ha.arms)
  refine ⟨(u*v)*(w*t), by simp [hu,hv,hw,ht], fun x h => ?_⟩
  simp only [map_mul, mul_ne_zero_iff] at h
  exact ⟨by simpa using cu x h.1.1, by simpa using cv x h.1.2,
    by simpa using cw x h.2.1, by simpa using ct x h.2.2⟩

/-- For each leak position and full length, the endpoint experiment globally
identifies a generic positive rate vector when j−1≤n−k (one-based labels). -/
theorem generic_global_small {m} (ℓ j k : Chamber m) (hj : 0 < j.val)
    (hjk : j < k) (small : j.val ≤ m-k.val) :
    ∃ q : RatePoly m, MvPolynomial.eval (SpectralPhysical.rates ℓ) q = 1 ∧
      ∀ x y : Params m, Positive x → Positive y → MvPolynomial.eval x q ≠ 0 →
        SameCurves 0 j k ℓ x y → x = y := by
  obtain ⟨q,hq,hgood⟩ := good_certificate ℓ j k _ (good_at_separated ℓ j k hjk)
  refine ⟨q,hq,fun x y hx hy hq' hc => ?_⟩
  have h := hgood x hq'
  obtain ⟨hD,hW,hU,_,_⟩ := spectra_and_gains_of_curves ℓ j k x y hx hy h.reduced hc
  exact rates_of_three_spectra ℓ j k x y hx hy hj hjk small h hD hW hU

theorem generic_small {m} (ℓ j k : Chamber m) (hj : 0 < j.val)
    (hjk : j < k) (small : j.val ≤ m-k.val) : GenericLocalID 0 j k ℓ := by
  obtain ⟨q,hq,h⟩ := generic_global_small ℓ j k hj hjk small
  exact ⟨q,⟨_,SpectralPhysical.positive ℓ,hq.trans_ne one_ne_zero⟩,
    fun x hx he => ⟨1,zero_lt_one,fun y hy _ hs => (h x y hx hy he hs).symm⟩⟩

end Catenary.EndpointExterior
