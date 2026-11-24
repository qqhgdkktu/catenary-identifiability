import Chain.PrefixExtension
import Chain.EndpointThreshold

/-! The physical change of coordinates for an interior inlet. All unreduced
edge weights are signed. The proof differentiates actual polynomial motions
and recovers the prefix by Euclidean division over the dual numbers. -/
noncomputable section
open Polynomial Filter
open scoped Polynomial Topology
namespace Catenary.PrefixPhysical
open Continuant Obstruction WitnessVariation

/-- Independent diagonal and edge-product coordinates of a tail with n edges. -/
abbrev Jac (n : ℕ) := (Fin (n+1) → ℝ) × (Fin n → ℝ)

/-- The tail of a physical matrix, in its actual diagonal and edge-product coordinates. -/
def tailCoords {m} (ℓ : Chamber m) (x : Params m) (s n : ℕ) : Jac n :=
  (fun i => (physicalSite ℓ x (s+i.val)).diag, fun e => (physicalSite ℓ x (s+e.val)).weight)

abbrev leading {R : Type*} [CommRing R] (f : ℕ → PathSite R) (q : ℕ) :=
  intervalCharpoly (sitesFrom f 0 q)

/-- The bridge uses the product of the actual two opposing rates. -/
def edgeMinor {R : Type*} [CommRing R] (f : ℕ → PathSite R) (p : ℕ) : R[X] :=
  C (f p).weight * leading f p

/-- The prefix has p+1 vertices and the tail has n+1 vertices. The first
component stores a variation from the chosen monic reference polynomial. -/
def coordinates {m} (ℓ : Chamber m) (p n : ℕ) (z : Fin (p+1) → ℝ) (S : ℝ[X])
    (x : Params m) : (Fin (p+1) → ℝ) × (Fin (p+1) → ℝ) × Jac n :=
  let f := physicalSite ℓ x
  (fun a => (leading f (p+1) - S).eval (z a), fun a => (edgeMinor f p).eval (z a),
    tailCoords ℓ x (p+1) n)

theorem segment_smooth {m} (ℓ : Chamber m) (u q : ℕ) (z : ℝ) :
    ContDiff ℝ 1 (fun x : Params m => (intervalCharpoly (sitesFrom (physicalSite ℓ x) u q)).eval z) := by
  let P := intervalCharpoly (sitesFrom (symbolicSite ℓ) u q)
  have eval (x : Params m) : (intervalCharpoly (sitesFrom (physicalSite ℓ x) u q)).eval z =
      MvPolynomial.eval x (P.eval (MvPolynomial.C z)) := by
    have he : P.map (MvPolynomial.eval x) = intervalCharpoly (sitesFrom (physicalSite ℓ x) u q) := by
      simp only [P,map_interval,sitesFrom_map,eval_symbolicSite]
    rw [← he,eval_map]
    simpa only [MvPolynomial.eval_C] using (P.eval₂_at_apply (MvPolynomial.eval x) (MvPolynomial.C z))
  simp_rw [eval]
  exact (polynomial_eval_contDiff _).of_le (by simp)

private theorem site_smooth {m} (ℓ : Chamber m) (r : ℕ) :
    ContDiff ℝ 1 (fun x : Params m => (physicalSite ℓ x r).diag) ∧
    ContDiff ℝ 1 (fun x : Params m => (physicalSite ℓ x r).weight) := by
  constructor
  · have e (x : Params m) : (physicalSite ℓ x r).diag = MvPolynomial.eval x (symbolicSite ℓ r).diag :=
      congrArg PathSite.diag (eval_symbolicSite ℓ x r).symm
    simp_rw [e]
    exact (polynomial_eval_contDiff _).of_le (by simp)
  · have e (x : Params m) : (physicalSite ℓ x r).weight = MvPolynomial.eval x (symbolicSite ℓ r).weight := by
      rw [← eval_symbolicSite ℓ x r]
      simp [PathSite.weight,mapSite]
    simp_rw [e]
    exact (polynomial_eval_contDiff _).of_le (by simp)

theorem coordinates_smooth {m} (ℓ : Chamber m) (p n : ℕ) (z : Fin (p+1) → ℝ) (S : ℝ[X]) :
    ContDiff ℝ 1 (coordinates ℓ p n z S) := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro a
    simpa only [eval_sub] using (segment_smooth ℓ 0 (p+1) (z a)).sub
      (contDiff_const (c:=S.eval (z a)))
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro a
    simpa only [edgeMinor,eval_mul,eval_C] using (site_smooth ℓ p).2.mul (segment_smooth ℓ 0 p (z a))
  · exact (contDiff_pi.mpr fun i : Fin (n+1) => (site_smooth ℓ (p+1+i.val)).1).prodMk
      (contDiff_pi.mpr fun i : Fin n => (site_smooth ℓ (p+1+i.val)).2)

private theorem units_weight (φ : ℝ[X] →+* DualNumber ℝ) (f : ℕ → PathSite ℝ[X]) (p : ℕ)
    (h : ∀ a, a ≤ p → IsUnit (φ (f a).weight)) :
    ∃ w : ℕ → (DualNumber ℝ)ˣ, ∀ a, a ≤ p → (w a : DualNumber ℝ) = φ (f a).weight := by
  classical
  exact ⟨fun a => if ha : a≤p then (h a ha).unit else 1, fun a ha => by simp [ha]⟩

/-- The two true prefix polynomials recover every diagonal and every
edge-product variation up to and including the joining edge. -/
theorem prefix_velocity_rigid (f : ℕ → PathSite ℝ[X]) (p : ℕ) (t : ℝ)
    (hreg : ∀ a, a ≤ p → (f a).weight.eval t ≠ 0)
    (hS : velocity t (leading f (p+1)) = 0) (hV : velocity t (edgeMinor f p) = 0) :
    (∀ a, a ≤ p → (f a).diag.derivative.eval t = 0) ∧
      (∀ a, a ≤ p → (f a).weight.derivative.eval t = 0) := by
  let φ := jet t
  let ψ := stationary t
  obtain ⟨v,hv⟩ := units_weight φ f p (fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    (isUnit_iff_ne_zero.mpr (hreg a ha)))
  obtain ⟨w,hw⟩ := units_weight ψ f p (fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    (isUnit_iff_ne_zero.mpr (hreg a ha)))
  let x := Middle.leftCode (fun a => φ (f a).diag) v 0 p
  let y := Middle.leftCode (fun a => ψ (f a).diag) w 0 p
  have pair (η : ℝ[X] →+* DualNumber ℝ) (d : ℕ → (DualNumber ℝ)ˣ)
      (hd : ∀ a, a ≤ p → (d a : DualNumber ℝ) = η (f a).weight) :
      (Middle.leftCode (fun a => η (f a).diag) d 0 p).boundaryPair =
        ((leading f (p+1)).map η, (leading f p).map η) := by
    simp only [leading,map_interval,sitesFrom_map]
    apply Middle.left_pair (fun a => mapSite η (f a)) d 0 p
    intro a _ ha
    simpa only [Nat.zero_add,mapSite,PathSite.weight,map_mul] using hd a (by omega)
  have px := pair φ v hv
  have py := pair ψ w hw
  have hs : x.boundaryPair.1 = y.boundaryPair.1 :=
    (congrArg Prod.fst px).trans ((map_jet_eq_stationary.mpr hS).trans (congrArg Prod.fst py).symm)
  have hh := map_jet_eq_stationary.mpr hV
  change (edgeMinor f p).map φ = (edgeMinor f p).map ψ at hh
  simp only [edgeMinor,Polynomial.map_mul,map_C] at hh
  have he : C (v p : DualNumber ℝ) * x.boundaryPair.2 = C (w p : DualNumber ℝ) * y.boundaryPair.2 := by
    rw [hv p le_rfl,hw p le_rfl,show x.boundaryPair.2 = _ from congrArg Prod.snd px,
      show y.boundaryPair.2 = _ from congrArg Prod.snd py]
    exact hh
  obtain ⟨hb,hxy⟩ := PrefixExtension.recover_prefix_coordinates (v p) (w p) x y hs he
  obtain ⟨dd,de⟩ := Middle.left_inj _ _ _ _ _ _ hxy
  constructor
  · intro a ha
    exact jet_eq_stationary.mp (by simpa using dd a ha)
  · intro a ha
    apply jet_eq_stationary.mp
    rw [← hv a ha,← hw a ha]
    by_cases h : a = p
    · simpa [h] using congrArg Units.val hb
    · simpa using congrArg Units.val (de a (by omega))

private theorem first {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : ℝ → U × V} {y : U × V}
    (h : HasDerivAt f y 0) : HasDerivAt (fun t => (f t).1) y.1 0 :=
  (ContinuousLinearMap.fst ℝ U V).hasFDerivAt.comp_hasDerivAt 0 h

private theorem second {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : ℝ → U × V} {y : U × V}
    (h : HasDerivAt f y 0) : HasDerivAt (fun t => (f t).2) y.2 0 :=
  (ContinuousLinearMap.snd ℝ U V).hasFDerivAt.comp_hasDerivAt 0 h

set_option maxHeartbeats 650000 in
open EndpointThreshold in
/-- The full change from directed physical rates to sampled prefix polynomials
and the independent tail diagonals and weights has injective Fréchet derivative
at every real point with all directed edges nonzero, for every leak. -/
theorem coordinates_rank {m} (ℓ : Chamber m) (p n : ℕ) (hm : p+1+n=m)
    (z : Fin (p+1) → ℝ) (hz : Function.Injective z) (S : ℝ[X]) (x : Params m)
    (hab : ∀ a : Fin m, x (fwd a) ≠ 0 ∧ x (back a) ≠ 0) :
    Function.Injective (fderiv ℝ (coordinates ℓ p n z S) x) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro v hv
  change fderiv ℝ (coordinates ℓ p n z S) x v = 0 at hv
  have dd := ((coordinates_smooth ℓ p n z S).differentiable le_rfl x).hasFDerivAt
  have hline : HasDerivAt (fun t => coordinates ℓ p n z S (line x v t)) 0 0 := by
    simpa only [Function.comp_def,hv] using dd.comp_hasDerivAt_of_eq 0 (line_derivative x v)
      (by simp [line])
  let f := rawSite ℓ x v
  have sw (r : ℕ) (t : ℝ) : (f r).weight.eval t = (physicalSite ℓ (line x v t) r).weight := by
    simpa only [f,atSite,mapSite,PathSite.weight,eval_mul] using congrArg PathSite.weight (eval_raw ℓ x v r t)
  have sd (r : ℕ) (t : ℝ) : (f r).diag.eval t = (physicalSite ℓ (line x v t) r).diag :=
    congrArg PathSite.diag (eval_raw ℓ x v r t)
  have valS (q : ℕ) (t : ℝ) : value t (leading f q) = leading (physicalSite ℓ (line x v t)) q :=
    raw_segment ℓ x v 0 q t
  have valV (t : ℝ) : value t (edgeMinor f p) = edgeMinor (physicalSite ℓ (line x v t)) p := by
    change (C (f p).weight * leading f p).map (evalRingHom t) = _
    rw [Polynomial.map_mul,map_C]
    exact congrArg₂ (· * ·) (congrArg C (sw p t)) (valS p t)
  have hs : velocity 0 (leading f (p+1)) = 0 := by
    apply eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hz.injOn
    · have h := degree_velocity_lt 0 (p:=leading f (p+1)) (Matrix.charpoly_monic _)
      rw [show value 0 (leading f (p+1)) = leading (physicalSite ℓ (line x v 0)) (p+1) from valS _ _,
        degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero,leading,intervalCharpoly_natDegree,sitesFrom_length] at h
      simpa only [Finset.card_univ,Fintype.card_fin] using h
    · intro a _
      have dh := hasDerivAt_pi.mp (first hline) a
      have dh' : HasDerivAt (fun t : ℝ => (leading (physicalSite ℓ (line x v t)) (p+1)).eval (z a)) 0 0 := by
        simpa only [coordinates,eval_sub,sub_add_cancel,Pi.zero_apply,Prod.fst_zero] using dh.add_const (S.eval (z a))
      exact (eval_has_derivative (z a) 0 (leading f (p+1))).unique (by simpa only [valS] using dh')
  have ha : (edgeMinor f p).natDegree ≤ p :=
    (natDegree_C_mul_le _ _).trans (by rw [leading,intervalCharpoly_natDegree,sitesFrom_length])
  have he : velocity 0 (edgeMinor f p) = 0 := by
    apply eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hz.injOn
    · rw [Finset.card_univ,Fintype.card_fin,degree_lt_iff_coeff_zero]
      intro r hr
      simp only [coeff_velocity, coeff_eq_zero_of_natDegree_lt (p:=edgeMinor f p) (ha.trans_lt (by omega : p<r)),
        derivative_zero,eval_zero]
    · intro a _
      have dh := hasDerivAt_pi.mp (first (second hline)) a
      exact (eval_has_derivative (z a) 0 (edgeMinor f p)).unique (by simpa only [valV] using dh)
  have hreg (a) (h : a ≤ p) : (f a).weight.eval 0 ≠ 0 := by
    have h' : a<m := by omega
    rw [sw]
    simpa [line,physicalSite,PathSite.weight,h'] using mul_ne_zero (hab ⟨a,h'⟩).2 (hab ⟨a,h'⟩).1
  obtain ⟨hdiag,hweight⟩ := prefix_velocity_rigid f p 0 hreg hs he
  apply Closed.original_variation_zero ℓ x v hab
  · intro a
    by_cases hp : a.val ≤ p
    · have d := (f a.val).diag.hasDerivAt (0:ℝ)
      simpa only [sd,hdiag a.val hp,physicalSite,dif_pos a.isLt,line] using d
    · have h := a.isLt
      let k : Fin (n+1) := ⟨a.val-(p+1),by omega⟩
      have hk : p+1+k.val = a.val := by dsimp [k]; omega
      have d := hasDerivAt_pi.mp (first (second (second hline))) k
      simpa only [coordinates,tailCoords,hk,physicalSite,dif_pos a.isLt,line,Prod.snd_zero,
        Prod.fst_zero,Pi.zero_apply] using d
  · intro a
    by_cases hp : a.val ≤ p
    · have d := (f a.val).weight.hasDerivAt (0:ℝ)
      rw [hweight a.val hp] at d
      have e (t : ℝ) : (f a.val).weight.eval t = (x+t•v) (fwd a) * (x+t•v) (back a) := by
        rw [sw]; simp only [physicalSite,PathSite.weight,dif_pos a.isLt,line]; exact mul_comm _ _
      simpa only [e] using d
    · have h := a.isLt
      let k : Fin n := ⟨a.val-(p+1),by omega⟩
      have hk : p+1+k.val = a.val := by dsimp [k]; omega
      have d := hasDerivAt_pi.mp (second (second (second hline))) k
      change HasDerivAt (fun t => (physicalSite ℓ (line x v t) (p+1+k.val)).weight) 0 0 at d
      rw [hk] at d
      simpa only [physicalSite,PathSite.weight,dif_pos a.isLt,line,show ∀ t : ℝ,
        (x+t•v) (back a)*(x+t•v) (fwd a) = (x+t•v) (fwd a)*(x+t•v) (back a) from fun _ => mul_comm _ _] using d

end Catenary.PrefixPhysical
