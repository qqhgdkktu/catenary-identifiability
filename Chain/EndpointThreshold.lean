import Chain.EndpointExterior
import Chain.WitnessVariation
import Chain.SignedWitness
import Chain.ClosedDifferential

/-! The physical affine parameter curve and its actual polynomial spectral
motion. Chamber labels in the analytical model start at zero. -/
noncomputable section
namespace Catenary.EndpointThreshold
open Polynomial Continuant Obstruction WitnessVariation
open scoped Polynomial BigOperators

def line {m} (x v : Params m) (t : ℝ) : Params m := x+t • v

theorem line_derivative {m} (x v : Params m) : HasDerivAt (line x v) v 0 := by
  change HasDerivAt (fun t : ℝ => x + t • v) v 0
  simpa only [zero_add,one_smul] using
    (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v)

def lineHom {m} (x v : Params m) : RatePoly m →+* ℝ[X] :=
  MvPolynomial.eval₂Hom C (fun i => C (x i) + X*C (v i))

theorem eval_line {m} (x v : Params m) (t : ℝ) (p : RatePoly m) :
    (lineHom x v p).eval t = MvPolynomial.eval (line x v t) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [lineHom]
  | add p q hp hq => simp only [map_add,eval_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,eval_mul,hp,MvPolynomial.eval_X]
    simp [lineHom,line]
    exact Or.inl (mul_comm _ _)

def rawSite {m} (ℓ : Chamber m) (x v : Params m) (u : ℕ) : PathSite ℝ[X] :=
  mapSite (lineHom x v) (symbolicSite ℓ u)

theorem eval_raw {m} (ℓ : Chamber m) (x v : Params m) (u : ℕ) (t : ℝ) :
    atSite t (rawSite ℓ x v u) = physicalSite ℓ (line x v t) u := by
  rw [← eval_symbolicSite ℓ (line x v t) u]
  simp [atSite,rawSite,mapSite,coe_evalRingHom,eval_line]

def moveDiag {R : Type*} [CommRing R] (z : R) (a : PathSite R) : PathSite R :=
  ⟨a.diag+z,a.upper,a.lower⟩

def make {m} (f : ℕ → PathSite ℝ[X]) (j k : Chamber m) : Motion ℝ :=
  ⟨sitesFrom f 0 j.val, f j.val, sitesFrom f (j.val+1) (k.val-(j.val+1)),
   f k.val, sitesFrom f (k.val+1) (m-k.val)⟩

def motion {m} (ℓ j k : Chamber m) (x v : Params m) (z : ℝ) : Motion ℝ :=
  make (fun u => moveDiag (C z) (rawSite ℓ x v u)) j k

theorem suffix_parts {R : Type*} {m} (f : ℕ → PathSite R) (j k : Chamber m) (hjk : j < k) :
    sitesFrom f (j.val+1) (m-j.val) =
       sitesFrom f (j.val+1) (k.val-(j.val+1)) ++ f k.val ::
          sitesFrom f (k.val+1) (m-k.val) := by
  have hk := k.isLt
  have hj : j.val < k.val := hjk
  have len : (k.val-(j.val+1))+(m-k.val+1)=m-j.val := by omega
  have end_ : j.val+1+(k.val-(j.val+1))=k.val := by omega
  rw [← len, Middle.from_append, end_]
  rfl

theorem total_parts {R : Type*} {m} (f : ℕ → PathSite R) (j k : Chamber m) (hjk : j < k) :
    sitesFrom f 0 (m+1) =
      sitesFrom f 0 j.val ++ f j.val :: (sitesFrom f (j.val+1) (k.val-(j.val+1)) ++
        f k.val :: sitesFrom f (k.val+1) (m-k.val)) := by
  have hj := j.isLt
  calc
    _ = sitesFrom f 0 (j.val+(m-j.val+1)) := congrArg (sitesFrom f 0) (by omega)
    _ = _ := by rw [Middle.from_append, Nat.zero_add]; simp only [sitesFrom, suffix_parts f j k hjk]

theorem prefix_parts {R : Type*} {m} (f : ℕ → PathSite R) (j k : Chamber m) (hjk : j < k) :
    sitesFrom f 0 k.val =
      sitesFrom f 0 j.val ++ f j.val :: sitesFrom f (j.val+1) (k.val-(j.val+1)) := by
  have hj : j.val < k.val := hjk
  calc
    _ = sitesFrom f 0 (j.val+(k.val-(j.val+1)+1)) := congrArg (sitesFrom f 0) (by omega)
    _ = _ := by rw [Middle.from_append, Nat.zero_add]; rfl

theorem raw_segment {m} (ℓ : Chamber m) (x v : Params m) (u q : ℕ) (t : ℝ) :
    value t (intervalCharpoly (sitesFrom (rawSite ℓ x v) u q)) =
      intervalCharpoly (sitesFrom (physicalSite ℓ (line x v t)) u q) := by
  rw [value_interval, sitesFrom_map]
  simp only [eval_raw]

theorem raw_values {m} (ℓ j k : Chamber m) (x v : Params m) (hjk : j < k) (t : ℝ) :
    let b := make (rawSite ℓ x v) j k
    value t b.D = Middle.full ℓ (line x v t) ∧
      value t b.W = Middle.suffix ℓ (line x v t) j.val ∧
      value t b.U = Middle.suffix ℓ (line x v t) k.val ∧
      (value t b.E).eval 0 = Closed.pref ℓ (line x v t) j.val ∧
      (value t b.H).eval 0 = Closed.pref ℓ (line x v t) k.val := by
  let f := rawSite ℓ x v
  have suffix_ (c : Chamber m) : Middle.suffix ℓ (line x v t) c.val =
      intervalCharpoly (sitesFrom (physicalSite ℓ (line x v t)) (c.val+1) (m-c.val)) := by
    unfold Middle.suffix physicalSites
    rw [Middle.drop_from _ _ _ _ c.isLt]
    simp
  change value t (intervalCharpoly (sitesFrom f 0 j.val ++ f j.val ::
      (sitesFrom f (j.val+1) (k.val-(j.val+1)) ++ f k.val :: sitesFrom f (k.val+1) (m-k.val)))) = _ ∧ _
  rw [← total_parts f j k hjk, raw_segment]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · change value t (intervalCharpoly (sitesFrom f (j.val+1) (k.val-(j.val+1)) ++ f k.val ::
      sitesFrom f (k.val+1) (m-k.val))) = _
    rw [← suffix_parts f j k hjk, raw_segment, suffix_]
  · exact (raw_segment ℓ x v _ _ t).trans (suffix_ k).symm
  · exact congrArg (Polynomial.eval 0) (raw_segment ℓ x v 0 j.val t)
  · change (value t (intervalCharpoly (sitesFrom f 0 j.val ++ f j.val ::
      sitesFrom f (j.val+1) (k.val-(j.val+1))))).eval 0 = _
    rw [← prefix_parts f j k hjk, raw_segment, Closed.pref]

theorem gain_prod {m} (ℓ a : Chamber m) (x : Params m) :
    EndpointExterior.gain ℓ a x = ∏ r ∈ Finset.range a.val, PhysicalInverse.a x r := by
  unfold EndpointExterior.gain physicalSites
  rw [sitesFrom_take _ _ _ _ a.isLt.le]
  generalize a.val = n
  induction n with
  | zero => simp [sitesFrom,pathGain]
  | succ n ih =>
    rw [Closed.sites_snoc,Finset.prod_range_succ]
    simpa [pathGain,physicalSite,PhysicalInverse.a] using
      congrArg (fun z => z*PhysicalInverse.a x n) ih

theorem actual_derivative {m} (ℓ j k : Chamber m) (x v : Params m)
    (h : fderiv ℝ (polynomialValues (coordinatePolynomial ℓ 0 j k)) x v = 0) :
    HasDerivAt (fun t => flatten (physicalData ℓ 0 j k (line x v t))) 0 0 := by
  let P := coordinatePolynomial ℓ 0 j k
  have hd : DifferentiableAt ℝ (polynomialValues P) x :=
    differentiableAt_pi.mpr fun s => (polynomial_eval_contDiff (P s)).differentiable
      (by norm_num) x
  have hzero : line x v 0 = x := by simp [line]
  have hd' : DifferentiableAt ℝ (polynomialValues P) (line x v 0) := hzero.symm ▸ hd
  have he := hd'.hasFDerivAt.comp_hasDerivAt (0:ℝ) (line_derivative x v)
  unfold Function.comp at he
  have eqv (a : Params m) : polynomialValues (coordinatePolynomial ℓ 0 j k) a =
      flatten (physicalData ℓ 0 j k a) := eval_coordinatePolynomial ℓ 0 j k a
  simpa only [P, eqv, hzero, h] using he

private theorem zero_velocity {p : Family ℝ} (hp : p.Monic) {n : ℕ} (hn : p.natDegree = n)
    (h : ∀ c : Fin n, HasDerivAt (fun t => (value t p).coeff c.val) 0 0) :
    velocity 0 p = 0 := by
  ext u
  rw [coeff_zero]
  by_cases hu : u < n
  · exact (coefficient_hasDerivAt 0 p u).unique (h ⟨u,hu⟩)
  · apply coeff_eq_zero_of_degree_lt
    apply (degree_velocity_lt 0 hp).trans_le
    rw [value,hp.degree_map,degree_eq_natDegree hp.ne_zero,hn]
    exact_mod_cast Nat.le_of_not_lt hu

theorem kernel_data {m} (ℓ j k : Chamber m) (x v : Params m) (hjk : j < k)
    (h : fderiv ℝ (polynomialValues (coordinatePolynomial ℓ 0 j k)) x v = 0) :
    let b := make (rawSite ℓ x v) j k
    velocity 0 b.D = 0 ∧ velocity 0 b.W = 0 ∧ velocity 0 b.U = 0 ∧
      HasDerivAt (fun t => ∏ r ∈ Finset.range j.val, PhysicalInverse.a (line x v t) r) 0 0 ∧
      HasDerivAt (fun t => ∏ r ∈ Finset.range k.val, PhysicalInverse.a (line x v t) r) 0 0 := by
  let f := rawSite ℓ x v
  let b := make f j k
  have vals := raw_values ℓ j k x v hjk
  have der := hasDerivAt_pi.mp (actual_derivative ℓ j k x v h)
  have hj : j.val < k.val := hjk
  have hk := k.isLt
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply zero_velocity (Matrix.charpoly_monic _) (n:=m+1)
    · change (intervalCharpoly (sitesFrom f 0 j.val ++ f j.val ::
        (sitesFrom f (j.val+1) (k.val-(j.val+1)) ++ f k.val :: sitesFrom f (k.val+1) (m-k.val)))).natDegree = _
      rw [← total_parts _ _ _ hjk, intervalCharpoly_natDegree, sitesFrom_length]
    · intro c
      simpa only [fun t => (vals t).1] using der (.inl c)
  · apply zero_velocity (Matrix.charpoly_monic _) (n:=m+1-(j.val+1))
    · change (intervalCharpoly (sitesFrom f (j.val+1) (k.val-(j.val+1)) ++ f k.val ::
        sitesFrom f (k.val+1) (m-k.val))).natDegree = _
      rw [← suffix_parts _ _ _ hjk, intervalCharpoly_natDegree, sitesFrom_length]
      omega
    · intro c
      simpa only [fun t => (vals t).2.1] using der (.inr (.inr (.inl c)))
  · apply zero_velocity (Matrix.charpoly_monic _) (n:=m+1-(k.val+1))
    · change (intervalCharpoly (sitesFrom f (k.val+1) (m-k.val))).natDegree = _
      rw [intervalCharpoly_natDegree, sitesFrom_length]
      omega
    · intro c
      simpa only [fun t => (vals t).2.2.1] using der (.inr (.inr (.inr (.inl c))))
  · simp_rw [← gain_prod ℓ j]
    simpa [physicalData,siteData,flatten,EndpointExterior.gain] using der (.inr (.inr (.inr (.inr false))))
  · simp_rw [← gain_prod ℓ k]
    simpa [physicalData,siteData,flatten,EndpointExterior.gain] using der (.inr (.inr (.inr (.inr true))))

/-- Moving every diagonal by z translates the spectral variable by −z. -/
theorem translated_slice (s z : ℝ) (xs : List (PathSite ℝ[X])) :
    slice s (intervalCharpoly (xs.map (moveDiag (C z)))) = slice (s-z) (intervalCharpoly xs) := by
  rw [slice_interval,slice_interval,List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp [moveDiag,shiftedSite,Function.comp_def]
  ring

def shiftSites (z : ℝ) (f : ℕ → PathSite ℝ[X]) (n : ℕ) := moveDiag (C z) (f n)

theorem translated_eval_velocity (s z : ℝ) (f : ℕ → PathSite ℝ[X]) (u n : ℕ) :
    (velocity 0 (intervalCharpoly (sitesFrom (shiftSites z f) u n))).eval s =
      (velocity 0 (intervalCharpoly (sitesFrom f u n))).eval (s-z) := by
  rw [velocity_eval,velocity_eval]
  have hm := sitesFrom_map (moveDiag (C z)) f u n
  rw [show sitesFrom (shiftSites z f) u n = (sitesFrom f u n).map (moveDiag (C z)) from hm.symm,
    translated_slice]

private theorem interval_step {R : Type*} [CommRing R] (a b : PathSite R) (xs : List (PathSite R)) :
    intervalCharpoly (a::b::xs) = (X-C a.diag)*intervalCharpoly (b::xs) -
       C a.weight*intervalCharpoly xs := by
  simp only [intervalCharpoly,charpoly_eq_cont,List.map_cons,cont_cons_cons,pencil_weight]; rfl

private theorem separated_segment {m} (f : ℕ → PathSite ℝ)
    (hd : ∀ c : Chamber m, (f c.val).diag = (Spectral.site (c.val+1)).diag)
    (hw : ∀ c : Fin m, (f c.val).weight = 1) (u q : ℕ) (hn : u+q ≤ m+1) :
    intervalCharpoly (sitesFrom f u q) = Spectral.block (List.range' (u+1) q) := by
  induction q using Nat.strong_induction_on generalizing u with
  | h q ih =>
    cases q with
    | zero => exact (charpoly_eq_cont _).trans (by simp [sitesFrom])
    | succ q =>
      cases q with
      | zero =>
        change intervalCharpoly [f u] = Spectral.block [u+1]
        rw [Spectral.block_one]
        exact (charpoly_eq_cont _).trans (by simp [pencilSite,hd ⟨u,by omega⟩])
      | succ q =>
        have e₁ := ih (q+1) (by omega) (u+1) (by omega)
        have e₂ := ih q (by omega) (u+2) (by omega)
        change intervalCharpoly (f u :: f (u+1) :: sitesFrom f (u+2) q) =
          Spectral.block ((u+1)::(u+2)::List.range' (u+3) q)
        rw [interval_step,Spectral.block_step,hw ⟨u,by omega⟩,hd ⟨u,by omega⟩]
        change _*intervalCharpoly (sitesFrom f (u+1) (q+1)) - _ = _
        rw [e₁,e₂]
        simp [Spectral.site,List.range'_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem segment_at_eigen {m} (f : ℕ → PathSite ℝ[X]) (z : ℝ)
    (hd : ∀ c : Chamber m, (f c.val).diag.eval 0 = -(z+10*((c.val:ℝ)+1)))
    (hw : ∀ c : Fin m, (f c.val).weight.eval 0 = 1) (u q : ℕ) (hn : u+q ≤ m+1) :
    value 0 (intervalCharpoly (sitesFrom (shiftSites z f) u q)) =
      Spectral.block (List.range' (u+1) q) := by
  rw [value_interval, sitesFrom_map]
  apply separated_segment (m:=m) _ _ _ _ _ hn
  · intro c
    simp [atSite, mapSite, shiftSites, moveDiag, Spectral.site, hd c]
  · intro c
    exact (by simpa [atSite,mapSite,shiftSites,moveDiag,PathSite.weight] using hw c)

theorem polynomials_of_make {m} (f : ℕ → PathSite ℝ[X]) (j k : Chamber m) (hjk : j < k) :
    let b := make f j k
    b.D = intervalCharpoly (sitesFrom f 0 (m+1)) ∧
      b.W = intervalCharpoly (sitesFrom f (j.val+1) (m-j.val)) ∧
      b.H = intervalCharpoly (sitesFrom f 0 k.val) := by
  exact ⟨congrArg intervalCharpoly (total_parts f j k hjk).symm,
    congrArg intervalCharpoly (suffix_parts f j k hjk).symm,
    congrArg intervalCharpoly (prefix_parts f j k hjk).symm⟩

private theorem sites_member {R : Type*} (f : ℕ → PathSite R) (u n : ℕ) (a : PathSite R) :
    a ∈ sitesFrom f u n ↔ ∃ k, u ≤ k ∧ k<u+n ∧ a=f k := by
  induction n generalizing u with
  | zero => simp [sitesFrom]; omega
  | succ n ih =>
    rw [sitesFrom,List.mem_cons,ih]
    constructor
    · rintro (h|⟨k,h₁,h₂,h₃⟩)
      · exact ⟨u,by omega,by omega,h⟩
      · exact ⟨k,by omega,by omega,h₃⟩
    · rintro ⟨k,h₁,h₂,h₃⟩
      by_cases he : k=u
      · exact Or.inl (he ▸ h₃)
      · exact Or.inr ⟨k,by omega,by omega,h₃⟩

/-- The common spectral root works for arbitrary polynomial motions of the
original normalized or directed Jacobi coordinates. At this root the shifted
spectra are those of the single separated reference matrix. -/
theorem shift_recovery {m} (j k : Chamber m) (hj : 0 < j.val) (hjk : j < k)
    (small : j.val ≤ m-k.val+2) :
    ∃ z, (Spectral.block (List.range' 1 (m+1))).eval z = 0 ∧
      ∀ f : ℕ → PathSite ℝ[X],
        (∀ c : Chamber m, (f c.val).diag.eval 0 = -(z+10*((c.val:ℝ)+1))) →
        (∀ r : Fin m, (f r.val).weight.eval 0=1) →
        let b := make f j k
        velocity 0 b.D=0 → velocity 0 b.W=0 → velocity 0 b.U=0 →
        (velocity 0 b.E).eval 0=0 → (velocity 0 b.H).eval 0=0 →
        (∀ c : Chamber m, (f c.val).diag.derivative.eval 0=0) ∧
          (∀ r : Fin m, (f r.val).weight.derivative.eval 0=0) := by
  classical
  let g := k.val-(j.val+1)
  let r := m-k.val
  let L := List.range' 1 j.val
  let M := List.range' (j.val+2) g
  let T := List.range' (k.val+2) r
  have jk : j.val < k.val := hjk
  have hk := k.isLt
  have hm : j.val+2+g=k.val+1 := by dsimp [g]; omega
  have hlen : g+(r+1)=m-j.val := by dsimp [g,r]; omega
  have ht : List.range' (j.val+2) (m-j.val) = M ++ (k.val+1)::T := by
    rw [← hlen, ← List.range'_append_1, hm]
    simp only [List.range'_succ, M, T]
  have hfull : List.range' 1 (m+1) = L ++ (j.val+1)::(M ++ (k.val+1)::T) := by
    rw [SpectralPhysical.split_tags j, ht]
  obtain ⟨z, hz, hall⟩ := common_root_recovers_entries L M T (j.val+1) (k.val+1)
    (hfull ▸ List.nodup_range' (s:=1) (n:=m+1)) (by simpa [L] using hj)
    (by simpa [L,T,r] using small)
  refine ⟨z,?_,?_⟩
  · rw [hfull]
    exact isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz)
  intro f hd hw b hD hW hU hE hH
  let sf := shiftSites z f
  let c := make sf j k
  obtain ⟨d₀,w₀,h₀⟩ := polynomials_of_make f j k hjk
  obtain ⟨dz,wz,hz'⟩ := polynomials_of_make sf j k hjk
  have seg := segment_at_eigen f z hd hw
  have sd : value 0 c.D = Spectral.block (L++(j.val+1)::(M++(k.val+1)::T)) := by
    rw [show c.D = _ from dz,←hfull]
    exact seg 0 (m+1) (by omega)
  have sw : value 0 c.W = Spectral.block (M++(k.val+1)::T) := by
    rw [show c.W = _ from wz,←ht]
    exact seg (j.val+1) (m-j.val) (by omega)
  have sb : value 0 c.B = Spectral.block M := seg (j.val+1) g (by dsimp [g]; omega)
  have su : value 0 c.U = Spectral.block T := seg (k.val+1) r (by dsimp [r]; omega)
  have se : value 0 c.E = Spectral.block L := seg 0 j.val (by omega)
  have ed (u n : ℕ) (hn : u+n ≤ m) :
      (edgeProduct (sitesFrom sf u n)).eval 0 = 1 := by
    induction n generalizing u with
    | zero => simp [sitesFrom,edgeProduct]
    | succ n ih =>
      change ((sf u).weight * edgeProduct (sitesFrom sf (u+1) n)).eval 0 = 1
      rw [eval_mul, ih (u+1) (by omega)]
      simpa only [mul_one] using hw ⟨u,by omega⟩
  have sk : c.K.eval 0 = 1 := by
    change ((sf j.val).weight * edgeProduct (sitesFrom sf (j.val+1) g)).eval 0 = 1
    rw [eval_mul,ed _ _ (by dsimp [g]; omega),mul_one]
    exact hw ⟨j.val,by omega⟩
  have ls : c.sites = sitesFrom sf 0 (m+1) := (total_parts sf j k hjk).symm
  have ls' : c.sites.dropLast = sitesFrom sf 0 m := by rw [ls,Closed.sites_snoc]; simp
  have units_ (a : PathSite ℝ[X]) (ha : a ∈ c.sites.dropLast) : a.weight.eval 0 ≠ 0 := by
    rw [ls', sites_member] at ha
    obtain ⟨u,_,hu,rfl⟩ := ha
    exact (hw ⟨u,by omega⟩).trans_ne one_ne_zero
  have zh (u n : ℕ) (h : velocity 0 (intervalCharpoly (sitesFrom f u n))=0) :
      velocity 0 (intervalCharpoly (sitesFrom sf u n))=0 := by
    apply Polynomial.funext
    intro s
    rw [translated_eval_velocity, h]
    simp
  change velocity 0 (make f j k).D = 0 at hD
  change velocity 0 (make f j k).W = 0 at hW
  change (velocity 0 (make f j k).H).eval 0 = 0 at hH
  rw [d₀] at hD
  rw [w₀] at hW
  rw [h₀] at hH
  have cD : velocity 0 c.D=0 := by rw [show c.D=_ from dz]; exact zh _ _ hD
  have cW : velocity 0 c.W=0 := by rw [show c.W=_ from wz]; exact zh _ _ hW
  have cE : (velocity 0 c.E).eval z=0 := by
    simpa only [sub_self] using (translated_eval_velocity z z f 0 j.val).trans
      (by simpa only [sub_self] using hE)
  have cH : (velocity 0 c.H).eval z=0 := by
    rw [show c.H=_ from hz',translated_eval_velocity,sub_self]
    exact hH
  obtain ⟨diag,edge⟩ := hall c 0 units_ sd sb sw su se sk cD cW (zh _ _ hU) cE cH
  constructor
  · intro i
    have a := diag (sf i.val) (by rw [ls,sites_member]; exact ⟨i.val,by omega,by simp,rfl⟩)
    simpa [sf,shiftSites,moveDiag] using a
  · intro i
    exact edge (sf i.val) (by rw [ls',sites_member]; exact ⟨i.val,by omega,by simp,rfl⟩)

theorem eval_slice (z t : ℝ) (p : Family ℝ) : (slice z p).eval t = (value t p).eval z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [slice,value,eval_add,Polynomial.map_add] using congrArg₂ (·+·) hp hq
  | monomial n a => simp [slice,value,eval_monomial]

theorem eval_has_derivative (z t : ℝ) (p : Family ℝ) :
    HasDerivAt (fun u => (value u p).eval z) ((velocity t p).eval z) t := by
  simpa only [eval_slice] using slice_hasDerivAt t z p

private theorem physical_diagonal {m} (ℓ : Chamber m) (x v : Params m) (c : Chamber m) (t : ℝ) :
    (rawSite ℓ x v c.val).diag.eval t = generator ℓ (line x v t) c c := by
  simpa [atSite,mapSite,physicalSite,c.isLt] using congrArg PathSite.diag (eval_raw ℓ x v c.val t)

private theorem physical_product {m} (ℓ : Chamber m) (x v : Params m) (r : Fin m) (t : ℝ) :
    (rawSite ℓ x v r.val).weight.eval t = (line x v t) (fwd r)*(line x v t) (back r) := by
  have h := congrArg (fun s : PathSite ℝ => s.weight) (eval_raw ℓ x v r.val t)
  rw [mul_comm]
  simpa [atSite,mapSite,physicalSite,PathSite.weight,r.isLt] using h

/-- All placements satisfying d≤r+2 at a left end inlet have generically
locally identifiable positive physical rates, for every possible leak site. -/
theorem generic_endpoint_threshold {m} (ℓ j k : Chamber m)
    (hj : 0 < j.val) (hjk : j < k) (small : j.val ≤ m-k.val+2) :
    GenericLocalID 0 j k ℓ := by
  obtain ⟨z,hz,hrigid⟩ := shift_recovery j k hj hjk small
  let x := Closed.eigenRates m z
  obtain ⟨hclosed,hd,hed⟩ := Closed.eigen_witness ℓ z hz
  have edges (r : Fin m) : x (fwd r) ≠ 0 ∧ x (back r) ≠ 0 := ⟨(hed r).1,(hed r).2.1⟩
  let A := fderiv ℝ (polynomialValues (coordinatePolynomial ℓ 0 j k)) x
  have ker (v : Params m) (hv : A v = 0) : v = 0 := by
    let f := rawSite ℓ x v
    let b := make f j k
    obtain ⟨hD,hW,hU,hG,hG'⟩ := kernel_data ℓ j k x v hjk hv
    have values := raw_values ℓ j k x v hjk
    have hline : line x v 0 = x := by simp [line]
    have hd' (c : Chamber m) : (f c.val).diag.eval 0 = -(z+10*((c.val:ℝ)+1)) := by
      rw [show (f c.val).diag.eval 0 = _ from physical_diagonal ℓ x v c 0, hline]
      exact hd c
    have he' (r : Fin m) : (f r.val).weight.eval 0 = 1 := by
      rw [show (f r.val).weight.eval 0 = _ from physical_product ℓ x v r 0, hline]
      exact (hed r).2.2
    have determinant (t : ℝ) : (value t b.D).eval 0 = Closed.pref ℓ (line x v t) (m+1) :=
      congrArg (Polynomial.eval 0) (values t).1
    have eD := eval_has_derivative 0 0 b.D
    have dhD : velocity 0 b.D = 0 := hD
    have hzero : HasDerivAt (fun t : ℝ => Closed.pref ℓ (x+t•v) (m+1)) 0 0 := by
      simpa only [determinant,dhD,eval_zero,line] using eD
    have hleak := Closed.loss_variation ℓ x v hclosed edges hzero
    have near := Closed.prefix_variation ℓ x v hclosed hleak j.val j.isLt.le hG
    have far := Closed.prefix_variation ℓ x v hclosed hleak k.val k.isLt.le hG'
    have eE : (velocity 0 b.E).eval 0 = 0 := by
      have he (t : ℝ) : (value t b.E).eval 0 = Closed.pref ℓ (x+t•v) j.val :=
        (values t).2.2.2.1
      apply (eval_has_derivative 0 0 b.E).unique
      simpa only [he] using near
    have eH : (velocity 0 b.H).eval 0 = 0 := by
      have he (t : ℝ) : (value t b.H).eval 0 = Closed.pref ℓ (x+t•v) k.val :=
        (values t).2.2.2.2
      apply (eval_has_derivative 0 0 b.H).unique
      simpa only [he] using far
    obtain ⟨hdiag,hweights⟩ := hrigid f hd' he' hD hW hU eE eH
    apply Closed.original_variation_zero ℓ x v edges
    · intro c
      have h := (f c.val).diag.hasDerivAt (0:ℝ)
      simpa only [hdiag c, f, physical_diagonal, line] using h
    · intro r
      have h := (f r.val).weight.hasDerivAt (0:ℝ)
      simpa only [hweights r, f, physical_product, line] using h
  apply EndpointExterior.generic_of_observed_rank_somewhere ℓ j k x
  intro v w he
  apply sub_eq_zero.mp
  apply ker
  rw [map_sub,show A v = A w from he,sub_self]

end Catenary.EndpointThreshold
