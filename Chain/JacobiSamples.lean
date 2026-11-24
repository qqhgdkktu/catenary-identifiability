import Chain.EndpointThreshold

/-! Finite, differentiable observations of normalized diagonal and edge-product
coordinates. The same spectral root works for every set of distinct sample points. -/
noncomputable section
open Polynomial Catenary.Continuant Catenary.WitnessVariation
open scoped Polynomial
namespace Catenary.JacobiSamples

abbrev Coords (m : ℕ) := (Chamber m → ℝ) × (Fin m → ℝ)
abbrev Row (m : ℕ) := Fin (m+2) ⊕ Bool
abbrev Side (m : ℕ) := Bool × Fin (m+2)

def site {m} (x : Coords m) (u : ℕ) : PathSite ℝ :=
  ⟨if h : u<m+1 then x.1 ⟨u,h⟩ else 0, if h : u<m then x.2 ⟨u,h⟩ else 1, 1⟩

def seg {m} (x : Coords m) (u q : ℕ) (s : ℝ) : ℝ :=
  (intervalCharpoly (sitesFrom (site x) u q)).eval s

def data {m} (j k : Chamber m) (s : Fin (m+2) → ℝ) (x : Coords m) :
    (Row m → ℝ) × (Side m → ℝ) :=
  (Sum.elim (fun a => seg x 0 (m+1) (s a)) (fun b => seg x 0 (if b then k.val else j.val) 0),
    fun a => if a.1 then seg x (k.val+1) (m-k.val) (s a.2)
             else seg x (j.val+1) (m-j.val) (s a.2))

def base (m : ℕ) (z : ℝ) : Coords m :=
  (fun c => -(z+10*((c.val:ℝ)+1)), fun _ => 1)

def path {m} (x w : Coords m) (u : ℕ) : PathSite ℝ[X] :=
  ⟨if h : u<m+1 then C (x.1 ⟨u,h⟩)+X*C (w.1 ⟨u,h⟩) else 0,
   if h : u<m then C (x.2 ⟨u,h⟩)+X*C (w.2 ⟨u,h⟩) else 1, 1⟩

theorem at_path {m} (x w : Coords m) (u : ℕ) (t : ℝ) :
    atSite t (path x w u) = site (x+t • w) u := by
  by_cases h : u<m+1 <;> by_cases h' : u<m <;>
    simp [atSite,Obstruction.mapSite,path,site,h,h',Prod.fst_add,Prod.snd_add,smul_eq_mul] <;> first | exact ⟨mul_comm _ _, mul_comm _ _⟩ | exact mul_comm _ _

theorem value_path {m} (x w : Coords m) (u q : ℕ) (s t : ℝ) :
    (value t (intervalCharpoly (sitesFrom (path x w) u q))).eval s = seg (x+t • w) u q s := by
  rw [value_interval,sitesFrom_map]
  simp only [at_path,seg]

theorem seg_line {m} (x w : Coords m) (u q : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => seg (x+t • w) u q s)
      ((velocity 0 (intervalCharpoly (sitesFrom (path x w) u q))).eval s) 0 := by
  simpa only [value_path] using
    EndpointThreshold.eval_has_derivative s 0 (intervalCharpoly (sitesFrom (path x w) u q))

private theorem smooth_cont {m} (f : Coords m → ℕ → PathSite ℝ)
    (hd : ∀ u, ContDiff ℝ 2 (fun x => (f x u).diag))
    (hw : ∀ u, ContDiff ℝ 2 (fun x => (f x u).weight)) (u q : ℕ) :
    ContDiff ℝ 2 (fun x => cont (sitesFrom (f x) u q)) := by
  induction q using Nat.strong_induction_on generalizing u with
  | h q ih =>
    match q with
    | 0 => exact contDiff_const
    | 1 => simpa only [sitesFrom,cont_singleton] using hd u
    | q+2 =>
      change ContDiff ℝ 2 (fun x => (f x u).diag * cont (sitesFrom (f x) (u+1) (q+1)) -
        (f x u).weight * cont (sitesFrom (f x) ((u+1)+1) q))
      exact ((hd u).mul (ih (q+1) (by omega) (u+1))).sub ((hw u).mul (ih q (by omega) ((u+1)+1)))

theorem seg_smooth {m} (u q : ℕ) (s : ℝ) :
    ContDiff ℝ 2 (fun x : Coords m => seg x u q s) := by
  simp only [seg,Obstruction.interval_eval,sitesFrom_map]
  apply smooth_cont
  · intro t
    by_cases ht : t<m+1
    · simpa [site,shiftedSite,ht] using
        (contDiff_const (c:=s)).sub ((contDiff_pi.mp (contDiff_fst (E:=Chamber m → ℝ) (F:=Fin m → ℝ))) ⟨t,ht⟩)
    · simpa [site,shiftedSite,ht] using (contDiff_const (c:=s) : ContDiff ℝ 2 (fun _ : Coords m => s))
  · intro t
    by_cases ht : t<m
    · simpa [site,shiftedSite,PathSite.weight,ht] using
        ((contDiff_pi.mp (contDiff_snd (E:=Chamber m → ℝ) (F:=Fin m → ℝ))) ⟨t,ht⟩ :
        ContDiff ℝ 2 (fun x : Coords m => x.2 ⟨t,ht⟩))
    · simpa [site,shiftedSite,PathSite.weight,ht] using
        (contDiff_const (c:=(1:ℝ)) : ContDiff ℝ 2 (fun _ : Coords m => (1:ℝ)))

theorem data_smooth {m} (j k : Chamber m) (s : Fin (m+2) → ℝ) : ContDiff ℝ 2 (data j k s) := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    rintro (a|b)
    · exact seg_smooth _ _ _
    · exact seg_smooth _ _ _
  · apply contDiff_pi.mpr
    rintro ⟨b,a⟩
    cases b <;> exact seg_smooth _ _ _

private theorem vel_zero {m} (f : ℕ → PathSite ℝ[X]) (s : Fin (m+2) → ℝ) (hs : Function.Injective s)
    (u q : ℕ) (hq : q≤m+1) (hz : ∀ a, (velocity 0 (intervalCharpoly (sitesFrom f u q))).eval (s a) = 0) :
    velocity 0 (intervalCharpoly (sitesFrom f u q)) = 0 := by
  classical
  let p := intervalCharpoly (sitesFrom f u q)
  let v := velocity (0:ℝ) p
  by_contra hv
  have deg := natDegree_lt_natDegree hv (degree_velocity_lt 0 (Matrix.charpoly_monic _))
  change v.natDegree < (value 0 p).natDegree at deg
  have pd : (value 0 p).natDegree = q := by
    rw [show p = intervalCharpoly (sitesFrom f u q) from rfl,value_interval,intervalCharpoly_natDegree]
    simp
  let roots := Finset.univ.image s
  have card : roots.card = m+2 := by simp [roots,Finset.card_image_of_injective _ hs]
  apply hv
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' v roots
  · intro y hy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hy
    exact hz a
  · omega

private theorem fst_deriv {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {f : ℝ → A × B} {v : A×B}
    (h : HasDerivAt f v 0) : HasDerivAt (fun t => (f t).1) v.1 0 :=
  (ContinuousLinearMap.fst ℝ A B).hasFDerivAt.comp_hasDerivAt 0 h

private theorem snd_deriv {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {f : ℝ → A × B} {v : A×B}
    (h : HasDerivAt f v 0) : HasDerivAt (fun t => (f t).2) v.2 0 :=
  (ContinuousLinearMap.snd ℝ A B).hasFDerivAt.comp_hasDerivAt 0 h

/-- A common signed spectral witness for all distinct finite sampling grids. -/
theorem rank {m} (j k : Chamber m) (hj : 0<j.val) (hjk : j<k) (small : j.val≤m-k.val+2) :
    ∃ z, (Spectral.block (List.range' 1 (m+1))).eval z=0 ∧
      ∀ s : Fin (m+2) → ℝ, Function.Injective s →
        Function.Injective (fderiv ℝ (data j k s) (base m z)) := by
  obtain ⟨z,hz,hr⟩ := EndpointThreshold.shift_recovery j k hj hjk small
  refine ⟨z,hz,?_⟩
  intro s hs
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro w hw
  let x := base m z
  change fderiv ℝ (data j k s) x w = 0 at hw
  have dl : HasDerivAt (fun t : ℝ => x+t • w) w 0 := by
    simpa only [zero_add,one_smul] using
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const w)
  have zd := (((data_smooth j k s).differentiable (by decide)) x).hasFDerivAt.comp_hasDerivAt_of_eq
    0 dl (by simp)
  rw [hw] at zd
  have ha := hasDerivAt_pi.mp (fst_deriv zd)
  have hb := hasDerivAt_pi.mp (snd_deriv zd)
  let f := path x w
  have bp := EndpointThreshold.polynomials_of_make f j k hjk
  dsimp only at bp
  have hd (c : Chamber m) : (f c.val).diag.eval 0 = -(z+10*((c.val:ℝ)+1)) := by
    simp [f,path,x,base,c.isLt]
  have he (r : Fin m) : (f r.val).weight.eval 0=1 := by simp [f,path,x,base,PathSite.weight,r.isLt]
  have rig := hr f hd he
  dsimp only at rig
  have dD : velocity 0 (EndpointThreshold.make f j k).D=0 := by
    rw [bp.1]
    apply vel_zero f s hs _ _ le_rfl
    intro a
    exact (seg_line x w _ _ _).unique (ha (Sum.inl a))
  have dW : velocity 0 (EndpointThreshold.make f j k).W=0 := by
    rw [bp.2.1]
    apply vel_zero f s hs _ _ (by omega)
    intro a
    exact (seg_line x w _ _ _).unique (hb (false,a))
  have dU : velocity 0 (EndpointThreshold.make f j k).U=0 := by
    apply vel_zero f s hs _ _ (by omega)
    intro a
    exact (seg_line x w _ _ _).unique (hb (true,a))
  have dE : (velocity 0 (EndpointThreshold.make f j k).E).eval 0=0 :=
    (seg_line x w _ _ _).unique (ha (Sum.inr false))
  have dH : (velocity 0 (EndpointThreshold.make f j k).H).eval 0=0 := by
    rw [bp.2.2]
    exact (seg_line x w _ _ _).unique (ha (Sum.inr true))
  obtain ⟨dg,ed⟩ := rig dD dW dU dE dH
  apply Prod.ext
  · funext c
    simpa [f,path,c.isLt] using dg c
  · funext c
    simpa [f,path,c.isLt,PathSite.weight] using ed c

/-- Every interval of the translated separated Jacobi witness is obtained by
the same shift of the spectral variable. -/
theorem base_segment {m} (z s : ℝ) (u q : ℕ) (hn : u+q ≤ m+1) :
    seg (base m z) u q s = (Spectral.block (List.range' (u+1) q)).eval (s+z) := by
  let x := base m z
  let f := path x 0
  have hd (c : Chamber m) : (f c.val).diag.eval 0 = -(z+10*((c.val:ℝ)+1)) := by
    simp [f,path,x,base,c.isLt]
  have he (r : Fin m) : (f r.val).weight.eval 0=1 := by simp [f,path,x,base,PathSite.weight,r.isLt]
  have e := EndpointThreshold.segment_at_eigen (m:=m) f z hd he u q hn
  have ev := congrArg (Polynomial.eval (s+z)) e
  rw [← EndpointThreshold.eval_slice] at ev
  have hm := sitesFrom_map (EndpointThreshold.moveDiag (C z)) f u q
  rw [show sitesFrom (EndpointThreshold.shiftSites z f) u q =
      (sitesFrom f u q).map (EndpointThreshold.moveDiag (C z)) from hm.symm,
    EndpointThreshold.translated_slice,add_sub_cancel_right,EndpointThreshold.eval_slice] at ev
  simpa only [f,value_path,zero_smul,add_zero,x] using ev

theorem base_prefix {m} (z : ℝ) (q : ℕ) (hq : q≤m+1) :
    seg (base m z) 0 q 0 = Closed.spectralPrefix z q := by
  simpa only [zero_add,Nat.zero_add,Closed.spectralPrefix] using base_segment (m:=m) z 0 0 q (by omega)

end Catenary.JacobiSamples
