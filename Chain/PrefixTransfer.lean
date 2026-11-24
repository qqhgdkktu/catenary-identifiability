import Chain.PrefixPhysical
import Chain.ExteriorObservations
import Chain.PrefixInstantiation

/-! The observations at a signed closed physical chain, in a finite set of
spectral frequencies. This module only uses actual path determinants. -/
noncomputable section
open Polynomial Filter
open scoped Polynomial Topology
namespace Catenary.PrefixPhysical
open Continuant Obstruction

/-- Directed physical data with the gains replaced by the corresponding
leading minors on a closed chain. The replacement is used for derivatives
at the signed closed point and applies to arbitrary leak placement. -/
def probes {m p n} (ℓ i j k : Chamber m) (nodes : Fin (p+1) → ℝ) (samples : Fin (n+2) → ℝ)
    (x : Params m) : (Fin (p+1) → ℝ) × (Fin (p+1) → ℝ) × (JacobiSamples.Row n → ℝ) ×
      (JacobiSamples.Side n → ℝ) :=
  (fun a => (Middle.prefix ℓ x i.val).eval (nodes a), fun a => (Middle.full ℓ x).eval (nodes a),
   Sum.elim (fun a => (Middle.full ℓ x).eval (samples a))
     (fun b => Closed.pref ℓ x (if b then k.val else j.val)),
   fun a => if a.1 then (Middle.suffix ℓ x k.val).eval (samples a.2)
     else (Middle.suffix ℓ x j.val).eval (samples a.2))

/-- Every physical Jacobian kernel direction annihilates all sampled probes at
a signed point where the leak is zero and all directed edges are nonzero. -/
theorem probes_kernel {m p n} (ℓ i j k : Chamber m) (nodes : Fin (p+1) → ℝ)
    (samples : Fin (n+2) → ℝ) (x v : Params m) (hx : x (loss m)=0)
    (hab : ∀ a : Fin m, x (fwd a) ≠ 0 ∧ x (back a) ≠ 0) (hij : i≤j) (hik : i≤k)
    (hv : fderiv ℝ (polynomialValues (coordinatePolynomial ℓ i j k)) x v = 0) :
    HasDerivAt (fun t : ℝ => probes ℓ i j k nodes samples (x+t•v)) 0 0 := by
  have read := ExteriorObservations.physicalData_kernel_evaluations ℓ i j k x v hv
  obtain ⟨_,hj,hk⟩ := ExteriorObservations.closed_exterior_kernel ℓ i j k x v hx hab hij hik hv
  apply HasDerivAt.prodMk
  · exact hasDerivAt_pi.mpr fun a => (read (nodes a)).2.1
  apply HasDerivAt.prodMk
  · exact hasDerivAt_pi.mpr fun a => (read (nodes a)).1
  apply HasDerivAt.prodMk
  · apply hasDerivAt_pi.mpr
    rintro (a|b)
    · exact (read (samples a)).1
    · cases b
      · exact hj
      · exact hk
  · apply hasDerivAt_pi.mpr
    rintro ⟨b,a⟩
    cases b
    · exact (read (samples a)).2.2.1
    · exact (read (samples a)).2.2.2

/-- Chain rule for the exact physical splice. The sampled observation chart
may be any C¹ realization of the displayed finite physical probes. -/
theorem physical_rank_of_chart {m p n} (ℓ i j k : Chamber m) (hm : p+1+n=m)
    (nodes : Fin (p+1) → ℝ) (hn : Function.Injective nodes) (samples : Fin (n+2) → ℝ)
    (S : ℝ[X]) (x : Params m) (hx : x (loss m)=0)
    (hab : ∀ a : Fin m, x (fwd a) ≠ 0 ∧ x (back a) ≠ 0) (hij : i≤j) (hik : i≤k)
    (F : (Fin (p+1) → ℝ) × (Fin (p+1) → ℝ) × Jac n →
      (Fin (p+1) → ℝ) × (Fin (p+1) → ℝ) × (JacobiSamples.Row n → ℝ) × (JacobiSamples.Side n → ℝ))
    (heq : ∀ y, F (coordinates ℓ p n nodes S y)=probes ℓ i j k nodes samples y)
    (hd : DifferentiableAt ℝ F (coordinates ℓ p n nodes S x))
    (hr : Function.Injective (fderiv ℝ F (coordinates ℓ p n nodes S x))) :
    Function.Injective (fderiv ℝ (polynomialValues (coordinatePolynomial ℓ i j k)) x) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro v hv
  change fderiv ℝ (polynomialValues (coordinatePolynomial ℓ i j k)) x v = 0 at hv
  let c := coordinates ℓ p n nodes S
  have hcv := ((coordinates_smooth ℓ p n nodes S).differentiable le_rfl x).hasFDerivAt
  have hlin := EndpointThreshold.line_derivative x v
  have e₀ : EndpointThreshold.line x v 0 = x := by simp [EndpointThreshold.line]
  have cd := hcv.comp_hasDerivAt_of_eq 0 hlin e₀.symm
  have fd := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 cd (congrArg c e₀).symm
  have dz := probes_kernel ℓ i j k nodes samples x v hx hab hij hik hv
  have hh : fderiv ℝ F (c x) (fderiv ℝ c x v) = 0 := by
    apply fd.unique
    simpa only [Function.comp_def,heq,EndpointThreshold.line] using dz
  apply coordinates_rank ℓ p n hm nodes hn S x hab
  rw [map_zero]
  apply hr
  simpa only [map_zero] using hh

/-- Normalization of directed entries changes no interval characteristic
polynomial whenever each diagonal and every internal edge product agree. -/
theorem interval_of_entries {R : Type*} [CommRing R] (f g : ℕ → PathSite R) (u v q : ℕ)
    (hd : ∀ a, a<q → (f (u+a)).diag=(g (v+a)).diag)
    (hb : ∀ a, a+1<q → (f (u+a)).weight=(g (v+a)).weight) :
    intervalCharpoly (sitesFrom f u q) = intervalCharpoly (sitesFrom g v q) := by
  have one (a : PathSite R) : intervalCharpoly [a] = X-C a.diag :=
    (charpoly_eq_cont _).trans (cont_singleton _)
  have step (a b : PathSite R) (r : List (PathSite R)) : intervalCharpoly (a::b::r) =
      (X-C a.diag)*intervalCharpoly (b::r) - C a.weight*intervalCharpoly r := by
    simp only [intervalCharpoly,charpoly_eq_cont,List.map_cons,cont_cons_cons,pencil_weight]; rfl
  induction q using Nat.strong_induction_on generalizing u v with
  | h q ih =>
    cases q with
    | zero => rfl
    | succ q =>
      cases q with
      | zero => simp only [sitesFrom,one,show (f u).diag=(g v).diag by simpa using hd 0 (by omega)]
      | succ q =>
        have h₁ := ih (q+1) (by omega) (u+1) (v+1)
          (fun a ha => by simpa only [Nat.add_assoc,Nat.add_comm 1 a] using hd (a+1) (by omega))
          (fun a ha => by simpa only [Nat.add_assoc,Nat.add_comm 1 a] using hb (a+1) (by omega))
        have h₂ := ih q (by omega) (u+2) (v+2)
          (fun a ha => by simpa only [Nat.add_assoc,Nat.add_comm 2 a] using hd (a+2) (by omega))
          (fun a ha => by simpa only [Nat.add_assoc,Nat.add_comm 2 a] using hb (a+2) (by omega))
        change intervalCharpoly (f u :: f (u+1) :: sitesFrom f (u+2) q) =
          intervalCharpoly (g v :: g (v+1) :: sitesFrom g (v+2) q)
        rw [step,step,show (f u).diag=(g v).diag by simpa using hd 0 (by omega),
          show (f u).weight=(g v).weight by simpa using hb 0 (by omega),h₂]
        exact congrArg (fun z => (X-C (g v).diag)*z - C (g v).weight*intervalCharpoly (sitesFrom g (v+2) q)) h₁

/-- Normalized tail coordinates represent every true principal submatrix. -/
theorem tail_interval {m n} (ℓ : Chamber m) (x : Params m) (s u q : ℕ) (h : u+q≤n+1) :
    intervalCharpoly (sitesFrom (JacobiSamples.site (tailCoords ℓ x s n)) u q) =
      intervalCharpoly (sitesFrom (physicalSite ℓ x) (s+u) q) := by
  apply interval_of_entries
  · intro a ha
    have h' : u+a<n+1 := by omega
    simp [JacobiSamples.site,tailCoords,h',Nat.add_assoc]
  · intro a ha
    have h' : u+a<n := by omega
    simp [JacobiSamples.site,tailCoords,PathSite.weight,h',Nat.add_assoc]

/-- Exact Schur polynomial identity at an arbitrary nonempty segment of the
tail. It includes the joining bridge weight of the actual unnormalized path. -/
theorem cut_after {R : Type*} [CommRing R] (f : ℕ → PathSite R) (p t : ℕ) :
    leading f (p+1+(t+1)) = leading f (p+1) * intervalCharpoly (sitesFrom f (p+1) (t+1)) -
      edgeMinor f p * intervalCharpoly (sitesFrom f (p+2) t) := by
  have head := Closed.sites_snoc f 0 p
  simp only [Nat.zero_add] at head
  have split : sitesFrom f 0 (p+1+(t+1)) = sitesFrom f 0 p ++ f p :: f (p+1) :: sitesFrom f (p+2) t := by
    rw [Middle.from_append f 0 (p+1) (t+1),Nat.zero_add,head,List.append_assoc]
    rfl
  change intervalCharpoly (sitesFrom f 0 (p+1+(t+1))) = _
  rw [split]
  unfold leading edgeMinor
  rw [head]
  exact charpoly_cut (sitesFrom f 0 p) (sitesFrom f (p+2) t) (f p) (f (p+1))

open PrefixInstantiation in
/-- The actual prefix and tail on the physical parameter domain realize
exactly the finite splice chart, as an identity for every real parameter
vector. Both sensors are strictly inside the retained tail. -/
theorem chart_on_physical {m p n} (ℓ i j k : Chamber m) (a b : Chamber n) (hm : p+1+n=m)
    (hi : i.val=p+1) (hj : j.val=p+1+a.val) (hk : k.val=p+1+b.val) (ha : 0<a.val) (hb : 0<b.val)
    (nodes : Fin (p+1)→ℝ) (hn : Function.Injective nodes) (S : ℝ[X]) (hM : S.Monic)
    (hdegree : S.natDegree=p+1) (hz : ∀ u, S.eval (nodes u)=0) (x : Params m) :
    chart a b nodes S (coordinates ℓ p n nodes S x) = probes ℓ i j k nodes (grid n) x := by
  let f := physicalSite ℓ x
  let s := leading f (p+1)
  let v := edgeMinor f p
  let y := tailCoords ℓ x (p+1) n
  have pr : s.degree = (p+1:ℕ) := by
    rw [show s = intervalCharpoly (sitesFrom f 0 (p+1)) from rfl,
      degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero,intervalCharpoly_natDegree,sitesFrom_length]
  have hs : (s-S).degree < (p+1:ℕ) := by
    rw [← pr]
    apply degree_sub_lt
    · rw [pr,degree_eq_natDegree hM.ne_zero,hdegree]
    · exact (Matrix.charpoly_monic _).ne_zero
    · exact (Matrix.charpoly_monic _).leadingCoeff.trans hM.leadingCoeff.symm
  have hv : v.degree < (p+1:ℕ) := by
    have d : v.natDegree ≤ p := (natDegree_C_mul_le _ _).trans (by rw [leading,intervalCharpoly_natDegree,sitesFrom_length])
    exact (degree_le_natDegree (p:=v)).trans_lt (by exact_mod_cast Nat.lt_succ_of_le d)
  have glued (u : ℕ) (hu : 0<u) (hlen : u≤n+1) :
      s*tailPoly y 0 u - v*tailPoly y 1 (u-1) = leading f (p+1+u) := by
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu)
    simp only [Nat.succ_sub_one,tailPoly]
    rw [tail_interval ℓ x (p+1) 0 (t+1) (by omega),tail_interval ℓ x (p+1) 1 t (by omega)]
    simpa only [Nat.add_zero] using (cut_after f p t).symm
  have full : s*tailPoly y 0 (n+1)-v*tailPoly y 1 n = Middle.full ℓ x := by
    have e := glued (n+1) (by omega) le_rfl
    simpa only [Nat.add_sub_cancel,Nat.succ_sub_one,show p+1+(n+1)=m+1 by omega] using e
  have side (c : Chamber n) (d : Chamber m) (h : d.val=p+1+c.val) :
      tailPoly y (c.val+1) (n-c.val) = Middle.suffix ℓ x d.val := by
    have hcv := c.isLt
    unfold tailPoly Middle.suffix physicalSites
    rw [tail_interval ℓ x (p+1) (c.val+1) (n-c.val) (by omega)]
    rw [Middle.drop_from _ 0 (m+1) (d.val+1) (by have := d.isLt; omega),Nat.zero_add]
    congr 2 <;> omega
  have e := chart_exact a b nodes hn S s v hz hs hv y
  change chart a b nodes S ((fun u => (s-S).eval (nodes u)),(fun u => v.eval (nodes u)),y) = _
  rw [e]
  apply Prod.ext
  · funext u
    change s.eval (nodes u)=(Middle.prefix ℓ x i.val).eval (nodes u)
    unfold Middle.prefix physicalSites
    rw [sitesFrom_take _ _ _ _ i.isLt.le,hi]
  apply Prod.ext
  · funext u
    exact congrArg (Polynomial.eval (nodes u)) full
  apply Prod.ext
  · funext u
    cases u with
    | inl u => exact congrArg (Polynomial.eval (grid n u)) full
    | inr u =>
      cases u with
      | false => simpa only [rowLen,rows,probes,Closed.pref,Sum.elim_inr,Bool.false_eq_true,if_false,hj] using
          congrArg (Polynomial.eval (0:ℝ)) (glued a.val ha a.isLt.le)
      | true => simpa only [rowLen,rows,probes,Closed.pref,Sum.elim_inr,if_true,hk] using
          congrArg (Polynomial.eval (0:ℝ)) (glued b.val hb b.isLt.le)
  · funext u
    rcases u with ⟨c,u⟩
    cases c
    · exact congrArg (Polynomial.eval (grid n u)) (side a j hj)
    · exact congrArg (Polynomial.eval (grid n u)) (side b k hk)

open PrefixInstantiation in
/-- A signed full-rank splice chart is sufficient for generic local
identifiability of the actual directed chain, with an arbitrary leak site. -/
theorem generic_of_physical_splice {m p n} (ℓ i j k : Chamber m) (a b : Chamber n)
    (hm : p+1+n=m) (hi : i.val=p+1) (hj : j.val=p+1+a.val) (hk : k.val=p+1+b.val)
    (ha : 0<a.val) (hb : 0<b.val) (nodes : Fin (p+1)→ℝ) (hn : Function.Injective nodes)
    (S : ℝ[X]) (hM : S.Monic) (hdegree : S.natDegree=p+1) (hz : ∀ u, S.eval (nodes u)=0)
    (x : Params m) (hx : x (loss m)=0) (hab : ∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0)
    (hr : Function.Injective (fderiv ℝ (chart a b nodes S) (coordinates ℓ p n nodes S x))) :
    GenericLocalID i j k ℓ := by
  have h1 : i≤j := by change i.val≤j.val; omega
  have h2 : i≤k := by change i.val≤k.val; omega
  apply generic_of_exterior_signed_rank i j k ℓ x h1 h2
  apply physical_rank_of_chart ℓ i j k hm nodes hn (grid n) S x hx hab h1 h2 (chart a b nodes S)
    (chart_on_physical ℓ i j k a b hm hi hj hk ha hb nodes hn S hM hdegree hz)
  · have hd : ContDiff ℝ 1 (chart a b nodes S) := by
      apply PrefixExtension.sampleChart_smooth
      · exact contDiff_pi.mpr fun u => (JacobiSamples.seg_smooth _ _ _).of_le (by norm_num)
      · exact contDiff_pi.mpr fun u => (JacobiSamples.seg_smooth _ _ _).of_le (by norm_num)
      · exact contDiff_pi.mpr fun u => (JacobiSamples.seg_smooth _ _ _).of_le (by norm_num)
      · exact (JacobiSamples.data_smooth _ _ _).of_le (by norm_num)
    exact hd.differentiable le_rfl _
  · exact hr

end Catenary.PrefixPhysical
