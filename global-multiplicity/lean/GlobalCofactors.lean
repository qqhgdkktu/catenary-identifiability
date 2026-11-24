import Chain.EndpointThreshold

/-! Physical DC cofactor identities for an endpoint input and one leak.
All chamber labels start at zero. No genericity or positivity is required
until division by a DC tail determinant is used. -/
noncomputable section
namespace Catenary.GlobalCofactors
open Polynomial Continuant
open scoped Polynomial BigOperators

private theorem prefix_sites {m} (ℓ v : Chamber m) (x : Params m) :
    Middle.prefix ℓ x v.val = intervalCharpoly (sitesFrom (physicalSite ℓ x) 0 v.val) := by
  unfold Middle.prefix physicalSites
  rw [sitesFrom_take _ _ _ _ v.isLt.le]

private theorem suffix_sites {m} (ℓ v : Chamber m) (x : Params m) :
    Middle.suffix ℓ x v.val =
      intervalCharpoly (sitesFrom (physicalSite ℓ x) (v.val+1) (m-v.val)) := by
  unfold Middle.suffix physicalSites
  rw [Middle.drop_from _ _ _ _ v.isLt]
  simp

/-- The gain to any output before or at the leak equals its leading
cofactor at zero. Includes p=E(0) if ℓ≥3 and q=H(0) if ℓ=n. -/
theorem gain_eq_prefix_eval {m} (ℓ v : Chamber m) (x : Params m) (hv : v.val ≤ ℓ.val) :
    EndpointExterior.gain ℓ v x = (Middle.prefix ℓ x v.val).eval 0 := by
  rw [EndpointThreshold.gain_prod, prefix_sites]
  exact (Closed.pref_before ℓ x v.val hv).symm

private def dc {m} (ℓ : Chamber m) (x : Params m) (u n : ℕ) : ℝ :=
  (intervalCharpoly (sitesFrom (physicalSite ℓ x) u n)).eval 0

private theorem dc_empty {m} (ℓ : Chamber m) (x : Params m) (u : ℕ) :
    dc ℓ x u 0 = 1 := by
  have he : intervalCharpoly ([] : List (PathSite ℝ)) = 1 :=
    (charpoly_eq_cont _).trans cont_nil
  simp [dc,sitesFrom,he]

private theorem phys_weight {m} (ℓ : Chamber m) (x : Params m) (r : ℕ) :
    (physicalSite ℓ x r).weight = PhysicalInverse.a x r * PhysicalInverse.b x r := by
  simp only [physicalSite,PathSite.weight,PhysicalInverse.a,PhysicalInverse.b,mul_comm]

private theorem tail_diag {m} (ℓ : Chamber m) (x : Params m) (r : ℕ)
    (hr : ℓ.val ≤ r) (hm : r+1 ≤ m) :
    -(physicalSite ℓ x (r+1)).diag = PhysicalInverse.a x (r+1) + PhysicalInverse.b x r := by
  have ht : r+1<m+1 := by omega
  have hn : r+1 ≠ ℓ.val := by omega
  have he := PhysicalInverse.diag_total ℓ (⟨r+1,ht⟩ : Chamber m) x
  simpa [physicalSite, ht, PhysicalInverse.prev, hn] using he

private theorem dc_step {m} (ℓ : Chamber m) (x : Params m) (u d : ℕ) :
    dc ℓ x u (d+2) = -(physicalSite ℓ x u).diag * dc ℓ x (u+1) (d+1) -
      (physicalSite ℓ x u).weight * dc ℓ x (u+2) d := by
  have step (a b : PathSite ℝ) (xs : List (PathSite ℝ)) :
      intervalCharpoly (a::b::xs) = (X-C a.diag)*intervalCharpoly (b::xs) -
        C a.weight*intervalCharpoly xs := by
    simp only [intervalCharpoly,charpoly_eq_cont,List.map_cons,cont_cons_cons,pencil_weight]
    rfl
  let f := physicalSite ℓ x
  have he := congrArg (Polynomial.eval (0:ℝ)) (step (f u) (f (u+1)) (sitesFrom f (u+2) d))
  simpa only [dc, sitesFrom, f, eval_sub,eval_mul,eval_X,eval_C,zero_sub] using he

private theorem tail_ratio {m} (ℓ : Chamber m) (x : Params m) (r d : ℕ)
    (hr : ℓ.val ≤ r) (hd : r+1+d = m) :
    dc ℓ x (r+1) (d+1) = PhysicalInverse.b x r * dc ℓ x (r+2) d := by
  induction d generalizing r with
  | zero =>
    have hdiag := tail_diag ℓ x r hr (by omega)
    have hzero : PhysicalInverse.a x (r+1) = 0 := by
      simp [PhysicalInverse.a,show ¬r+1<m by omega]
    have single (a : PathSite ℝ) : intervalCharpoly [a] = X-C a.diag :=
      (charpoly_eq_cont _).trans (cont_singleton _)
    rw [dc_empty, mul_one]
    simpa [dc,sitesFrom,single,hzero] using hdiag
  | succ d ih =>
    rw [dc_step, tail_diag ℓ x r hr (by omega),phys_weight]
    have h := ih (r+1) (by omega) (by omega)
    linear_combination (PhysicalInverse.a x (r+1)) * h

/-- A trailing principal block strictly past the leak has DC determinant
equal to the product of backwards transfer rates along its incoming cuts. -/
theorem suffix_eval_eq_backwards {m} (ℓ v : Chamber m) (x : Params m) (hv : ℓ.val ≤ v.val) :
    (Middle.suffix ℓ x v.val).eval 0 =
      ∏ t ∈ Finset.range (m-v.val), PhysicalInverse.b x (v.val+t) := by
  have run (d r : ℕ) (hr : ℓ.val ≤ r) (hd : r+d=m) :
      dc ℓ x (r+1) d = ∏ t ∈ Finset.range d, PhysicalInverse.b x (r+t) := by
    induction d generalizing r with
    | zero => simp [dc_empty]
    | succ d ih =>
      rw [tail_ratio ℓ x r d hr (by omega), ih (r+1) (by omega) (by omega),
        Finset.prod_range_succ']
      simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,mul_comm]
  rw [suffix_sites]
  exact run (m-v.val) v.val hv (by have := v.isLt; omega)

private theorem weights {m} (ℓ : Chamber m) (x : Params m) (r d : ℕ) :
    edgeProduct (sitesFrom (physicalSite ℓ x) r d) =
    ∏ t ∈ Finset.range d, (PhysicalInverse.a x (r+t) * PhysicalInverse.b x (r+t)) := by
  induction d generalizing r with
  | zero => simp [sitesFrom, edgeProduct]
  | succ d ih =>
    change (physicalSite ℓ x r).weight * edgeProduct (sitesFrom _ (r+1) d) = _
    rw [phys_weight, ih, Finset.prod_range_succ']
    simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,mul_comm]

private theorem all_weights {m} (ℓ v : Chamber m) (x : Params m) (hv : v.val < m) :
    EndpointExterior.weightProduct ℓ v (Fin.last m) x =
      ∏ t ∈ Finset.range (m-v.val), (PhysicalInverse.a x (v.val+t) * PhysicalInverse.b x (v.val+t)) := by
  have he : m-v.val = (m-(v.val+1))+1 := by omega
  change (physicalSite ℓ x v.val).weight *
    edgeProduct (sitesFrom _ (v.val+1) (m-(v.val+1))) = _
  rw [← weights ℓ x v.val (m-v.val), he]
  rfl

/-- For every output v at or after the leak and before the last chamber,
q times its zero-frequency trailing cofactor equals the gain to v times the
product of squared Jacobi off-diagonal entries from v to the endpoint.
In particular at v=3 this is q W(0)=p K whenever the leak is at 1, 2, or 3. -/
theorem gain_times_tail {m} (ℓ v : Chamber m) (x : Params m) (hv : ℓ.val ≤ v.val)
    (hvm : v.val < m) :
    EndpointExterior.gain ℓ (Fin.last m) x * (Middle.suffix ℓ x v.val).eval 0 =
      EndpointExterior.weightProduct ℓ v (Fin.last m) x * EndpointExterior.gain ℓ v x := by
  rw [suffix_eval_eq_backwards ℓ v x hv, all_weights ℓ v x hvm, Finset.prod_mul_distrib,
    EndpointThreshold.gain_prod,EndpointThreshold.gain_prod]
  change (∏ r ∈ Finset.range m, PhysicalInverse.a x r) * _ = _
  have he := Finset.prod_range_add (PhysicalInverse.a x) v.val (m-v.val)
  rw [show v.val+(m-v.val)=m by omega] at he
  rw [he]
  ring

/-- Exact polynomial condensation with the second cut at the last chamber.
All factors are principal characteristic polynomials of the physical model. -/
theorem endpoint_condensation {m} (ℓ v : Chamber m) (x : Params m) (hv : v.val < m) :
    Middle.full ℓ x * EndpointExterior.middlePolynomial ℓ v (Fin.last m) x =
      Middle.suffix ℓ x v.val * Middle.prefix ℓ x m -
      C (EndpointExterior.weightProduct ℓ v (Fin.last m) x) * Middle.prefix ℓ x v.val := by
  let f := physicalSite ℓ x
  let k := Fin.last m
  have hjk : v < k := hv
  have endNil : sitesFrom f (k.val+1) (m-k.val) = [] := by
    simp [k,sitesFrom]
  have eh := EndpointThreshold.total_parts f v k hjk
  have ew := EndpointThreshold.suffix_parts f v k hjk
  rw [endNil] at eh ew
  have e := charpoly_condensation (sitesFrom f 0 v.val)
    (sitesFrom f (v.val+1) (k.val-(v.val+1))) [] (f v.val) (f k.val)
  change intervalCharpoly (sitesFrom f 0 (m+1)) * _ = _
  rw [eh, suffix_sites ℓ v x, ew]
  change _ = _ * Middle.prefix ℓ x k.val - _ * _
  rw [prefix_sites ℓ k x, EndpointThreshold.prefix_parts f v k hjk, prefix_sites ℓ v x]
  have he : intervalCharpoly ([] : List (PathSite ℝ)) = 1 :=
    (charpoly_eq_cont _).trans cont_nil
  change _ = _ - intervalCharpoly ([] : List (PathSite ℝ)) * _ at e
  rw [he, one_mul] at e
  exact e

/-- The manuscript's last DC identity with the denominator cleared. Valid
at every physical real rate vector, including singular ones, and at every
nonterminal leak. The terminal-leak identity is `gain_eq_prefix_eval`. -/
theorem physical_cofactor_identity {m} (ℓ : Chamber m) (x : Params m) (hleak : ℓ.val < m) :
    EndpointExterior.gain ℓ (Fin.last m) x * (Middle.suffix ℓ x ℓ.val).eval 0 =
      (Middle.prefix ℓ x m).eval 0 * (Middle.suffix ℓ x ℓ.val).eval 0 -
      (Middle.full ℓ x).eval 0 * (EndpointExterior.middlePolynomial ℓ ℓ (Fin.last m) x).eval 0 := by
  have h := congrArg (Polynomial.eval (0:ℝ)) (endpoint_condensation ℓ ℓ x hleak)
  simp only [eval_mul,eval_sub,eval_C] at h
  rw [gain_times_tail ℓ ℓ x le_rfl hleak, gain_eq_prefix_eval ℓ ℓ x le_rfl]
  linarith only [h]

/-- A clean trailing cofactor at DC is strictly positive on the physical orthant. -/
theorem suffix_eval_pos {m} (ℓ v : Chamber m) (x : Params m) (hx : Positive x)
    (hv : ℓ.val ≤ v.val) : 0 < (Middle.suffix ℓ x v.val).eval 0 := by
  rw [suffix_eval_eq_backwards ℓ v x hv]
  apply Finset.prod_pos
  intro t ht
  have ht' := Finset.mem_range.mp ht
  have h : v.val+t<m := by omega
  simpa [PhysicalInverse.b,h] using hx (back ⟨v.val+t,h⟩)

/-- Divided form of the full endpoint gain for every positive vector,
with C the characteristic polynomial of the open interval between the
leak and the final chamber. -/
theorem gain_eq_cofactor_quotient {m} (ℓ : Chamber m) (x : Params m) (hx : Positive x)
    (hleak : ℓ.val < m) :
    EndpointExterior.gain ℓ (Fin.last m) x =
      (Middle.prefix ℓ x m).eval 0 - (Middle.full ℓ x).eval 0 *
      (EndpointExterior.middlePolynomial ℓ ℓ (Fin.last m) x).eval 0 /
      (Middle.suffix ℓ x ℓ.val).eval 0 := by
  have h := physical_cofactor_identity ℓ x hleak
  have hn := (suffix_eval_pos ℓ ℓ x hx le_rfl).ne'
  field_simp [hn]
  linarith only [h]

end Catenary.GlobalCofactors
