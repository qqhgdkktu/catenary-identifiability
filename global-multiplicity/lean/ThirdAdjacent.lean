import Chain.PrefixTransfer
import Chain.Endpoint

/-! Global recovery from two adjacent outputs and the terminal output.
Chambers in Lean start at zero. A cut at edge p has p+1 vertices on
the left and t+1 on the right, in a chain with m+1 chambers. -/

noncomputable section
namespace Catenary.ThirdAdjacent
open Polynomial Continuant Middle PrefixPhysical EndpointExterior
open scoped Polynomial

private def left {m} (ℓ : Chamber m) (x : Params m) (hx : Positive x) (p : ℕ) :=
  leftCode (fun i => (physicalSite ℓ x i).diag) (physicalEdge ℓ x hx) 0 p

private def right {m} (ℓ : Chamber m) (x : Params m) (hx : Positive x) (p t : ℕ) :=
  rightCode (fun i => (physicalSite ℓ x i).diag) (physicalEdge ℓ x hx) (p+1) t

private theorem left_polynomials {m} (ℓ : Chamber m) (x : Params m) (hx : Positive x)
    (p : ℕ) (hp : p ≤ m) :
    (left ℓ x hx p).boundaryPair =
      (leading (physicalSite ℓ x) (p+1), leading (physicalSite ℓ x) p) :=
  left_pair _ _ _ _ (fun i _ hi => edge_value _ _ _ _ (by omega))

private theorem right_polynomials {m} (ℓ : Chamber m) (x : Params m) (hx : Positive x)
    (p t : ℕ) (hm : p+t+1=m) :
    (right ℓ x hx p t).boundaryPair = (suffix ℓ x p, suffix ℓ x (p+1)) := by
  rw [right, right_pair _ _ _ _ (fun i _ hi => edge_value _ _ _ _ (by omega))]
  simp only [suffix, physicalSites, drop_from _ _ _ _ (show p+1 ≤ m+1 by omega),
    drop_from _ _ _ _ (show p+1+1 ≤ m+1 by omega), Nat.zero_add,
    show m+1-(p+1)=t+1 by omega, show m+1-(p+1+1)=t by omega]

private theorem cut_eq {m} (ℓ : Chamber m) (x : Params m) (hx : Positive x)
    (p t : ℕ) (hm : p+t+1=m) :
    full ℓ x = (left ℓ x hx p).boundaryPair.1 * (right ℓ x hx p t).boundaryPair.1 -
      (C ((physicalEdge ℓ x hx p : ℝˣ) : ℝ) * (left ℓ x hx p).boundaryPair.2) *
        (right ℓ x hx p t).boundaryPair.2 := by
  rw [left_polynomials _ _ _ _ (by omega), right, right_pair _ _ _ _
    (fun i _ hi => edge_value _ _ _ _ (by omega)), edge_value _ _ _ _ (by omega)]
  simpa only [full, physicalSites, leading, edgeMinor, show p+1+(t+1)=m+1 by omega] using
    cut_after (physicalSite ℓ x) p t

private theorem rates_of_parts {m} (ℓ : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) (p t : ℕ) (hm : p+t+1=m)
    (hl : left ℓ x hx p = left ℓ y hy p) (hr : right ℓ x hx p t = right ℓ y hy p t)
    (hb : physicalEdge ℓ x hx p = physicalEdge ℓ y hy p) : x = y := by
  obtain ⟨ld,lw⟩ := left_inj _ _ _ _ _ _ hl
  obtain ⟨rd,rw'⟩ := right_inj _ _ _ _ _ _ hr
  simp only [Nat.zero_add] at ld lw
  apply PhysicalInverse.rates_of_diagonal_and_products ℓ x y hx hy
  · intro c
    have he : (physicalSite ℓ x c.val).diag = (physicalSite ℓ y c.val).diag := by
      by_cases h : c.val ≤ p
      · exact ld _ h
      · have h' : p+1+(c.val-(p+1))=c.val := by omega
        simpa only [h'] using rd (c.val-(p+1)) (by have := c.isLt; omega)
    simpa [physicalSite,c.isLt] using he
  · intro e
    have he : physicalEdge ℓ x hx e.val = physicalEdge ℓ y hy e.val := by
      by_cases h : e.val < p
      · exact lw _ h
      by_cases hp : e.val = p
      · simpa only [hp] using hb
      · have h' : p+1+(e.val-(p+1))=e.val := by omega
        simpa only [h'] using rw' (e.val-(p+1)) (by have := e.isLt; omega)
    have z := congrArg (fun u : ℝˣ => (u : ℝ)) he
    simpa [edge_value,physicalSite,PathSite.weight,e.isLt,mul_comm] using z

private theorem pair_degree {q} (x : JacobiData ℝ q) :
    x.boundaryPair.1.degree = (q+1 : ℕ) ∧ x.boundaryPair.2.degree = (q : ℕ) := by
  simp only [JacobiData.boundaryPair, degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero,
    intervalCharpoly_natDegree, JacobiData.sites_length, JacobiData.tail_length, and_self]

/-- Degree-bounded division recovers the interface weight and both Jacobi
blocks. The second alternative uses the cancellation of monic leading terms
when the interface weight has been separately measured. -/
private theorem recover {p t : ℕ} (L L' : JacobiData ℝ p) (R R' : JacobiData ℝ t)
    (b b' : ℝˣ) (hr : R.boundaryPair = R'.boundaryPair)
    (hd : L.boundaryPair.1 * R.boundaryPair.1 -
      (C (b:ℝ)*L.boundaryPair.2)*R.boundaryPair.2 =
      L'.boundaryPair.1 * R'.boundaryPair.1 - (C (b':ℝ)*L'.boundaryPair.2)*R'.boundaryPair.2)
    (hsize : p ≤ t ∨ (p = t+1 ∧ b = b')) :
    L = L' ∧ R = R' ∧ b = b' := by
  have he := JacobiData.boundaryPair_injective t hr
  subst R'
  let P := C (b:ℝ)*L.boundaryPair.2
  let Q := C (b':ℝ)*L'.boundaryPair.2
  have e₁ : P.degree = (p : ℕ) := (degree_C_mul_of_isUnit b.isUnit _).trans (pair_degree L).2
  have e₂ : Q.degree = (p : ℕ) := (degree_C_mul_of_isUnit b'.isUnit _).trans (pair_degree L').2
  have hm : L.boundaryPair.2.Monic := Matrix.charpoly_monic _
  have hm' : L'.boundaryPair.2.Monic := Matrix.charpoly_monic _
  have lead : P.leadingCoeff = (b:ℝ) := by simp [P,leadingCoeff_mul,hm.leadingCoeff]
  have lead' : Q.leadingCoeff = (b':ℝ) := by simp [Q,leadingCoeff_mul,hm'.leadingCoeff]
  have small : (P-Q).degree < R.boundaryPair.1.degree := by
    rw [(pair_degree R).1]
    rcases hsize with h | ⟨h,hb⟩
    · apply (degree_sub_le _ _).trans_lt
      rw [e₁,e₂,max_self]
      exact_mod_cast (Nat.lt_succ_of_le h)
    · rw [← h, ← e₁]
      exact degree_sub_lt (e₁.trans e₂.symm) (mul_ne_zero (C_ne_zero.mpr b.ne_zero) hm.ne_zero)
        (lead.trans ((congrArg (fun z : ℝˣ => (z:ℝ)) hb).trans lead'.symm))
  have dvd : R.boundaryPair.1 ∣ R.boundaryPair.2*(P-Q) := by
    refine ⟨L.boundaryPair.1 - L'.boundaryPair.1, ?_⟩
    dsimp [P,Q]
    linear_combination -hd
  have pq : P = Q := sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt
    ((JacobiData.consecutive_coprime R).dvd_of_dvd_mul_left dvd) small)
  have hb : b = b' := Units.ext (lead.symm.trans ((congrArg leadingCoeff pq).trans lead'))
  have pl : L.boundaryPair.1 = L'.boundaryPair.1 := by
    change L.boundaryPair.1 * _ - P * _ = L'.boundaryPair.1 * _ - Q * _ at hd
    rw [pq] at hd
    exact mul_right_cancel₀ (Matrix.charpoly_monic _).ne_zero (sub_left_inj.mp hd)
  have pt : L.boundaryPair.2 = L'.boundaryPair.2 := by
    subst b'
    exact mul_left_cancel₀ (C_ne_zero.mpr b.ne_zero) pq
  exact ⟨JacobiData.boundaryPair_injective p (Prod.ext pl pt), rfl, hb⟩

private theorem suffix_last {m} (ℓ : Chamber m) (x : Params m) :
    suffix ℓ x (Fin.last m).val = 1 := by
  simp only [suffix, Fin.val_last, List.drop_eq_nil_of_le (physicalSites_length ℓ x).le]
  exact (charpoly_eq_cont _).trans cont_nil

/-- The noncancelling terminal output provides the denominator. Each further
output then gives its actual monic suffix and its forward gain, everywhere
on the positive parameter domain. -/
theorem terminal_and_sensor {m} (ℓ j : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) (h : SameCurves 0 (Fin.last m) j ℓ x y) :
    full ℓ x = full ℓ y ∧ suffix ℓ x j.val = suffix ℓ y j.val ∧
    gain ℓ (Fin.last m) x = gain ℓ (Fin.last m) y ∧ gain ℓ j x = gain ℓ j y := by
  have hc : IsCoprime (full ℓ x) (suffix ℓ x (Fin.last m).val) := by
    rw [suffix_last]; exact isCoprime_one_right
  obtain ⟨hd,_,hs,hg,hi⟩ := spectra_and_gains_of_curves _ _ _ _ _ hx hy hc h
  exact ⟨hd,hs,hg,hi⟩

private theorem recover_physical {m} (ℓ : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) (p t : ℕ) (hm : p+t+1=m)
    (hd : full ℓ x = full ℓ y) (h₁ : suffix ℓ x p = suffix ℓ y p)
    (h₂ : suffix ℓ x (p+1) = suffix ℓ y (p+1))
    (hsize : p ≤ t ∨ (p = t+1 ∧ physicalEdge ℓ x hx p = physicalEdge ℓ y hy p)) : x = y := by
  rw [cut_eq ℓ x hx p t hm,cut_eq ℓ y hy p t hm] at hd
  have hr : (right ℓ x hx p t).boundaryPair = (right ℓ y hy p t).boundaryPair := by
    rw [right_polynomials _ _ _ _ _ hm,right_polynomials _ _ _ _ _ hm,h₁,h₂]
  obtain ⟨hl,hr',hb⟩ := recover _ _ _ _ _ _ hr hd hsize
  exact rates_of_parts ℓ x y hx hy p t hm hl hr' hb

/-- For input 1 and three outputs k,k+1,n, all positive physical rates are
globally identifiable if n ≥ 2k. In particular this includes k=2, n≥4
(extra measurement in chamber 2) and k=3, n≥6 (extra measurement in 4). -/
theorem adjacent_physical_unique {m} (ℓ j k : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) (hnext : k.val = j.val+1)
    (hsize : 2*(j.val+1) ≤ m+1)
    (hj : SameCurves 0 (Fin.last m) j ℓ x y) (hk : SameCurves 0 (Fin.last m) k ℓ x y) :
    x = y := by
  let t := m-k.val
  have hm : j.val+t+1=m := by dsimp [t]; have := k.isLt; omega
  have h₁ := terminal_and_sensor ℓ j x y hx hy hj
  have h₂ := terminal_and_sensor ℓ k x y hx hy hk
  exact recover_physical ℓ x y hx hy j.val t hm h₁.1 h₁.2.1 (hnext ▸ h₂.2.1)
    (Or.inl (by omega))

private theorem gain_pos {m} (ℓ j : Chamber m) (x : Params m) (hx : Positive x) :
    0 < gain ℓ j x := by
  rw [EndpointThreshold.gain_prod]
  apply Finset.prod_pos
  intro r hr
  have h : r<m := by have := j.isLt; have := Finset.mem_range.mp hr; omega
  simpa [PhysicalInverse.a,h] using hx (fwd ⟨r,h⟩)

private theorem forward_of_gains {m} (ℓ i j : Chamber m) (x y : Params m) (hx : Positive x)
    (hn : j.val=i.val+1) (hi : gain ℓ i x = gain ℓ i y) (hj : gain ℓ j x = gain ℓ j y) :
    PhysicalInverse.a x i.val = PhysicalInverse.a y i.val := by
  have step (v : Params m) : gain ℓ j v = gain ℓ i v * PhysicalInverse.a v i.val := by
    rw [EndpointThreshold.gain_prod,EndpointThreshold.gain_prod,hn,Finset.prod_range_succ]
  rw [step,step,← hi] at hj
  exact mul_left_cancel₀ (gain_pos ℓ i x hx).ne' hj

private theorem read_diag {m} (ℓ : Chamber m) (x : Params m) (i : ℕ) (hi : i ≤ m) :
    -(physicalSite ℓ x i).diag = PhysicalInverse.a x i + PhysicalInverse.prev x i +
      (if i = ℓ.val then x (loss m) else 0) := by
  have ht : i<m+1 := by omega
  simpa [physicalSite,ht] using PhysicalInverse.diag_total ℓ (⟨i,ht⟩ : Chamber m) x

/-- At five chambers, outputs 3,4,5 also give uniqueness. The observed
gain ratios give a₃,a₄. When the fourth chamber leaks, the physical
zero-frequency determinant recovers its loss from the measured gain
and the terminal diagonal. -/
theorem five_physical_unique (ℓ : Chamber 4) (x y : Params 4)
    (hx : Positive x) (hy : Positive y)
    (h₃ : SameCurves 0 (Fin.last 4) 2 ℓ x y)
    (h₄ : SameCurves 0 (Fin.last 4) 3 ℓ x y) : x = y := by
  obtain ⟨hd,h₂,hg₄,hg₂⟩ := terminal_and_sensor ℓ 2 x y hx hy h₃
  obtain ⟨_,h₃',_,hg₃⟩ := terminal_and_sensor ℓ 3 x y hx hy h₄
  have hr : (right ℓ x hx 2 1).boundaryPair = (right ℓ y hy 2 1).boundaryPair := by
    rw [right_polynomials _ _ _ _ _ (by decide),right_polynomials _ _ _ _ _ (by decide)]
    exact Prod.ext h₂ h₃'
  obtain ⟨hdiag,_⟩ := right_inj _ _ _ _ _ _ (JacobiData.boundaryPair_injective 1 hr)
  have d₃ : (physicalSite ℓ x 3).diag = (physicalSite ℓ y 3).diag := hdiag 0 (by decide)
  have d₄ : (physicalSite ℓ x 4).diag = (physicalSite ℓ y 4).diag := hdiag 1 (by decide)
  have a₂ : PhysicalInverse.a x 2 = PhysicalInverse.a y 2 :=
    forward_of_gains ℓ 2 3 x y hx rfl hg₂ hg₃
  have a₃ : PhysicalInverse.a x 3 = PhysicalInverse.a y 3 :=
    forward_of_gains ℓ 3 (Fin.last 4) x y hx rfl hg₃ hg₄
  have hl : (if 3=ℓ.val then x (loss 4) else 0) = (if 3=ℓ.val then y (loss 4) else 0) := by
    split_ifs with h
    · have no₄ : 4 ≠ ℓ.val := by omega
      have b₃ : PhysicalInverse.b x 3 = PhysicalInverse.b y 3 := by
        have ha := read_diag ℓ x 4 (by decide)
        have hb := read_diag ℓ y 4 (by decide)
        rw [d₄,hb] at ha
        simpa [PhysicalInverse.a,PhysicalInverse.prev,no₄] using ha.symm
      have bh : PhysicalInverse.b x 3 ≠ 0 := by
        simpa [PhysicalInverse.b] using (hx (back (3 : Fin 4))).ne'
      have dc (z : Params 4) : (full ℓ z).eval 0 =
          z (loss 4) * gain ℓ (3 : Chamber 4) z * PhysicalInverse.b z 3 := by
        have e := Closed.determinant_at_zero ℓ z
        rw [← h] at e
        simpa [full,physicalSites,Closed.pref,EndpointThreshold.gain_prod] using e
      have e := congrArg (Polynomial.eval (0:ℝ)) hd
      rw [dc,dc,← hg₃,← b₃] at e
      exact mul_right_cancel₀ (gain_pos ℓ 3 x hx).ne' (mul_right_cancel₀ bh e)
    · rfl
  have b₂ : PhysicalInverse.b x 2 = PhysicalInverse.b y 2 := by
    have e := read_diag ℓ x 3 (by decide)
    rw [d₃,read_diag ℓ y 3 (by decide), ← a₃, ← hl] at e
    exact (add_left_cancel (add_right_cancel e)).symm
  have he : physicalEdge ℓ x hx 2 = physicalEdge ℓ y hy 2 := by
    apply Units.ext
    rw [edge_value _ _ _ _ (by decide),edge_value _ _ _ _ (by decide)]
    change PhysicalInverse.b x 2 * PhysicalInverse.a x 2 =
      PhysicalInverse.b y 2 * PhysicalInverse.a y 2
    rw [a₂,b₂]
  exact recover_physical ℓ x y hx hy 2 1 (by decide) hd h₂ h₃' (Or.inr ⟨rfl,he⟩)

private theorem physical_suffix {m} (ℓ j : Chamber m) (x : Params m) :
    suffix ℓ x j.val =
      intervalCharpoly (sitesFrom (physicalSite ℓ x) (j.val+1) (m-j.val)) := by
  unfold suffix physicalSites
  rw [drop_from _ _ _ _ j.isLt]
  simp

private theorem one_site (s : PathSite ℝ) : intervalCharpoly [s] = X-C s.diag :=
  (charpoly_eq_cont _).trans (cont_singleton _)

private theorem two_sites (a b : PathSite ℝ) :
    intervalCharpoly [a,b] = (X-C a.diag)*(X-C b.diag)-C a.weight := by
  simp only [intervalCharpoly,charpoly_eq_cont,List.map_cons,List.map_nil,
    cont_cons_cons,cont_singleton,cont_nil,pencil_weight,mul_one]
  rfl

private theorem three_sites (a b c : PathSite ℝ) :
    intervalCharpoly [a,b,c] =
      ((X-C a.diag)*(X-C b.diag)-C a.weight)*(X-C c.diag)-C b.weight*(X-C a.diag) := by
  simp only [intervalCharpoly,charpoly_eq_cont,List.map_cons,List.map_nil,
    cont_cons_cons,cont_singleton,cont_nil,pencil_weight,mul_one]
  change (X-C a.diag)*((X-C b.diag)*(X-C c.diag)-C b.weight)-C a.weight*(X-C c.diag) = _
  ring

/-- A three-vertex terminal block is determined by its cubic, the terminal
diagonal and the final nonzero edge product. Evaluating at the terminal
diagonal kills the first term, yielding the opposite diagonal. -/
private theorem cubic_inner (a b a' b' c u u' v : ℝ) (hv : v ≠ 0)
    (e : ((X-C a)*(X-C b)-C u)*(X-C c)-C v*(X-C a) =
      ((X-C a')*(X-C b')-C u')*(X-C c)-C v*(X-C a')) : a=a' ∧ b=b' := by
  have ec := congrArg (Polynomial.eval c) e
  simp only [eval_sub,eval_mul,eval_X,eval_C,sub_self,mul_zero,zero_sub,neg_inj] at ec
  have ha : a = a' := by linarith [mul_left_cancel₀ hv ec]
  subst a'
  have eq₂ := mul_right_cancel₀ (X_sub_C_ne_zero c) (sub_left_inj.mp e)
  have ea := congrArg (Polynomial.eval a) eq₂
  have hu : u = u' := by simpa only [eval_sub,eval_mul,eval_X,eval_C,
    sub_self,zero_mul,zero_sub,neg_inj] using ea
  subst u'
  have eq₁ := mul_left_cancel₀ (X_sub_C_ne_zero a) (sub_left_inj.mp eq₂)
  exact ⟨rfl,C_injective (by linear_combination -eq₁)⟩

/-- The remaining small placement, n=6 and outputs 3,5,6, is globally
identifiable at all positive rates. No pole separation is needed. -/
theorem six_preterminal_physical_unique (ℓ : Chamber 5) (x y : Params 5)
    (hx : Positive x) (hy : Positive y)
    (h₃ : SameCurves 0 (Fin.last 5) 2 ℓ x y)
    (h₅ : SameCurves 0 (Fin.last 5) 4 ℓ x y) : x = y := by
  obtain ⟨hd,h₂,_,_⟩ := terminal_and_sensor ℓ 2 x y hx hy h₃
  obtain ⟨_,h₄,hg₅,hg₄⟩ := terminal_and_sensor ℓ 4 x y hx hy h₅
  let f := physicalSite ℓ x
  let g := physicalSite ℓ y
  have c : (f 5).diag = (g 5).diag := by
    rw [physical_suffix ℓ 4 x,physical_suffix ℓ 4 y] at h₄
    change intervalCharpoly [f 5] = intervalCharpoly [g 5] at h₄
    rw [one_site,one_site] at h₄
    exact C_injective (by linear_combination -h₄)
  have a₄ : PhysicalInverse.a x 4 = PhysicalInverse.a y 4 :=
    forward_of_gains ℓ 4 (Fin.last 5) x y hx rfl hg₄ hg₅
  have hl : (if 5=ℓ.val then x (loss 5) else 0) = (if 5=ℓ.val then y (loss 5) else 0) := by
    split_ifs with h
    · have dc (z : Params 5) : (full ℓ z).eval 0 = z (loss 5) * gain ℓ (Fin.last 5) z := by
        have e := Closed.determinant_at_zero ℓ z
        rw [← h] at e
        simpa [full,physicalSites,Closed.pref,EndpointThreshold.gain_prod] using e
      have e := congrArg (Polynomial.eval (0:ℝ)) hd
      rw [dc,dc,← hg₅] at e
      exact mul_right_cancel₀ (gain_pos ℓ _ x hx).ne' e
    · rfl
  have b₄ : PhysicalInverse.b x 4 = PhysicalInverse.b y 4 := by
    have e := read_diag ℓ x 5 (by decide)
    change (physicalSite ℓ x 5).diag = (physicalSite ℓ y 5).diag at c
    rw [c,read_diag ℓ y 5 (by decide),← hl] at e
    simpa [PhysicalInverse.a,PhysicalInverse.prev] using e.symm
  have w : (f 4).weight = (g 4).weight := by
    change PhysicalInverse.b x 4 * PhysicalInverse.a x 4 =
      PhysicalInverse.b y 4 * PhysicalInverse.a y 4
    rw [a₄,b₄]
  have wn : (f 4).weight ≠ 0 := by
    change x (back 4) * x (fwd 4) ≠ 0
    exact mul_ne_zero (hx _).ne' (hx _).ne'
  have cubic := h₂
  rw [physical_suffix ℓ 2 x,physical_suffix ℓ 2 y] at cubic
  change intervalCharpoly [f 3,f 4,f 5] = intervalCharpoly [g 3,g 4,g 5] at cubic
  rw [three_sites,three_sites,← c,← w] at cubic
  obtain ⟨_,d⟩ := cubic_inner _ _ _ _ _ _ _ _ wn cubic
  have h₃' : suffix ℓ x 3 = suffix ℓ y 3 := by
    change suffix ℓ x (3 : Chamber 5).val = suffix ℓ y (3 : Chamber 5).val
    rw [physical_suffix ℓ (3 : Chamber 5) x,physical_suffix ℓ (3 : Chamber 5) y]
    change intervalCharpoly [f 4,f 5] = intervalCharpoly [g 4,g 5]
    rw [two_sites,two_sites,d,c,w]
  exact recover_physical ℓ x y hx hy 2 2 (by decide) hd h₂ h₃' (Or.inl (by decide))

/-- An extra output at the inlet identifies all positive rates for every
length and known leak. This is the endpoint inverse theorem in the same
ordering of curve equalities as the other placements above. -/
theorem inlet_physical_unique {m} (ℓ : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y)
    (h₁ : SameCurves 0 (Fin.last m) 0 ℓ x y) : x = y :=
  Endpoint.observed_endpoint_global (Fin.last m) ℓ x y hx hy
    (fun u hu t ht => (h₁ u hu t ht).symm)

#print axioms inlet_physical_unique
#print axioms adjacent_physical_unique
#print axioms five_physical_unique
#print axioms six_preterminal_physical_unique

end Catenary.ThirdAdjacent
