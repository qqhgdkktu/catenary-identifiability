import Chain.ClosedChain
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace Catenary.Closed

theorem generator_line {m} (ℓ : Chamber m) (x v : Params m) (t : ℝ) (r c : Chamber m) :
    generator ℓ (x+t•v) r c = generator ℓ x r c + t*generator ℓ v r c := by
  let ef (k : Fin m) := directedEdge k.castSucc k.succ r c
  let eb (k : Fin m) := directedEdge k.succ k.castSucc r c
  have e (k : Fin m) : (x+t•v) (fwd k)*ef k + (x+t•v) (back k)*eb k =
    (x (fwd k)*ef k+x (back k)*eb k) + t*(v (fwd k)*ef k+v (back k)*eb k) := by
    simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have esum := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) (fun k _ => e k)
  dsimp only [ef,eb] at esum
  unfold generator
  rw [esum]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  split_ifs <;> simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- The true derivative of det(-A) at a closed vector with nonzero edges
detects the leakage variation irrespective of the position of that leak. -/
theorem loss_variation {m} (ℓ : Chamber m) (x v : Params m)
    (hx : x (loss m) = 0) (hab : ∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0)
    (hd : HasDerivAt (fun t : ℝ => pref ℓ (x+t•v) (m+1)) 0 0) : v (loss m)=0 := by
  let A (t : ℝ) := ∏ r ∈ Finset.range ℓ.val, PhysicalInverse.a (x+t•v) r
  let B (t : ℝ) := ∏ d ∈ Finset.range (m-ℓ.val), PhysicalInverse.b (x+t•v) (ℓ.val+d)
  have hA : DifferentiableAt ℝ A 0 := by
    apply DifferentiableAt.finset_prod
    intro r _
    unfold PhysicalInverse.a
    split_ifs <;> simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hB : DifferentiableAt ℝ B 0 := by
    apply DifferentiableAt.finset_prod
    intro r _
    unfold PhysicalInverse.b
    split_ifs <;> simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have a0 : A 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have h : r<m := by have := ℓ.isLt; omega
    simpa [PhysicalInverse.a,h] using (hab ⟨r,h⟩).1
  have b0 : B 0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have h : ℓ.val+r<m := by omega
    simpa [PhysicalInverse.b,h] using (hab ⟨ℓ.val+r,h⟩).2
  have hl : HasDerivAt (fun t : ℝ => (x+t•v) (loss m)) (v (loss m)) 0 := by
    simpa [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
      (((hasDerivAt_id (0:ℝ)).mul_const (v (loss m))).const_add (x (loss m)))
  have e := (hl.mul hA.hasDerivAt).mul hB.hasDerivAt
  have hD : HasDerivAt (fun t : ℝ => pref ℓ (x+t•v) (m+1)) (v (loss m)*A 0*B 0) 0 := by
    simpa [determinant_at_zero,A,B,hx,Function.comp_def] using e
  exact (mul_eq_zero.mp ((mul_eq_zero.mp (hD.unique hd)).resolve_right b0)).resolve_right a0

theorem prefix_variation {m} (ℓ : Chamber m) (x v : Params m)
    (hx : x (loss m)=0) (hv : v (loss m)=0) (q : ℕ) (hq : q≤m+1)
    (hg : HasDerivAt (fun t : ℝ => ∏ r ∈ Finset.range q, PhysicalInverse.a (x+t•v) r) 0 0) :
    HasDerivAt (fun t : ℝ => pref ℓ (x+t•v) q) 0 0 := by
  have e (t : ℝ) : (x+t•v) (loss m) = 0 := by simp [hx,hv]
  simpa only [fun t => prefix_closed ℓ _ (e t) q hq] using hg

/-- Every zero variation of all diagonals and edge products is the zero physical
variation. The base rates may have either sign; only the directed edges must be
nonzero. The algebraic observation map has degree at most two: evaluate at
equidistant points x+t v and x−t v and the quadratic terms cancel exactly. -/
theorem original_variation_zero {m} (ℓ : Chamber m) (x v : Params m)
    (hn : ∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0)
    (hD : ∀ c, HasDerivAt (fun t : ℝ => generator ℓ (x+t•v) c c) 0 0)
    (hE : ∀ r : Fin m, HasDerivAt (fun t : ℝ =>
      (x+t•v) (fwd r)*(x+t•v) (back r)) 0 0) : v = 0 := by
  have scalar (k : Fin (2*m+1)) : HasDerivAt (fun t : ℝ => (x+t•v) k) (v k) 0 := by
    simpa [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
      (((hasDerivAt_id (0:ℝ)).mul_const (v k)).const_add (x k))
  have diag (c : Chamber m) : generator ℓ v c c = 0 := by
    have he := ((hasDerivAt_id (0:ℝ)).mul_const (generator ℓ v c c)).const_add (generator ℓ x c c)
    have hd : HasDerivAt (fun t : ℝ => generator ℓ (x+t•v) c c) (generator ℓ v c c) 0 := by
      simpa [generator_line] using he
    exact hd.unique (hD c)
  have edge (r : Fin m) : v (fwd r)*x (back r)+x (fwd r)*v (back r)=0 := by
    have he := ((scalar (fwd r)).mul (scalar (back r))).unique (hE r)
    simpa [add_comm,mul_comm] using he
  have hb (r : Fin m) : ∀ᶠ t : ℝ in 𝓝 0, (x+t•v) (back r) ≠ 0 :=
    (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds (by simpa using (hn r).2)
  have hf (r : Fin m) : ∀ᶠ t : ℝ in 𝓝 0, (x+(-t)•v) (fwd r) ≠ 0 :=
    (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds (by simpa using (hn r).1)
  have H := (Filter.eventually_all.mpr hb).and (Filter.eventually_all.mpr hf)
  obtain ⟨ε,he,ht⟩ := Metric.eventually_nhds_iff_ball.mp H
  let t := ε/2
  have hp : 0<t := half_pos he
  have hmem : t ∈ Metric.ball (0:ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hp]
    exact half_lt_self he
  obtain ⟨htb,htf⟩ := ht t hmem
  have e : x+t•v = x+(-t)•v := by
    apply PhysicalInverse.signed_rates_of_diagonal_and_products ℓ _ _ htb htf
    · intro c; simp only [generator_line,diag,mul_zero,add_zero]
    · intro r
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      linear_combination 2*t*edge r
  funext k
  have h := congrFun e k
  change x k+t*v k = x k+(-t)*v k at h
  have heq : t*v k=0 := by linarith
  exact (mul_eq_zero.mp heq).resolve_left hp.ne'

end Catenary.Closed
