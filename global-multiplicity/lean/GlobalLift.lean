import Chain.PrefixExtension
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open Filter Matrix
open scoped Topology BigOperators Matrix

namespace Catenary.GlobalLift

/-- A strict peak at three samples survives a pointwise convergent lift. -/
theorem peak_eventually {X : Type*} {l : Filter X} {a b c : X → ℝ} {A B C : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) (hc : Tendsto c l (𝓝 C))
    (hab : A < B) (hcb : C < B) : ∀ᶠ x in l, a x < b x ∧ c x < b x :=
  (ha.eventually_lt hb hab).and (hc.eventually_lt hb hcb)

/-- The three positive normalisation sums can differ. One small positive
    ε preserves both inequalities simultaneously. -/
theorem renormalized_peak {a b c A B C : ℝ} (ha : 0 < A) (hb : 0 < B)
    (hc : 0 < C) (hab : a < b) (hcb : c < b) :
    ∀ᶠ ε : ℝ in 𝓝 0, A / (A + ε) * a < B / (B + ε) * b ∧
      C / (C + ε) * c < B / (B + ε) * b := by
  have hlim (x s : ℝ) (hs : 0 < s) :
      Tendsto (fun ε : ℝ => s / (s + ε) * x) (𝓝 0) (𝓝 x) := by
    have h : Tendsto (fun ε : ℝ => s + ε) (𝓝 0) (𝓝 (s+0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa [ne_of_gt hs] using
      ((tendsto_const_nhds (x := s)).div h (by simpa using (ne_of_gt hs))).mul
      (tendsto_const_nhds (x := x))
  exact peak_eventually (hlim a A ha) (hlim b B hb) (hlim c C hc) hab hcb

/-- The two lifts reach exactly the needed half-strip from its base (5,4). -/
theorem interior_induction (P : ℕ → ℕ → Prop) (base : P 5 4)
    (liftA : ∀ n ell, 4 ≤ ell → ell < n → P n ell → P (n+1) (ell+1))
    (liftB : ∀ n ell, 4 ≤ ell → ell < n → P n ell → P (n+1) ell)
    (n ell : ℕ) (h4 : 4 ≤ ell) (hn : ell < n) : P n ell := by
  have diag (k : ℕ) : P (5+k) (4+k) := by
    induction k with
    | zero => exact base
    | succ k ih => exact liftA (5+k) (4+k) (by omega) (by omega) ih
  have step (j : ℕ) : P ((5+(ell-4))+j) (4+(ell-4)) := by
    induction j with
    | zero => exact diag _
    | succ j ih => exact liftB ((5+(ell-4))+j) (4+(ell-4)) (by omega) (by omega) ih
  convert step (n-(ell+1)) using 1 <;> omega

variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K]

def gram (w : I → ℝ) (v : I → K → ℝ) : Matrix K K ℝ :=
  fun j k => ∑ i, w i * v i j * v i k

def rhs (w d : I → ℝ) (v : I → K → ℝ) : K → ℝ :=
  fun j => ∑ i, w i * d i * v i j

/-- Value of the quadratic minimum in moment/Gram coordinates, equation (5).
    This definition is used only at invertible Gram matrices. -/
def gramValue (w d : I → ℝ) (v : I → K → ℝ) : ℝ :=
  ∑ i, w i * (d i)^2 - (rhs w d v) ⬝ᵥ ((gram w v)⁻¹ *ᵥ (rhs w d v))

theorem gramValue_tendsto {X : Type*} {l : Filter X}
    {w d : X → I → ℝ} {v : X → I → K → ℝ}
    {W D : I → ℝ} {V : I → K → ℝ}
    (hw : ∀ i, Tendsto (fun x => w x i) l (𝓝 (W i)))
    (hd : ∀ i, Tendsto (fun x => d x i) l (𝓝 (D i)))
    (hv : ∀ i j, Tendsto (fun x => v x i j) l (𝓝 (V i j)))
    (hinv : (gram W V).det ≠ 0) :
    Tendsto (fun x => gramValue (w x) (d x) (v x)) l (𝓝 (gramValue W D V)) := by
  have hg : Tendsto (fun x => gram (w x) (v x)) l (𝓝 (gram W V)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro k
    exact tendsto_finset_sum _ fun i _ => ((hw i).mul (hv i j)).mul (hv i k)
  have hr (j : K) : Tendsto (fun x => rhs (w x) (d x) (v x) j) l (𝓝 (rhs W D V j)) :=
    tendsto_finset_sum _ fun i _ => ((hw i).mul (hd i)).mul (hv i j)
  have hi := (continuousAt_matrix_inv (gram W V)
    (by simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hinv))).tendsto.comp hg
  have he (j k : K) : Tendsto (fun x => (gram (w x) (v x))⁻¹ j k) l
      (𝓝 ((gram W V)⁻¹ j k)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hi j) k
  apply Filter.Tendsto.sub
  · exact tendsto_finset_sum _ fun i _ => (hw i).mul ((hd i).pow 2)
  · apply tendsto_finset_sum
    intro j _
    exact (hr j).mul (tendsto_finset_sum _ fun k _ => (he j k).mul (hr k))


/-- A row for the extra spectral node and one extra variable, uncoupled
    in the limit. -/
def extraRows (v : I → K → ℝ) : I ⊕ Unit → K ⊕ Unit → ℝ
  | .inl i, .inl j => v i j
  | .inr _, .inr _ => 1
  | _, _ => 0

private def extVec (w : I → ℝ) (h : ℝ) : I ⊕ Unit → ℝ :=
  Sum.elim w (fun _ => h)

omit [Fintype K] [DecidableEq K] in
private theorem extGram (w : I → ℝ) (v : I → K → ℝ) (η : ℝ) :
    gram (extVec w η) (extraRows v) =
      Matrix.fromBlocks (gram w v) 0 0 (fun _ _ : Unit => η) := by
  ext i j
  cases i <;> cases j <;> simp [gram, extVec, extraRows, Matrix.fromBlocks, Fintype.sum_sum_type]

omit [Fintype K] [DecidableEq K] in
private theorem extRhs (w d : I → ℝ) (v : I → K → ℝ) (η : ℝ) :
    rhs (extVec w η) (extVec d 0) (extraRows v) = extVec (rhs w d v) 0 := by
  funext j
  cases j <;> simp [rhs, extVec, extraRows, Fintype.sum_sum_type]

private theorem extGram_det (w : I → ℝ) (v : I → K → ℝ) (η : ℝ) :
    (gram (extVec w η) (extraRows v)).det = (gram w v).det * η := by
  rw [extGram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (fun _ _ : Unit => η)]

private theorem solve_of_mulVec {G : Matrix K K ℝ} (h : G.det ≠ 0)
    {b z : K → ℝ} (heq : G *ᵥ z = b) : G⁻¹ *ᵥ b = z := by
  rw [← heq, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h),
    Matrix.one_mulVec]

theorem gramValue_extra (w d : I → ℝ) (v : I → K → ℝ) (η : ℝ)
    (hη : η ≠ 0) (hgram : (gram w v).det ≠ 0) :
    gramValue (extVec w η) (extVec d 0) (extraRows v) = gramValue w d v := by
  have hdet : (gram (extVec w η) (extraRows v)).det ≠ 0 := by
    rw [extGram_det]; exact mul_ne_zero hgram hη
  let z := (gram w v)⁻¹ *ᵥ rhs w d v
  have hz : gram w v *ᵥ z = rhs w d v := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hgram), Matrix.one_mulVec]
  have hsolve : gram (extVec w η) (extraRows v) *ᵥ extVec z 0 = extVec (rhs w d v) 0 := by
    rw [extGram, Matrix.fromBlocks_mulVec]
    have h1 : extVec z 0 ∘ Sum.inl = z := rfl
    have h2 : extVec z 0 ∘ Sum.inr = 0 := rfl
    rw [h1,h2,hz]
    simp [extVec]
    rfl
  unfold gramValue
  rw [extRhs, solve_of_mulVec hdet hsolve]
  simp [extVec, Fintype.sum_sum_type, dotProduct, z]

/-- In a lift B use h=1/√L. On the old nodes this is the trial polynomial
    (1−xh²)u(x) + z h^(2m+1) x^(m+1); the new-node residual is z
    after absorbing 1/L into the row. -/
def liftIntercept (x : I → ℝ) (h : ℝ) : I ⊕ Unit → ℝ :=
  extVec (fun i => 1 - x i * h^2) 0

def liftRows (m : ℕ) (x : I → ℝ) (h : ℝ) : I ⊕ Unit → Fin m ⊕ Unit → ℝ
  | .inl i, .inl j => (1-x i*h^2) * (x i)^(j.val+1)
  | .inl i, .inr _ => h^(2*m+1) * (x i)^(m+1)
  | .inr _, .inl _ => 0
  | .inr _, .inr _ => 1

/-- Limit of the finite dimensional Schur minimum in the rescaled basis.
    The hypothesis on old weights includes the 1/λ factor in (3). -/
theorem liftB_gram_limit {X : Type*} {l : Filter X} (m : ℕ) (x : I → ℝ)
    {h : X → ℝ} (hh : Tendsto h l (𝓝 0))
    {w : X → I → ℝ} {W : I → ℝ} {u : X → ℝ} {η : ℝ}
    (hw : ∀ i, Tendsto (fun t => w t i) l (𝓝 (W i))) (hu : Tendsto u l (𝓝 η))
    (hη : η ≠ 0) (hg : (gram W (fun i (j : Fin m) => (x i)^(j.val+1))).det ≠ 0) :
    Tendsto (fun t => gramValue (extVec (w t) (u t)) (liftIntercept x (h t))
      (liftRows m x (h t))) l
      (𝓝 (gramValue W (fun _ => 1) (fun i (j : Fin m) => (x i)^(j.val+1)))) := by
  let v : I → Fin m → ℝ := fun i j => (x i)^(j.val+1)
  rw [← gramValue_extra W (fun _ => 1) v η hη hg]
  apply gramValue_tendsto
  · intro i; cases i with
    | inl i => exact hw i
    | inr _ => exact hu
  · intro i; cases i with
    | inl i => simpa [liftIntercept, extVec] using
        (tendsto_const_nhds (x:=(1:ℝ))).sub ((tendsto_const_nhds (x:= x i)).mul (hh.pow 2))
    | inr _ => exact tendsto_const_nhds
  · intro i j
    cases i with
    | inr y => cases j <;> exact tendsto_const_nhds
    | inl i =>
      cases j with
      | inl j =>
        simpa [liftRows,extraRows,v] using
          ((tendsto_const_nhds (x:=(1:ℝ))).sub
            ((tendsto_const_nhds (x:= x i)).mul (hh.pow 2))).mul
            (tendsto_const_nhds (x:=(x i)^(j.val+1)))
      | inr _ =>
        simpa [liftRows, extraRows] using
          (hh.pow (2*m+1)).mul (tendsto_const_nhds (x:=(x i)^(m+1)))
  · rw [extGram_det]
    exact mul_ne_zero hg hη


def lsEnergy (w d : I → ℝ) (v : I → K → ℝ) (z : K → ℝ) : ℝ :=
  ∑ i, w i * (d i - (v i ⬝ᵥ z))^2

omit [DecidableEq K] in
private theorem cross (w d : I → ℝ) (v : I → K → ℝ) (z : K → ℝ) :
    ∑ i, w i * d i * (v i ⬝ᵥ z) = rhs w d v ⬝ᵥ z := by
  simp only [rhs,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext j
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq K] in
private theorem crossGram (w : I → ℝ) (v : I → K → ℝ) (u : K → ℝ) :
    rhs w (fun i => v i ⬝ᵥ u) v = gram w v *ᵥ u := by
  funext j
  simp only [rhs,Matrix.mulVec,gram,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq K] in
private theorem energy_expand (w d : I → ℝ) (v : I → K → ℝ) (z : K → ℝ) :
    lsEnergy w d v z = (∑ i, w i*(d i)^2) - 2*(rhs w d v ⬝ᵥ z) +
      (gram w v *ᵥ z) ⬝ᵥ z := by
  rw [← crossGram, ← cross, ← cross, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Formula (5) actually is the attained minimum, including for the
    renormalised augmented rows in lift B. -/
theorem gramValue_isLeast (w d : I → ℝ) (v : I → K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hg : (gram w v).det ≠ 0) :
    IsLeast (Set.range (lsEnergy w d v)) (gramValue w d v) := by
  let z := (gram w v)⁻¹ *ᵥ rhs w d v
  have hz : gram w v *ᵥ z = rhs w d v := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), Matrix.one_mulVec]
  have hval : lsEnergy w d v z = gramValue w d v := by
    unfold gramValue
    rw [energy_expand,hz]
    dsimp [z]
    ring
  refine ⟨⟨z,hval⟩,?_⟩
  rintro _ ⟨y,rfl⟩
  let d' := fun i => d i - (v i ⬝ᵥ z)
  have hres : rhs w d' v = 0 := by
    have r : rhs w d' v = rhs w d v - rhs w (fun i => v i ⬝ᵥ z) v := by
      funext j
      simp [d',rhs,mul_sub,sub_mul,Finset.sum_sub_distrib]
    rw [r,crossGram,hz,sub_self]
  have e : lsEnergy w d v y = lsEnergy w d' v (y-z) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [d',dotProduct_sub]
  have f : lsEnergy w d' v (y-z) =
      lsEnergy w d v z + ∑ i, w i * (v i ⬝ᵥ (y-z))^2 := by
    rw [energy_expand, hres, zero_dotProduct, mul_zero, sub_zero, ← crossGram, ← cross]
    unfold lsEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e, f, hval]
  exact le_add_of_nonneg_right <| Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)


open Polynomial in
/-- The rescaled family used in liftB_gram_limit spans every admissible
    polynomial of degree ≤ m+1, with no exceptional polynomial lost. -/
theorem split_at_new_node (r : ℝ[X]) (m : ℕ) (L : ℝ) (hL : L ≠ 0)
    (hr : r.natDegree ≤ m+1) (h0 : r.eval 0 = 1) :
    ∃ (u : ℝ[X]) (c : ℝ), u.natDegree ≤ m ∧ u.eval 0 = 1 ∧
      r = (1 - C L⁻¹ * X) * u + C c * X^(m+1) := by
  let c := r.eval L / L^(m+1)
  let t := r-C c * X^(m+1)
  have hroot : t.IsRoot L := by
    simp [t,c,Polynomial.IsRoot, div_mul_cancel₀ _ (pow_ne_zero _ hL)]
  obtain ⟨q,hq⟩ := (dvd_iff_isRoot.mpr hroot)
  have ht0 : t.eval 0 = 1 := by simp [t,h0]
  have hq0 : q ≠ 0 := by
    intro e
    simp [e,hq] at ht0
  have ht : t.natDegree ≤ m+1 := by
    apply (natDegree_sub_le _ _).trans
    exact max_le hr <| (natDegree_C_mul_le _ _).trans <| by simp
  rw [hq,Polynomial.natDegree_mul (X_sub_C_ne_zero _) hq0, natDegree_X_sub_C] at ht
  refine ⟨C (-L)*q,c,(natDegree_C_mul_le _ _).trans (by omega),?_,?_⟩
  · simpa [hq] using ht0
  · have hs : (1 - C L⁻¹ * X) * C (-L) = (X - C L : ℝ[X]) := by
      have hi : C L⁻¹ * C L = (1 : ℝ[X]) := by
        rw [← C_mul,inv_mul_cancel₀ hL,C_1]
      rw [C_neg]; linear_combination X * hi
    rw [← mul_assoc,hs, ← hq]
    simp [t]


/-- Lift B in the inverse coordinate h=1/√L. The following are (7)
    divided by h^4; using the factored products removes all divergent powers. -/
def oldB (n : ℕ) (ε a x h : ℝ) : ℝ :=
  a / ((1-x*h^2)*(1-(h^2)^(2*n-7)/ε*h^2-x*h^2))

def newB {J : Type*} [Fintype J] (v : I → ℝ) (u : J → ℝ) (ε t p h : ℝ) : ℝ :=
  ε * (1-t*h^2+p*h^4) /
    ((∏ i, (1-v i*h^2)) * (∏ j, (1-u j*h^2)))

theorem oldB_zero (n : ℕ) (ε a x : ℝ) : oldB n ε a x 0 = a := by simp [oldB]

theorem newB_zero {J : Type*} [Fintype J] (v : I → ℝ) (u : J → ℝ) (ε t p : ℝ) :
    newB v u ε t p 0 = ε := by simp [newB]

theorem oldB_cont (n : ℕ) (ε a x : ℝ) : ContinuousAt (oldB n ε a x) 0 := by
  unfold oldB
  fun_prop (disch := norm_num)

theorem newB_cont {J : Type*} [Fintype J] (v : I → ℝ) (u : J → ℝ) (ε t p : ℝ) :
    ContinuousAt (newB v u ε t p) 0 := by
  unfold newB
  fun_prop (disch := norm_num)

def totalB {J : Type*} [Fintype J] (n : ℕ) (x a : I → ℝ) (u : J → ℝ)
    (ε t p h : ℝ) : ℝ :=
  (∑ i, oldB n ε (a i) (x i) h) + newB x u ε t p h

theorem totalB_zero {J : Type*} [Fintype J] (n : ℕ) (x a : I → ℝ) (u : J → ℝ)
    (ε t p : ℝ) : totalB n x a u ε t p 0 = (∑ i, a i) + ε := by
  simp [totalB,oldB_zero,newB_zero]

theorem totalB_cont {J : Type*} [Fintype J] (n : ℕ) (x a : I → ℝ) (u : J → ℝ)
    (ε t p : ℝ) : ContinuousAt (totalB n x a u ε t p) 0 :=
  (tendsto_finset_sum _ fun i _ => (oldB_cont n ε (a i) (x i)).tendsto).add (newB_cont x u ε t p)

theorem gramValue_scale (w d : I → ℝ) (v : I → K → ℝ) (s : ℝ)
    (hs : 0 < s) (hw : ∀ i, 0 ≤ w i) (hg : (gram w v).det ≠ 0) :
    gramValue (fun i => s*w i) d v = s*gramValue w d v := by
  have hG : gram (fun i => s*w i) v = s • gram w v := by
    ext j k
    simp [gram, Finset.mul_sum, mul_assoc]
  have hsG : (gram (fun i => s*w i) v).det ≠ 0 := by
    rw [hG,Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs.ne') hg
  have he (z : K → ℝ) : lsEnergy (fun i => s*w i) d v z = s*lsEnergy w d v z := by
    simp [lsEnergy,Finset.mul_sum,mul_assoc]
  have ho := gramValue_isLeast w d v hw hg
  have hn := gramValue_isLeast (fun i => s*w i) d v (fun i => mul_nonneg hs.le (hw i)) hsG
  obtain ⟨zo,hzo⟩ := ho.1
  obtain ⟨zn,hzn⟩ := hn.1
  apply le_antisymm
  · exact (hn.2 ⟨zo,rfl⟩).trans_eq ((he zo).trans (by rw [hzo]))
  · rw [← hzn,he]
    exact mul_le_mul_of_nonneg_left (ho.2 ⟨zn,rfl⟩) hs.le


/-- Augmented quantity (5) after the basis change and the exact mass
    rescaling in (7), written at h=1/√L so its limit is a finite point. -/
def liftBValue {J : Type*} [Fintype J] (n m : ℕ) (x a : I → ℝ) (y : J → ℝ)
    (ε t p h : ℝ) : ℝ :=
  let S := totalB n x a y ε t p h
  gramValue (extVec (fun i => oldB n ε (a i) (x i) h / S / x i)
    (newB x y ε t p h / S)) (liftIntercept x h) (liftRows m x h)

/-- Formula (8) for the explicit rational weights and augmented least-squares
    rows. The original normalized Gram determinant is the only invertibility
    assumption. -/
theorem liftB_explicit_limit {J : Type*} [Fintype J] (n m : ℕ)
    (x a : I → ℝ) (y : J → ℝ) (ε t p : ℝ)
    (hε : 0 < ε) (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 < x i)
    (hS : 0 < ∑ i, a i)
    (hg : (gram (fun i => a i / (∑ j, a j) / x i)
      (fun i (j : Fin m) => (x i)^(j.val+1))).det ≠ 0) :
    Tendsto (liftBValue n m x a y ε t p) (𝓝 0)
      (𝓝 (((∑ j, a j) / ((∑ j, a j) + ε)) *
        gramValue (fun i => a i / (∑ j, a j) / x i)
        (fun _ => 1) (fun i (j : Fin m) => (x i)^(j.val+1)))) := by
  let S := ∑ j, a j
  let s := S/(S+ε)
  let w := fun i => a i / S / x i
  let V := fun i (j : Fin m) => (x i)^(j.val+1)
  have hS' : 0 < S := hS
  have hT : 0 < S+ε := by positivity
  have hs : 0 < s := div_pos hS' hT
  have hw : ∀ i, 0 ≤ w i :=
    fun i => div_nonneg (div_nonneg (ha i) hS'.le) (hx i).le
  have hGr : (gram w V).det ≠ 0 := hg
  have hG : gram (fun i => s*w i) V = s • gram w V := by
    ext j k
    simp [gram,Finset.mul_sum,mul_assoc]
  have hGram : (gram (fun i => s*w i) V).det ≠ 0 := by
    rw [hG, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs.ne') hGr
  change Tendsto _ _ (𝓝 (s * gramValue w (fun _ => 1) V))
  rw [← gramValue_scale w (fun _ => 1) V s hs hw hGr]
  have htot : Tendsto (totalB n x a y ε t p) (𝓝 0) (𝓝 (S+ε)) := by
    simpa only [totalB_zero] using (totalB_cont n x a y ε t p).tendsto
  apply liftB_gram_limit (m:=m) (x:=x) (h:=fun h : ℝ => h) (η:=ε/(S+ε))
    tendsto_id ?_ ?_ (div_ne_zero hε.ne' hT.ne') hGram
  · intro i
    have hA : Tendsto (oldB n ε (a i) (x i)) (𝓝 0) (𝓝 (a i)) := by
      simpa only [oldB_zero] using (oldB_cont n ε (a i) (x i)).tendsto
    have eq : s*w i = a i / (S+ε) / x i := by
      dsimp only [s,w]
      field_simp [hS'.ne',hT.ne',(hx i).ne']
      ring
    rw [eq]
    exact (hA.div htot hT.ne').div_const (x i)
  · have hA : Tendsto (newB x y ε t p) (𝓝 0) (𝓝 ε) := by
      simpa only [newB_zero] using (newB_cont x y ε t p).tendsto
    exact hA.div htot hT.ne'


/-- Positivity and unisolvence make the Gram system invertible. -/
theorem gram_nonsingular (w : I → ℝ) (v : I → K → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ z : K → ℝ, (∀ i, v i ⬝ᵥ z = 0) → z = 0) :
    (gram w v).det ≠ 0 := by
  have kernel (z : K → ℝ) (hz : gram w v *ᵥ z = 0) : z = 0 := by
    have eq : ∑ i, w i * (v i ⬝ᵥ z)^2 = 0 := by
      have t := cross w (fun i => v i ⬝ᵥ z) v z
      simpa [crossGram, hz, pow_two, mul_assoc] using t
    apply hv z
    intro i
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw j).le (sq_nonneg (v j ⬝ᵥ z)))).mp eq i (Finset.mem_univ _)
    exact (sq_eq_zero_iff).mp <| (mul_eq_zero.mp h).resolve_left (hw i).ne'
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u z huz
  exact sub_eq_zero.mp (kernel (u-z) (by rw [Matrix.mulVec_sub,huz,sub_self]))

theorem monomial_gram_nonsingular {n m : ℕ} (hmn : m ≤ n) (w x : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, x i ≠ 0) (hd : Function.Injective x) :
    (gram w (fun i (j : Fin m) => (x i)^(j.val+1))).det ≠ 0 := by
  apply gram_nonsingular _ _ hw
  intro z hz
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (hd.comp e.injective)
  intro i
  have h : (∑ j : Fin m, (x (e i))^(j.val+1) * z j) = 0 := hz (e i)
  have h' : x (e i) * (∑ j : Fin m, (x (e i))^j.val * z j) = 0 := by
    rw [Finset.mul_sum]
    convert h using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  exact (mul_eq_zero.mp h').resolve_left (hx _)


/-- Adding a zero data row has no effect even if its row weight is nonzero. -/
theorem gramValue_zeroRow (w d : I → ℝ) (v : I → K → ℝ) (c : ℝ) :
    gramValue (extVec w c) (extVec d 0) (Sum.elim v fun _ : Unit => 0) = gramValue w d v := by
  have g : gram (extVec w c) (Sum.elim v fun _ : Unit => 0) = gram w v := by
    ext j k
    simp [gram,extVec,Fintype.sum_sum_type]
  have b : rhs (extVec w c) (extVec d 0) (Sum.elim v fun _ : Unit => 0) = rhs w d v := by
    ext j
    simp [rhs,extVec,Fintype.sum_sum_type]
  unfold gramValue
  rw [g,b]
  simp [extVec,Fintype.sum_sum_type]

/-- Rescaled lift A, h=1/√L. The new row weight is bounded after taking
    h^(2n-5) into its row, while all new-row monomials vanish for ℓ≥3. -/
theorem liftA_gram_limit {X : Type*} {l : Filter X} (n m : ℕ) (hm : m+3 ≤ n)
    (x : I → ℝ) {h : X → ℝ} (hh : Tendsto h l (𝓝 0))
    {w : X → I → ℝ} {W : I → ℝ} {u : X → ℝ} {η : ℝ}
    (hw : ∀ i, Tendsto (fun t => w t i) l (𝓝 (W i))) (hu : Tendsto u l (𝓝 η))
    (hg : (gram W (fun i (j : Fin m) => (x i)^(j.val+1))).det ≠ 0) :
    Tendsto (fun t => gramValue (extVec (w t) (u t)) (extVec (fun _ => 1) ((h t)^(2*n-5)))
      (Sum.elim (fun i (j : Fin m) => (x i)^(j.val+1))
        (fun (_ : Unit) (j : Fin m) => (h t)^(2*n-(7+2*j.val))))) l
      (𝓝 (gramValue W (fun _ => 1) (fun i (j : Fin m) => (x i)^(j.val+1)))) := by
  let v := fun (i : I) (j : Fin m) => (x i)^(j.val+1)
  rw [← gramValue_zeroRow W (fun _ => 1) v η]
  apply gramValue_tendsto
  · rintro (i|u')
    · exact hw i
    · exact hu
  · rintro (i|u')
    · exact tendsto_const_nhds
    · simpa [extVec,zero_pow (show 2*n-5 ≠ 0 by omega)] using hh.pow (2*n-5)
  · rintro (i|u') j
    · exact tendsto_const_nhds
    · have hj := j.isLt
      simpa [zero_pow (show 2*n-(7+2*j.val) ≠ 0 by omega)] using hh.pow (2*n-(7+2*j.val))
  · have heq : gram (extVec W η) (Sum.elim v fun _ : Unit => 0) = gram W v := by
      ext j k
      simp [gram, extVec,Fintype.sum_sum_type]
    rwa [heq]

end Catenary.GlobalLift
