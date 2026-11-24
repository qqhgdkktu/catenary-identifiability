import Chain.ResolventData
import Chain.Polynomial
import Chain.Continuant
import Chain.WitnessVariation
import Chain.PolynomialReconstruction
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Eliminating a prefix joined by a single symmetric edge. Throughout the
block matrix represents the negative Jacobi matrix; the two off-diagonal
entries at the cut are both `-c`. -/

noncomputable section

open Polynomial Matrix Filter Set
open scoped Matrix Polynomial Topology
namespace Catenary.PrefixExtension

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def connected (A : Matrix I I ℝ) (T : Matrix J J ℝ) (p : I) (e : J) (c : ℝ) :
    Matrix (I ⊕ J) (I ⊕ J) ℝ :=
  fromBlocks A (stdBasisMatrix p e (-c)) (stdBasisMatrix e p (-c)) T

def corrected (T : Matrix J J ℝ) (e : J) (q : ℝ) : Matrix J J ℝ :=
  T - stdBasisMatrix e e q

private theorem rows (A : Matrix I I ℝ) (T : Matrix J J ℝ) (p : I) (e : J) (c : ℝ)
    (x b : I → ℝ) (y h : J → ℝ)
    (heq : (connected A T p e c) *ᵥ Sum.elim x y = Sum.elim b h) :
    A *ᵥ x = b + Pi.single p (c * y e) ∧ T *ᵥ y = h + Pi.single e (c * x p) := by
  rw [connected, fromBlocks_mulVec] at heq
  constructor
  · ext j
    have v := congrFun heq (Sum.inl j)
    by_cases hj : j = p
    · subst j
      simp [mulVec_stdBasisMatrix, Function.comp_def] at v ⊢
      linarith
    · simpa [mulVec_stdBasisMatrix, Function.comp_def, Pi.single_eq_of_ne hj, hj] using v
  · ext j
    have v := congrFun heq (Sum.inr j)
    by_cases hj : j = e
    · subst j
      simp [mulVec_stdBasisMatrix, Function.comp_def] at v ⊢
      linarith
    · simpa [mulVec_stdBasisMatrix, Function.comp_def, Pi.single_eq_of_ne hj, hj] using v

private theorem solve_entry {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.det ≠ 0) (x : I → ℝ) (p j : I) (t : ℝ)
    (h : A *ᵥ x = Pi.single p t) : x j = A⁻¹ j p * t := by
  have hh := congrArg (fun v => A⁻¹ *ᵥ v) h
  dsimp only at hh
  rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA), one_mulVec, mulVec_single] at hh
  exact congrFun hh j

/-- If the leak is in the discarded prefix, the entire tail is the first
column of its own inverse scaled by the same `c * x p`. -/
theorem left_leak_tail (A : Matrix I I ℝ) (T : Matrix J J ℝ) (p ℓ : I) (e : J) (c : ℝ)
    (x : I → ℝ) (y : J → ℝ) (hT : T.det ≠ 0)
    (h : connected A T p e c *ᵥ Sum.elim x y = Sum.elim (Pi.single ℓ 1) 0) (v : J) :
    y v = T⁻¹ v e * (c * x p) := by
  have z := (rows A T p e c x _ y _ h).2
  rw [zero_add] at z
  exact solve_entry T hT y e v _ z

/-- The scalar in the preceding formula cancels in the physical gain,
including when the original leak is many vertices to the left. -/
theorem left_leak_gain (A : Matrix I I ℝ) (T : Matrix J J ℝ) (p ℓ : I) (e v : J)
    (c g : ℝ) (x : I → ℝ) (y : J → ℝ) (hT : T.det ≠ 0) (hy : y e ≠ 0)
    (h : connected A T p e c *ᵥ Sum.elim x y = Sum.elim (Pi.single ℓ 1) 0) :
    g * y v / y e = g * T⁻¹ v e / T⁻¹ e e := by
  have hv := left_leak_tail A T p ℓ e c x y hT h v
  have he := left_leak_tail A T p ℓ e c x y hT h e
  rw [he] at hy
  obtain ⟨hn, hk⟩ := mul_ne_zero_iff.mp hy
  rw [hv,he]
  rw [← mul_assoc, mul_div_mul_right _ _ hk]

/-- If the leak is in the tail, its equation is the Schur complement with
the negative rank-one correction, for an arbitrary invertible prefix. -/
theorem right_leak_schur (A : Matrix I I ℝ) (T : Matrix J J ℝ) (p : I) (e ℓ : J) (c : ℝ)
    (x : I → ℝ) (y : J → ℝ) (hA : A.det ≠ 0)
    (h : connected A T p e c *ᵥ Sum.elim x y = Sum.elim (0 : I → ℝ) (Pi.single ℓ 1)) :
    corrected T e (c^2 * A⁻¹ p p) *ᵥ y = Pi.single ℓ 1 := by
  obtain ⟨ha,ht⟩ := rows A T p e c x _ y _ h
  rw [zero_add] at ha
  have xp := solve_entry A hA x p p _ ha
  ext j
  rw [corrected, sub_mulVec, ht, mulVec_stdBasisMatrix]
  by_cases hj : j = e
  · subst j
    simp [xp]
    ring
  · simp [hj, Pi.single_eq_of_ne hj]

/-- The self-transfer of the last prefix site is exactly the previous
principal minor divided by the full determinant, also for a one-site prefix. -/
theorem inverse_last {p : ℕ} (L : Matrix (Fin (p+1)) (Fin (p+1)) ℝ) :
    (-L)⁻¹ (Fin.last p) (Fin.last p) =
      ((L.submatrix Fin.castSucc Fin.castSucc).charpoly.eval 0) / (L.charpoly.eval 0) := by
  simp only [TransferData.eval_charpoly_eq_det,zero_smul,zero_sub]
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    adjugate_fin_succ_eq_det_submatrix]
  have sign : (-1 : ℝ)^((Fin.last p).val+(Fin.last p).val)=1 := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [sign, one_mul, Fin.succAbove_last]
  change (-L).det⁻¹ * (-(L.submatrix Fin.castSucc Fin.castSucc)).det = _
  ring

abbrev prefixPoly {p : ℕ} (L : Matrix (Fin (p+1)) (Fin (p+1)) ℝ) := L.charpoly

def couplingPoly {p : ℕ} (L : Matrix (Fin (p+1)) (Fin (p+1)) ℝ) (c : ℝ) : ℝ[X] :=
  C (c^2) * (L.submatrix Fin.castSucc Fin.castSucc).charpoly

/-- In the monic coefficient coordinates of §7 the exact correction factor
is `V(0) / S(0)`, rather than an expression containing the square root edge. -/
theorem right_leak_schur_polynomials {p : ℕ} (L : Matrix (Fin (p+1)) (Fin (p+1)) ℝ)
    (T : Matrix J J ℝ) (e ℓ : J) (c : ℝ) (x : Fin (p+1) → ℝ) (y : J → ℝ)
    (hL : (-L).det ≠ 0) (h : connected (-L) T (Fin.last p) e c *ᵥ Sum.elim x y =
      Sum.elim (0 : Fin (p+1) → ℝ) (Pi.single ℓ 1)) :
    corrected T e ((couplingPoly L c).eval 0 / (prefixPoly L).eval 0) *ᵥ y = Pi.single ℓ 1 := by
  have hh := right_leak_schur (-L) T (Fin.last p) e ℓ c x y hL h
  simpa only [couplingPoly,prefixPoly,eval_mul,eval_C,inverse_last, mul_div_assoc] using hh

section Signed
open Continuant
variable {K : Type*} [Field K]

/-- The replacement changes only the outgoing edge, which does not enter the
determinant of the prefix itself. -/
def linkSite (u : PathSite K) (β : K) : PathSite K := ⟨u.diag, β, 1⟩

def shiftDiagonal (v : PathSite K) (q : K) : PathSite K := ⟨v.diag-q, v.upper, v.lower⟩

theorem same_last (left : List (PathSite K)) (u : PathSite K) (β : K) :
    intervalCharpoly (left ++ [linkSite u β]) = intervalCharpoly (left ++ [u]) := by
  simp only [intervalCharpoly,charpoly_eq_cont,List.map_append,List.map_cons,List.map_nil,
    cont,run_append,run,step, mul_one,mul_zero,sub_zero]
  rfl

theorem shift_first (v : PathSite K) (right : List (PathSite K)) (q : K) :
    intervalCharpoly (shiftDiagonal v q :: right) =
      intervalCharpoly (v :: right) + C q * intervalCharpoly right := by
  simp only [intervalCharpoly,charpoly_eq_cont,List.map_cons,cont,run,step,pencilSite,
    shiftDiagonal,PathSite.weight,map_sub]
  ring

/-- Full spectral polynomial after adding a prefix, a signed nonzero edge
product, and a compensating shift of the first tail diagonal. -/
theorem signed_splice (left right : List (PathSite K)) (u v : PathSite K) (β q : K) :
    intervalCharpoly (left ++ linkSite u β :: shiftDiagonal v q :: right) =
      intervalCharpoly (left ++ [u]) *
        (intervalCharpoly (v :: right) + C q * intervalCharpoly right) -
      C β * intervalCharpoly left * intervalCharpoly right := by
  have h := charpoly_cut left right (linkSite u β) (shiftDiagonal v q)
  change intervalCharpoly (left ++ linkSite u β :: shiftDiagonal v q :: right) =
    intervalCharpoly (left ++ [linkSite u β]) * intervalCharpoly (shiftDiagonal v q :: right) -
    C (linkSite u β).weight * intervalCharpoly left * intervalCharpoly right at h
  rw [same_last, shift_first] at h
  simpa only [linkSite,PathSite.weight,mul_one] using h

def compensation (left : List (PathSite K)) (u : PathSite K) (β : K) : K :=
  β * (intervalCharpoly left).eval 0 / (intervalCharpoly (left ++ [u])).eval 0

/-- The same central diagonal shift preserves every tail leading principal
minor at zero up to the nonzero prefix factor. In particular it preserves a
zero full determinant along the entire signed path, including at nonzero β. -/
theorem signed_splice_at_zero (left right : List (PathSite K)) (u v : PathSite K) (β : K)
    (hS : (intervalCharpoly (left ++ [u])).eval 0 ≠ 0) :
    (intervalCharpoly (left ++ linkSite u β ::
      shiftDiagonal v (compensation left u β) :: right)).eval 0 =
       (intervalCharpoly (left ++ [u])).eval 0 * (intervalCharpoly (v :: right)).eval 0 := by
  rw [signed_splice]
  simp only [eval_sub,eval_mul,eval_add,eval_C,compensation]
  field_simp
  ring

/-- Simultaneous preservation for all the leading subchains of one tail,
with the same physical perturbation at the seam. -/
theorem signed_splice_all_prefixes (left right : List (PathSite K)) (u v : PathSite K) (β : K)
    (hS : (intervalCharpoly (left ++ [u])).eval 0 ≠ 0) (k : ℕ) :
    (intervalCharpoly (left ++ linkSite u β :: shiftDiagonal v (compensation left u β) ::
      right.take k)).eval 0 = (intervalCharpoly (left ++ [u])).eval 0 *
      (intervalCharpoly (v :: right.take k)).eval 0 :=
  signed_splice_at_zero left (right.take k) u v β hS

open WitnessVariation

/-- The linearized polynomial gluing step in the independent coordinates
`(S,V,tail)`. These are actual coefficient derivatives of polynomial paths.
The family `P` includes both signed gains' leading determinants. -/
theorem signed_velocity_lift {α : Type*} (t : K) (S V D R : Family K) (P Q : α → Family K)
    (hS0 : (value t S).eval 0 ≠ 0) (hV0 : value t V = 0)
    (hcop : IsCoprime (value t S) (value t R)) (hdeg : (velocity t V).degree < (value t S).degree)
    (hS : velocity t S = 0) (hD : velocity t (S * D - V * R) = 0)
    (hP : ∀ a, (velocity t (S * P a - V * Q a)).eval 0 = 0) :
    velocity t V = 0 ∧ velocity t D = 0 ∧ ∀ a, (velocity t (P a)).eval 0 = 0 := by
  have hSn : value t S ≠ 0 := fun h => hS0 (by simp [h])
  simp only [velocity_sub,velocity_mul,hV0,hS,zero_mul,zero_add,add_zero,sub_eq_zero] at hD
  obtain ⟨hv,hd⟩ := prefix_tangent_kernel hSn hcop hdeg hD
  refine ⟨hv,hd,fun a => ?_⟩
  have e := hP a
  simp only [velocity_sub,velocity_mul,hV0,hS,hv,zero_mul,zero_add,add_zero,sub_zero,
    eval_mul] at e
  exact (mul_eq_zero.mp e).resolve_left hS0

end Signed

section Coordinates
variable {R : Type*} [CommRing R] [Nontrivial R]

/-- At a nonzero bridge weight, the two prefix coordinates recover the whole
Jacobi block and the bridge. This also holds over the dual numbers, so it
recovers first variations wherever the bridge really is present. -/
theorem recover_prefix_coordinates {p : ℕ} (b d : Rˣ) (x y : JacobiData R p)
    (hs : x.boundaryPair.1 = y.boundaryPair.1)
    (hv : C (b : R) * x.boundaryPair.2 = C (d : R) * y.boundaryPair.2) :
    b = d ∧ x = y := by
  have hb : b = d := by
    apply Units.ext
    have m₁ : x.boundaryPair.2.Monic := Matrix.charpoly_monic _
    have m₂ : y.boundaryPair.2.Monic := Matrix.charpoly_monic _
    simpa only [leadingCoeff_C_mul_of_isUnit b.isUnit,leadingCoeff_C_mul_of_isUnit d.isUnit,
      m₁.leadingCoeff,m₂.leadingCoeff,mul_one] using congrArg leadingCoeff hv
  subst d
  exact ⟨rfl,JacobiData.boundaryPair_injective _ (Prod.ext hs
    ((b.isUnit.map (C : R →+* R[X])).mul_left_cancel hv))⟩
end Coordinates

section SampleChart

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Coefficient coordinates can equally be their values at distinct fixed
nodes. The input stores the variations of the monic prefix and the coupling
polynomial at the prefix roots, followed by the tail parameters. The first
group of determinant observations is sampled at those roots. The remaining
rows comprise tail denominator samples and the two leading determinants at
zero. `ev` evaluates an interpolated polynomial on those remaining rows. -/
def sampleChart (ev : κ → (ι → ℝ) →L[ℝ] ℝ) (base : κ → ℝ)
    (A R : E → ι → ℝ) (Q : E → κ → ℝ) (H : E → (κ → ℝ) × Z) :
    (ι → ℝ) × (ι → ℝ) × E → (ι → ℝ) × (ι → ℝ) × (κ → ℝ) × Z := fun z =>
  (z.1, fun i => z.1 i * A z.2.2 i - z.2.1 i * R z.2.2 i,
    fun j => (base j + ev j z.1) * (H z.2.2).1 j - ev j z.2.1 * Q z.2.2 j,
    (H z.2.2).2)

theorem sampleChart_smooth (ev : κ → (ι → ℝ) →L[ℝ] ℝ) (base : κ → ℝ)
    (A R : E → ι → ℝ) (Q : E → κ → ℝ) (H : E → (κ → ℝ) × Z)
    (hA : ContDiff ℝ 1 A) (hR : ContDiff ℝ 1 R)
    (hQ : ContDiff ℝ 1 Q) (hH : ContDiff ℝ 1 H) :
    ContDiff ℝ 1 (sampleChart ev base A R Q H) := by
  unfold sampleChart
  let X := (ι → ℝ) × (ι → ℝ) × E
  have hs : ContDiff ℝ 1 (fun z : X => z.1) := contDiff_fst
  have hv : ContDiff ℝ 1 (fun z : X => z.2.1) := contDiff_snd.fst
  have ht : ContDiff ℝ 1 (fun z : X => z.2.2) := contDiff_snd.snd
  apply hs.prodMk
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    exact ((contDiff_pi.mp hs i).mul (contDiff_pi.mp (hA.comp ht) i)).sub
      ((contDiff_pi.mp hv i).mul (contDiff_pi.mp (hR.comp ht) i))
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    exact ((contDiff_const.add ((ev j).contDiff.comp hs)).mul
      (contDiff_pi.mp (hH.comp ht).fst j)).sub
      (((ev j).contDiff.comp hv).mul (contDiff_pi.mp (hQ.comp ht) j))
  · exact (hH.comp ht).snd

/-- Evaluation on a new row after interpolation from all prefix roots. -/
def interpolateAt [DecidableEq ι] (nodes : ι → ℝ) (z : ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ((Polynomial.leval z).comp (Lagrange.interpolate Finset.univ nodes)).toContinuousLinearMap

theorem interpolateAt_exact [DecidableEq ι] (nodes : ι → ℝ) (hn : Function.Injective nodes)
    (p : ℝ[X]) (hp : p.degree < Fintype.card ι) (z : ℝ) :
    interpolateAt nodes z (fun i => p.eval (nodes i)) = p.eval z := by
  have h := Lagrange.eq_interpolate (s:=Finset.univ) (v:=nodes) hn.injOn
    (by simpa using hp : p.degree < Finset.univ.card)
  exact congrArg (Polynomial.eval z) h.symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Fintype κ] in
/-- The finite chart is exactly the normalized physical polynomial gluing
formula on every sampled row. Different types of rows may use the same
spectral value (for instance the two measured leading determinants at zero). -/
theorem sampleChart_exact [DecidableEq ι] (nodes : ι → ℝ) (hn : Function.Injective nodes)
    (rows : κ → ℝ) (S s v : ℝ[X]) (hz : ∀ i, S.eval (nodes i) = 0)
    (hs : (s-S).degree < Fintype.card ι) (hv : v.degree < Fintype.card ι)
    (D R : E → ℝ[X]) (P Q : E → κ → ℝ[X]) (B : E → Z) (x : E) :
    sampleChart (fun j => interpolateAt nodes (rows j)) (fun j => S.eval (rows j))
      (fun y i => (D y).eval (nodes i)) (fun y i => (R y).eval (nodes i))
      (fun y j => (Q y j).eval (rows j)) (fun y => (fun j => (P y j).eval (rows j), B y))
      ((fun i => (s-S).eval (nodes i)), (fun i => v.eval (nodes i)), x) =
      ((fun i => s.eval (nodes i)), (fun i => (s * D x - v * R x).eval (nodes i)),
       (fun j => (s * P x j - v * Q x j).eval (rows j)), B x) := by
  unfold sampleChart
  apply Prod.ext
  · funext i
    simp [hz]
  apply Prod.ext
  · funext i
    simp [hz]
  apply Prod.ext
  · funext j
    dsimp only
    rw [interpolateAt_exact _ hn _ hs, interpolateAt_exact _ hn _ hv]
    simp [eval_sub, eval_mul]
  · rfl

private theorem first_derivative {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : ℝ → U × V} {y : U × V}
    (h : HasDerivAt f y 0) : HasDerivAt (fun t => (f t).1) y.1 0 :=
  (ContinuousLinearMap.fst ℝ U V).hasFDerivAt.comp_hasDerivAt 0 h

private theorem second_derivative {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : ℝ → U × V} {y : U × V}
    (h : HasDerivAt f y 0) : HasDerivAt (fun t => (f t).2) y.2 0 :=
  (ContinuousLinearMap.snd ℝ U V).hasFDerivAt.comp_hasDerivAt 0 h

private theorem line_deriv (a w : E) : HasDerivAt (fun t : ℝ => a+t • w) w 0 := by
  simpa only [one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add a

private theorem zero_line_deriv (w : E) : HasDerivAt (fun t : ℝ => t • w) w 0 := by
  simpa only [one_smul] using (hasDerivAt_id (0:ℝ)).smul_const w

/-- A true Fréchet-rank inheritance theorem. An injective tail differential,
nonvanishing adjacent determinant at each prefix root, and nonvanishing
prefix factor on the retained samples give an injective differential of the
whole extended map at zero coupling. -/
theorem sampleChart_rank (ev : κ → (ι → ℝ) →L[ℝ] ℝ) (base : κ → ℝ)
    (A R : E → ι → ℝ) (Q : E → κ → ℝ) (H : E → (κ → ℝ) × Z) (a : E)
    (hbase : ∀ j, base j ≠ 0) (hR : ∀ i, R a i ≠ 0)
    (hr : DifferentiableAt ℝ R a) (hh : DifferentiableAt ℝ H a)
    (hchart : DifferentiableAt ℝ (sampleChart ev base A R Q H) (0,0,a))
    (hinj : Function.Injective (fderiv ℝ H a)) :
    Function.Injective (fderiv ℝ (sampleChart ev base A R Q H) (0,0,a)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  rintro ⟨s,v,w⟩ hker
  change fderiv ℝ (sampleChart ev base A R Q H) (0,0,a) (s,v,w) = 0 at hker
  let line := fun t : ℝ => (t • s, t • v, a+t • w)
  have dl : HasDerivAt line (s,v,w) 0 :=
    (zero_line_deriv s).prodMk ((zero_line_deriv v).prodMk (line_deriv a w))
  have cl : line 0 = (0,0,a) := by simp [line]
  have z := hchart.hasFDerivAt.comp_hasDerivAt_of_eq 0 dl cl.symm
  rw [hker] at z
  have hs : s = 0 := (zero_line_deriv s).unique (first_derivative z)
  subst s
  have rpath := hr.hasFDerivAt.comp_hasDerivAt_of_eq 0 (line_deriv a w) (by simp)
  have hv : v = 0 := by
    funext i
    have hz := hasDerivAt_pi.mp (first_derivative (second_derivative z)) i
    have dh := ((hasDerivAt_pi.mp (zero_line_deriv v) i).mul (hasDerivAt_pi.mp rpath i)).neg
    have dh' : HasDerivAt (fun t : ℝ => -((t • v) i * R (a+t • w) i)) (-(v i * R a i)) 0 := by
      simpa [Function.comp_def] using dh
    have hz' : HasDerivAt (fun t : ℝ => -((t • v) i * R (a+t • w) i)) 0 0 := by
      simpa [Function.comp_def,line,sampleChart] using hz
    exact (mul_eq_zero.mp (neg_eq_zero.mp (dh'.unique hz'))).resolve_right (hR i)
  subst v
  have hpath := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 (line_deriv a w) (by simp)
  have hc : (fderiv ℝ H a w).1 = 0 := by
    funext j
    have hz := hasDerivAt_pi.mp (first_derivative (second_derivative (second_derivative z))) j
    have dh := (hasDerivAt_pi.mp (first_derivative hpath) j).const_mul (base j)
    have hz' : HasDerivAt (fun t : ℝ => base j * (H (a+t • w)).1 j) 0 0 := by
      simpa [Function.comp_def,line,sampleChart] using hz
    exact (mul_eq_zero.mp (dh.unique hz')).resolve_left (hbase j)
  have hu : (fderiv ℝ H a w).2 = 0 :=
    (second_derivative hpath).unique (second_derivative (second_derivative (second_derivative z)))
  have hw : w = 0 := hinj (by rw [map_zero]; exact Prod.ext hc hu)
  simp [hw]

end SampleChart

/-- For a finite-dimensional source, full differential rank survives along
any continuous matrix path through the separated point. The bridge can be
taken strictly positive and arbitrarily small. -/
theorem positive_rank_persistence {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → E →L[ℝ] F) (hA : ContinuousAt A 0) (hinj : Function.Injective (A 0)) :
    ∀ δ : ℝ, 0 < δ → ∃ β : ℝ, 0 < β ∧ β < δ ∧ Function.Injective (A β) := by
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), Function.Injective (A s) :=
    hA (ContinuousLinearMap.isOpen_injective.mem_nhds hinj)
  intro δ hδ
  obtain ⟨ε,hε,hs⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let β := min δ ε / 2
  have hβ : 0 < β := half_pos (lt_min hδ hε)
  have hlt : β < min δ ε := half_lt_self (lt_min hδ hε)
  refine ⟨β,hβ,hlt.trans_le (min_le_left _ _),hs β ?_⟩
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hβ] using
    hlt.trans_le (min_le_right _ _)

/-- Direct transfer of a full-rank endpoint witness onto the signed gluing
line. The second component is the vector of values of `β Lprev`; the last
component is the affine central-diagonal adjustment.

Together with `sampleChart_exact` and `signed_splice_all_prefixes`, this
keeps the full zero eigenvalue and all proper nonzero leading minors of a
signed Jacobi witness while restoring a strictly positive bridge weight. -/
theorem signed_chart_witness {E Z ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Fintype ι] [Fintype κ]
    (ev : κ → (ι → ℝ) →L[ℝ] ℝ) (base : κ → ℝ) (A R : E → ι → ℝ)
    (Q : E → κ → ℝ) (H : E → (κ → ℝ) × Z) (a shift : E) (leftMinor : ι → ℝ)
    (hA : ContDiff ℝ 1 A) (hR : ContDiff ℝ 1 R) (hQ : ContDiff ℝ 1 Q) (hH : ContDiff ℝ 1 H)
    (hbase : ∀ j, base j ≠ 0) (hr : ∀ i, R a i ≠ 0) (hinj : Function.Injective (fderiv ℝ H a))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ β : ℝ, 0 < β ∧ β < δ ∧ Function.Injective (fderiv ℝ (sampleChart ev base A R Q H)
      (0, β • leftMinor, a+β • shift)) := by
  let phi := sampleChart ev base A R Q H
  have hphi : ContDiff ℝ 1 phi := sampleChart_smooth ev base A R Q H hA hR hQ hH
  have h0 := sampleChart_rank ev base A R Q H a hbase hr (hR.differentiable le_rfl a)
    (hH.differentiable le_rfl a) (hphi.differentiable le_rfl _) hinj
  let path := fun β : ℝ => ((0 : ι → ℝ), β • leftMinor, a+β • shift)
  have hp : Continuous path :=
    continuous_const.prodMk ((continuous_id.smul continuous_const).prodMk
      (continuous_const.add (continuous_id.smul continuous_const)))
  have hc : Continuous (fderiv ℝ phi) :=
    (hphi.fderiv_right (m:=0) (by simp)).continuous
  exact positive_rank_persistence (fun x => fderiv ℝ phi (path x))
    (hc.continuousAt.comp hp.continuousAt) (by simpa [path,phi] using h0) δ hδ

end Catenary.PrefixExtension
