import Chain.ResolventFormula
import Chain.ResolventData
import Chain.PolynomialChain
import Chain.Dimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Finite-dimensional factorization of both physical transfer entries when
the inlet is to the left of the outputs. Chamber indices in this file are zero-based.
-/
noncomputable section
namespace Catenary.Obstruction
open Polynomial Continuant
open Filter Set
open scoped Polynomial BigOperators Topology

/-- Four blocks of freely stored lower coefficients and two scalar gains.
The common left polynomial is stored only once. -/
abbrev DataTuple (R : Type*) (n d w u : ℕ) :=
  (Fin n → R) × (Fin d → R) × (Fin w → R) × (Fin u → R) × R × R

abbrev DataSpace := DataTuple ℝ

abbrev LeftData (m : ℕ) (i j k : Chamber m) :=
  DataSpace (m + 1) i.val (m + 1 - (j.val + 1)) (m + 1 - (k.val + 1))

/-- Restore a monic polynomial, including the constant polynomial 1 when d=0. -/
def restore {d : ℕ} (z : Fin d → ℝ) : ℝ[X] :=
  X^d + ∑ t : Fin d, C (z t) * X^t.val

theorem restore_coefficients {d : ℕ} (p : ℝ[X]) (hm : p.Monic) (hd : p.natDegree = d) :
    restore (fun t : Fin d => p.coeff t.val) = p := by
  simpa only [restore, hd, Finset.sum_range] using hm.as_sum.symm

def lowerCoefficients {R : Type*} [CommRing R] (d : ℕ) (xs : List (PathSite R)) : Fin d → R :=
  fun t => (intervalCharpoly xs).coeff t.val

theorem restore_interval {d : ℕ} (xs : List (PathSite ℝ)) (hd : xs.length = d) :
    restore (lowerCoefficients d xs) = intervalCharpoly xs :=
  restore_coefficients _ (Matrix.charpoly_monic _) ((intervalCharpoly_natDegree xs).trans hd)

/-- The directed path product is independent of the spectral parameter. -/
def pathGain {R : Type*} [CommRing R] (xs : List (PathSite R)) : R :=
  (xs.map PathSite.lower).prod

theorem directedProduct_shift (s : ℝ) (xs : List (PathSite ℝ)) :
    directedProduct (xs.map (shiftedSite s)) = pathGain xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change -(shiftedSite s a).lower * directedProduct (xs.map (shiftedSite s)) =
      a.lower * pathGain xs
    simp [ih, shiftedSite]

private theorem run_eval (s : ℝ) (xs : List (PathSite ℝ)) :
    ((run (xs.map pencilSite) (1,0)).1.eval s,
      (run (xs.map pencilSite) (1,0)).2.eval s) =
      run (xs.map (shiftedSite s)) (1,0) := by
  induction xs with
  | nil => simp [run]
  | cons a xs ih =>
    have ha := congrArg Prod.fst ih
    have hb := congrArg Prod.snd ih
    simp only [Prod.fst, Prod.snd] at ha hb
    simp [run, step, pencilSite, shiftedSite, PathSite.weight, ha, hb]

theorem interval_eval (s : ℝ) (xs : List (PathSite ℝ)) :
    (intervalCharpoly xs).eval s = cont (xs.map (shiftedSite s)) := by
  rw [intervalCharpoly, charpoly_eq_cont]
  exact congrArg Prod.fst (run_eval s xs)

def siteData {R : Type*} [CommRing R] {m : ℕ} (i j k : Chamber m)
    (xs : List (PathSite R)) :
    DataTuple R (m+1) i.val (m+1-(j.val+1)) (m+1-(k.val+1)) :=
  (lowerCoefficients (m+1) xs,
   lowerCoefficients i.val (xs.take i.val),
   lowerCoefficients (m+1-(j.val+1)) (xs.drop (j.val+1)),
   lowerCoefficients (m+1-(k.val+1)) (xs.drop (k.val+1)),
   pathGain ((xs.drop i.val).take (j.val-i.val)),
   pathGain ((xs.drop i.val).take (k.val-i.val)))

/-- Each lower coefficient is taken from a concrete physical interval. -/
def physicalData {m : ℕ} (ℓ i j k : Chamber m) (θ : Params m) : LeftData m i j k :=
  siteData i j k (physicalSites ℓ θ)

/-- The common prefix factor is used in both response numerators. -/
def decode {n d w u : ℕ} (z : DataSpace n d w u) (s : ℝ) : ℝ × ℝ :=
  let ⟨den, prefix_, right₁, right₂, gain₁, gain₂⟩ := z
  let D := (restore den).eval s
  let L := (restore prefix_).eval s
  (L * (gain₁ * (restore right₁).eval s) / D,
   L * (gain₂ * (restore right₂).eval s) / D)

theorem physical_transfer_factors {m : ℕ} (ℓ i j k : Chamber m) (θ : Params m) (s : ℝ)
    (hij : i ≤ j) (hik : i ≤ k) (hθ : Positive θ)
    (hD : (s • (1 : Mat m) - generator ℓ θ).det ≠ 0) :
    ((s • (1 : Mat m) - generator ℓ θ)⁻¹ j i,
     (s • (1 : Mat m) - generator ℓ θ)⁻¹ k i) = decode (physicalData ℓ i j k θ) s := by
  let xs := physicalSites ℓ θ
  have hn : xs.length = m+1 := physicalSites_length ℓ θ
  have hi : (xs.take i.val).length = i.val := by
    simp only [List.length_take, hn, Nat.min_eq_left i.isLt.le]
  have hj : (xs.drop (j.val+1)).length = m+1-(j.val+1) := by simp [hn]
  have hk : (xs.drop (k.val+1)).length = m+1-(k.val+1) := by simp [hn]
  have h₁ := (physical_transfer_formula ℓ i j θ s hθ hij hD).1
  have h₂ := (physical_transfer_formula ℓ i k θ s hθ hik hD).1
  change _ = decode (lowerCoefficients _ xs, lowerCoefficients _ (xs.take i.val),
    lowerCoefficients _ (xs.drop (j.val+1)), lowerCoefficients _ (xs.drop (k.val+1)),
    pathGain ((xs.drop i.val).take (j.val-i.val)), pathGain ((xs.drop i.val).take (k.val-i.val))) s
  simp only [decode, restore_interval _ hn, restore_interval _ hi, restore_interval _ hj,
    restore_interval _ hk, interval_eval]
  rw [h₁, h₂]
  simp only [xs, ← List.map_take, ← List.map_drop, directedProduct_shift]

/-- Equal finite data produce equal amounts for every continuous input at every
nonnegative time, with both experiments started at zero. -/
theorem sameCurves_of_data {m : ℕ} (ℓ i j k : Chamber m) (θ η : Params m)
    (hij : i ≤ j) (hik : i ≤ k) (hθ : Positive θ) (hη : Positive η)
    (heq : physicalData ℓ i j k θ = physicalData ℓ i j k η) :
    SameCurves i j k ℓ θ η := by
  apply (sameCurves_iff_common_regular i j k ℓ θ η).mpr
  intro s hrθ hrη
  have h₁ := physical_transfer_factors ℓ i j k θ s hij hik hθ hrθ
  have h₂ := physical_transfer_factors ℓ i j k η s hij hik hη hrη
  rw [heq] at h₁
  exact ⟨congrArg Prod.fst (h₁.trans h₂.symm), congrArg Prod.snd (h₁.trans h₂.symm)⟩

theorem data_finrank {m : ℕ} (i j k : Chamber m) :
    Module.finrank ℝ (LeftData m i j k) =
      (m+1) + i.val + (m+1-(j.val+1)) + (m+1-(k.val+1)) + 2 := by
  simp [LeftData, DataSpace, Module.finrank_prod, Nat.add_assoc]

theorem too_few_coordinates {m : ℕ} (i j k : Chamber m) (hij : i < j) (hjk : j < k) :
    Module.finrank ℝ (LeftData m i j k) < Module.finrank ℝ (Params m) ↔
      ¬placement (m+1) (i.val+1) (j.val+1) (k.val+1) := by
  rw [data_finrank]
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have h₁ : i.val < j.val := hij
  have h₂ : j.val < k.val := hjk
  simp only [Params, Module.finrank_pi, Fintype.card_fin]
  unfold placement
  omega

/-- Every linear differential through these coordinates has nontrivial kernel
in the forbidden placements. -/
theorem linear_map_not_injective {m : ℕ} (i j k : Chamber m) (hij : i < j) (hjk : j < k)
    (hbad : ¬placement (m+1) (i.val+1) (j.val+1) (k.val+1))
    (L : Params m →ₗ[ℝ] LeftData m i j k) : ¬ Function.Injective L := by
  intro hinj
  exact (Nat.not_le_of_gt ((too_few_coordinates i j k hij hjk).2 hbad))
    (LinearMap.finrank_le_finrank_of_injective hinj)

theorem physicalData_derivative_not_injective {m : ℕ} (ℓ i j k : Chamber m)
    (hij : i < j) (hjk : j < k)
    (hbad : ¬placement (m+1) (i.val+1) (j.val+1) (k.val+1)) (θ : Params m) :
    ¬ Function.Injective (fderiv ℝ (physicalData ℓ i j k) θ) :=
  linear_map_not_injective i j k hij hjk hbad _

/-- At a submersive point, a nonzero kernel produces another point of the same
fiber in every neighbourhood, by the actual implicit function theorem. -/
theorem nonisolated_submersion
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : E → V} {a : E} {L : E →L[ℝ] V} (hf : HasStrictFDerivAt f L a)
    (hs : LinearMap.range L.toLinearMap = ⊤) (hn : ¬ Function.Injective L)
    {U : Set E} (hU : U ∈ 𝓝 a) :
    ∃ b ∈ U, b ≠ a ∧ f b = f a := by
  classical
  letI : Nontrivial (LinearMap.ker L.toLinearMap) :=
    Submodule.nontrivial_iff_ne_bot.mpr fun h => hn (LinearMap.ker_eq_bot.mp h)
  obtain ⟨v, hv⟩ := exists_ne (0 : LinearMap.ker L.toLinearMap)
  let e := hf.implicitToPartialHomeomorph f L hs
  let z := fun t : ℝ => (f a, t • v)
  have hz : Tendsto z (𝓝[≠] (0 : ℝ)) (𝓝 (f a, 0)) := by
    have hc : Continuous z := continuous_const.prodMk (continuous_id.smul continuous_const)
    simpa [z] using ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
  have ht : (f a, (0 : LinearMap.ker L.toLinearMap)) ∈ e.target :=
    hf.mem_implicitToPartialHomeomorph_target hs
  have he : e a = (f a, 0) := hf.implicitToPartialHomeomorph_self hs
  have hcenter : e.symm (f a, 0) = a := by
    rw [← he]
    exact e.left_inv (hf.mem_implicitToPartialHomeomorph_source hs)
  have hnear := (e.continuousAt_symm ht).tendsto.comp hz
  rw [hcenter] at hnear
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := self_mem_nhdsWithin
  have htarget' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), z t ∈ e.target := hz (e.open_target.mem_nhds ht)
  have hinside' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), e.symm (z t) ∈ U := hnear hU
  obtain ⟨t, htarget, hinside, ht0⟩ := (htarget'.and (hinside'.and hne)).exists
  have hr := e.right_inv htarget
  refine ⟨e.symm (z t), hinside, ?_, ?_⟩
  · intro h
    rw [h, he] at hr
    have hzero : (0 : LinearMap.ker L.toLinearMap) = t • v := congrArg Prod.snd hr
    exact (smul_ne_zero ht0 hv) hzero.symm
  · exact congrArg Prod.fst hr

theorem positive_open (m : ℕ) : IsOpen {x : Params m | Positive x} := by
  change IsOpen {x : Params m | ∀ p, (0 : ℝ) < x p}
  simp only [← Set.iInter_setOf]
  exact isOpen_iInter_of_finite fun p => isOpen_lt continuous_const (continuous_apply p)

/-- The sufficient regularity condition below can be used when all the stored
coordinates have independent differentials on a dense set. -/
def SubmersivePoints {m : ℕ} (ℓ i j k : Chamber m) : Set (Params m) :=
  {θ | ∃ L : Params m →L[ℝ] LeftData m i j k,
       HasStrictFDerivAt (physicalData ℓ i j k) L θ ∧ LinearMap.range L.toLinearMap = ⊤}

theorem not_generic_of_dense_submersions {m : ℕ} (ℓ i j k : Chamber m)
    (hij : i < j) (hjk : j < k)
    (hbad : ¬placement (m+1) (i.val+1) (j.val+1) (k.val+1))
    (hsub : Dense (SubmersivePoints ℓ i j k)) :
    ¬GenericLocalID i j k ℓ := by
  rintro ⟨p, ⟨θ, hθ, hp⟩, hloc⟩
  let U : Set (Params m) := {x | Positive x} ∩ {x | MvPolynomial.eval x p ≠ 0}
  have hu : IsOpen U :=
    (positive_open m).inter (isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const)
  obtain ⟨a, ⟨L, hf, hs⟩, ha⟩ := hsub.exists_mem_open hu ⟨θ, hθ, hp⟩
  obtain ⟨ε, hε, hεuniq⟩ := hloc a ha.1 ha.2
  have nh : U ∩ Metric.ball a ε ∈ 𝓝 a :=
    inter_mem (hu.mem_nhds ha) (Metric.ball_mem_nhds _ hε)
  obtain ⟨b, hb, hne, heq⟩ := nonisolated_submersion hf hs
    (linear_map_not_injective i j k hij hjk hbad L.toLinearMap) nh
  exact hne (hεuniq b hb.1.1 hb.2
    (sameCurves_of_data ℓ i j k a b hij.le (hij.trans hjk).le ha.1 hb.1.1 heq.symm))

section PolynomialKernel
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

/-- A wide polynomial Jacobian has a nonzero polynomial vector field in its
kernel as a polynomial identity over the coefficient ring itself. -/
theorem polynomial_kernel (P : τ → MvPolynomial σ ℝ)
    (hd : Fintype.card τ < Fintype.card σ) :
    ∃ W : σ → MvPolynomial σ ℝ, W ≠ 0 ∧
      ∀ i, ∑ j, MvPolynomial.pderiv j (P i) * W j = 0 := by
  classical
  let R := MvPolynomial σ ℝ
  let J : Matrix τ σ R := fun i j => MvPolynomial.pderiv j (P i)
  let L := J.mulVecLin
  have hn : ¬ Function.Injective L := by
    intro h
    have z := LinearMap.finrank_le_finrank_of_injective h
    simp only [Module.finrank_pi] at z
    omega
  have hker : LinearMap.ker L ≠ ⊥ := fun h => hn (LinearMap.ker_eq_bot.mp h)
  obtain ⟨W, hW, hne⟩ := (Submodule.ne_bot_iff _).mp hker
  exact ⟨W, hne, fun i => congrFun (LinearMap.mem_ker.mp hW) i⟩

theorem polynomial_eval_contDiff (p : MvPolynomial σ ℝ) :
    ContDiff ℝ 1 (fun x : σ → ℝ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : σ → ℝ => a))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p j hp => simpa using hp.mul (contDiff_apply ℝ ℝ j)

theorem polynomial_curve_derivative (p : MvPolynomial σ ℝ)
    (γ : ℝ → σ → ℝ) (t : ℝ) (v : σ → ℝ) (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => MvPolynomial.eval (γ s) p)
      (∑ j, MvPolynomial.eval (γ t) (MvPolynomial.pderiv j p) * v j) t := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.pderiv_C] using (hasDerivAt_const t a)
  | add p q hp hq =>
    simpa [add_mul, Finset.sum_add_distrib] using hp.add hq
  | mul_X p k hp =>
    have hk : HasDerivAt (fun s => γ s k) (v k) t :=
      (hasFDerivAt_apply (𝕜 := ℝ) k (γ t)).comp_hasDerivAt t hγ
    convert hp.mul hk using 1
    · ext s; simp
    · simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X,
        add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · simp [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, mul_ite, ite_mul]

end PolynomialKernel

/-- A polynomial on a finite number of real variables vanishing on the entire
positive orthant is the zero polynomial. -/
theorem eq_zero_on_positive {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (h : ∀ x : Fin n → ℝ, (∀ i, 0 < x i) → MvPolynomial.eval x p = 0) : p = 0 := by
  induction n with
  | zero =>
    apply MvPolynomial.funext
    intro x
    simpa using h x (fun i => Fin.elim0 i)
  | succ n ih =>
    apply (MvPolynomial.finSuccEquiv ℝ n).injective
    rw [map_zero]
    let c : ℝ → MvPolynomial (Fin n) ℝ := MvPolynomial.C
    have hi : (c '' Ioi (0 : ℝ)).Infinite :=
      (Set.Ioi_infinite (0 : ℝ)).image (MvPolynomial.C_injective (σ := Fin n) (R := ℝ)).injOn
    apply Polynomial.eq_of_infinite_eval_eq _ _ (hi.mono ?_)
    rintro _ ⟨r, hr, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.eval_zero]
    apply ih
    intro x hx
    rw [MvPolynomial.eval_polynomial_eval_finSuccEquiv]
    apply h
    refine Fin.cases ?_ (fun j => ?_)
    · simpa [c] using hr
    · exact hx j

theorem positive_common_witness {n : ℕ} (p q : MvPolynomial (Fin n) ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a : Fin n → ℝ, (∀ i, 0 < a i) ∧
      MvPolynomial.eval a p ≠ 0 ∧ MvPolynomial.eval a q ≠ 0 := by
  classical
  by_contra! bad
  apply mul_ne_zero hp hq
  apply eq_zero_on_positive
  intro x hx
  rw [map_mul]
  by_cases hz : MvPolynomial.eval x p = 0
  · simp [hz]
  · simp [bad x hx hz]

/-- A polynomial map from a larger Euclidean space has nonisolated fibers at
some positive point off every prescribed proper algebraic exception. -/
theorem polynomial_fibers {n : ℕ} {τ : Type*} [Fintype τ]
    (P : τ → MvPolynomial (Fin n) ℝ) (hd : Fintype.card τ < n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    ∃ a : Fin n → ℝ, (∀ i, 0 < a i) ∧ MvPolynomial.eval a p ≠ 0 ∧
      ∀ U ∈ 𝓝 a, ∃ b ∈ U, b ≠ a ∧
        (fun s => MvPolynomial.eval b (P s)) = (fun s => MvPolynomial.eval a (P s)) := by
  classical
  obtain ⟨W, hw, hker⟩ := polynomial_kernel P (by simpa using hd)
  obtain ⟨j, hj⟩ : ∃ j, W j ≠ 0 := by
    by_contra! h
    exact hw (funext h)
  obtain ⟨a, ha, hap, hwa⟩ := positive_common_witness p (W j) hp hj
  let w := fun (x : Fin n → ℝ) (i : Fin n) => MvPolynomial.eval x (W i)
  let f := fun (x : Fin n → ℝ) (s : τ) => MvPolynomial.eval x (P s)
  have hwd : ContDiff ℝ 1 w := contDiff_pi.mpr fun i => polynomial_eval_contDiff (W i)
  have hwn : w a ≠ 0 := fun h => hwa (congrFun h j)
  refine ⟨a, ha, hap, fun U hU => Dimension.nonisolated_of_ode_invariant
    (f := f) hwd.contDiffAt ?_ hwn hU⟩
  intro γ t hγ
  apply hasDerivAt_pi.mpr
  intro s
  have hs := congrArg (MvPolynomial.eval (γ t)) (hker s)
  simp only [map_sum, map_mul, map_zero] at hs
  have h := polynomial_curve_derivative (P s) γ t (w (γ t)) hγ
  simpa only [f, Function.comp_apply, w, hs, Pi.zero_apply] using h

abbrev Slot (n d w u : ℕ) := Fin n ⊕ Fin d ⊕ Fin w ⊕ Fin u ⊕ Bool

def flatten {R : Type*} {n d w u : ℕ} (z : DataTuple R n d w u) : Slot n d w u → R :=
  Sum.elim z.1 (Sum.elim z.2.1 (Sum.elim z.2.2.1 (Sum.elim z.2.2.2.1
    (fun b => if b then z.2.2.2.2.2 else z.2.2.2.2.1))))

def unflatten {R : Type*} {n d w u : ℕ} (z : Slot n d w u → R) : DataTuple R n d w u :=
  (fun t => z (.inl t), fun t => z (.inr (.inl t)),
   fun t => z (.inr (.inr (.inl t))), fun t => z (.inr (.inr (.inr (.inl t)))),
   z (.inr (.inr (.inr (.inr false)))), z (.inr (.inr (.inr (.inr true)))))

theorem flatten_injective {R : Type*} {n d w u : ℕ} :
    Function.Injective (flatten (R := R) (n := n) (d := d) (w := w) (u := u)) :=
  (show Function.LeftInverse unflatten _ from fun _ => rfl).injective

def mapSite {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a : PathSite R) : PathSite S := ⟨φ a.diag, φ a.upper, φ a.lower⟩

private theorem map_cont {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (xs : List (PathSite R)) : φ (cont xs) = cont (xs.map (mapSite φ)) := by
  suffices h : (φ (run xs (1,0)).1, φ (run xs (1,0)).2) =
      run (xs.map (mapSite φ)) (1,0) from congrArg Prod.fst h
  induction xs with
  | nil => simp [run]
  | cons a xs ih =>
    have h₁ := congrArg Prod.fst ih
    have h₂ := congrArg Prod.snd ih
    simp only [Prod.fst, Prod.snd] at h₁ h₂
    simp [run, step, PathSite.weight, mapSite, h₁, h₂]

theorem map_interval {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (xs : List (PathSite R)) :
    (intervalCharpoly xs).map φ = intervalCharpoly (xs.map (mapSite φ)) := by
  simp only [intervalCharpoly, charpoly_eq_cont]
  change Polynomial.mapRingHom φ (cont (xs.map pencilSite)) = _
  rw [map_cont, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp [mapSite, pencilSite, Function.comp_def]

theorem map_pathGain {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (xs : List (PathSite R)) : φ (pathGain xs) = pathGain (xs.map (mapSite φ)) := by
  induction xs with
  | nil => simp [pathGain]
  | cons a xs ih =>
    change φ (a.lower * pathGain xs) = (mapSite φ a).lower * pathGain (xs.map (mapSite φ))
    rw [map_mul, ih]
    rfl

theorem map_lowerCoefficient {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (xs : List (PathSite R)) {d : ℕ} (t : Fin d) :
    φ (lowerCoefficients d xs t) = lowerCoefficients d (xs.map (mapSite φ)) t := by
  simpa only [lowerCoefficients, Polynomial.coeff_map] using
    congrArg (fun z : S[X] => z.coeff t.val) (map_interval φ xs)

theorem map_siteData {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {m : ℕ} (i j k : Chamber m) (xs : List (PathSite R))
    (s : Slot (m+1) i.val (m+1-(j.val+1)) (m+1-(k.val+1))) :
    φ (flatten (siteData i j k xs) s) = flatten (siteData i j k (xs.map (mapSite φ))) s := by
  rcases s with t | (t | (t | (t | b)))
  · exact map_lowerCoefficient φ xs t
  · simpa only [List.map_take] using map_lowerCoefficient φ (xs.take i.val) t
  · simpa only [List.map_drop] using map_lowerCoefficient φ (xs.drop (j.val+1)) t
  · simpa only [List.map_drop] using map_lowerCoefficient φ (xs.drop (k.val+1)) t
  · cases b
    · simpa only [List.map_take, List.map_drop] using
        map_pathGain φ ((xs.drop i.val).take (j.val-i.val))
    · simpa only [List.map_take, List.map_drop] using
        map_pathGain φ ((xs.drop i.val).take (k.val-i.val))

abbrev RatePoly (m : ℕ) := MvPolynomial (Fin (2*m+1)) ℝ

def symbolicDiagonal {m : ℕ} (ℓ x : Chamber m) : RatePoly m :=
  (∑ r : Fin m, (MvPolynomial.X (fwd r) *
      MvPolynomial.C (directedEdge r.castSucc r.succ x x) +
      MvPolynomial.X (back r) * MvPolynomial.C (directedEdge r.succ r.castSucc x x))) -
    if x = ℓ then MvPolynomial.X (loss m) else 0

def symbolicSite {m : ℕ} (ℓ : Chamber m) (t : ℕ) : PathSite (RatePoly m) where
  diag := if ht : t < m+1 then symbolicDiagonal ℓ ⟨t, ht⟩ else 0
  upper := if ht : t < m then MvPolynomial.X (back ⟨t,ht⟩) else 0
  lower := if ht : t < m then MvPolynomial.X (fwd ⟨t,ht⟩) else 0

theorem eval_symbolicSite {m : ℕ} (ℓ : Chamber m) (θ : Params m) (t : ℕ) :
    mapSite (MvPolynomial.eval θ) (symbolicSite ℓ t) = physicalSite ℓ θ t := by
  have hdiag (x : Chamber m) : MvPolynomial.eval θ (symbolicDiagonal ℓ x) =
      generator ℓ θ x x := by
    by_cases h : x = ℓ <;> simp [symbolicDiagonal, generator, h]
  by_cases ht : t < m+1 <;> by_cases hr : t < m <;>
    simp [mapSite, symbolicSite, physicalSite, ht, hr, hdiag]

def coordinatePolynomial {m : ℕ} (ℓ i j k : Chamber m) :
    Slot (m+1) i.val (m+1-(j.val+1)) (m+1-(k.val+1)) → RatePoly m :=
  flatten (siteData i j k (sitesFrom (symbolicSite ℓ) 0 (m+1)))

theorem eval_coordinatePolynomial {m : ℕ} (ℓ i j k : Chamber m) (θ : Params m) :
    (fun s => MvPolynomial.eval θ (coordinatePolynomial ℓ i j k s)) =
      flatten (physicalData ℓ i j k θ) := by
  funext s
  rw [coordinatePolynomial, map_siteData, sitesFrom_map]
  simp only [eval_symbolicSite, physicalData, physicalSites]

/-- A placement failing the left-hand inequality cannot generically locally
identify the physical rates from the two entire continuous-input experiments. -/
theorem not_generic_of_left_failure {m : ℕ} (ℓ i j k : Chamber m) (hij : i < j) (hjk : j < k)
    (hbad : ¬placement (m+1) (i.val+1) (j.val+1) (k.val+1)) :
    ¬GenericLocalID i j k ℓ := by
  rintro ⟨p, ⟨θ, _, hpθ⟩, hloc⟩
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hpθ
  have hdim := (too_few_coordinates i j k hij hjk).mpr hbad
  rw [data_finrank] at hdim
  simp only [Params, Module.finrank_pi, Fintype.card_fin] at hdim
  have hc : Fintype.card (Slot (m+1) i.val (m+1-(j.val+1)) (m+1-(k.val+1))) < 2*m+1 := by
    simpa [Slot, Nat.add_assoc] using hdim
  obtain ⟨a, ha, hap, hf⟩ := polynomial_fibers (coordinatePolynomial ℓ i j k) hc p hp
  obtain ⟨ε, hε, huniq⟩ := hloc a ha hap
  have hn : {x : Params m | Positive x} ∩ Metric.ball a ε ∈ 𝓝 a :=
    inter_mem ((positive_open m).mem_nhds ha) (Metric.ball_mem_nhds a hε)
  obtain ⟨b, hb, hne, hsame⟩ := hf _ hn
  rw [eval_coordinatePolynomial, eval_coordinatePolynomial] at hsame
  exact hne (huniq b hb.1 hb.2
    (sameCurves_of_data ℓ i j k a b hij.le (hij.trans hjk).le ha hb.1
      (flatten_injective hsame).symm))

end Catenary.Obstruction
