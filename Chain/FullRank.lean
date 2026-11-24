import Chain.RankWitness
import Chain.Obstruction
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open MvPolynomial
open scoped BigOperators
namespace Catenary

/-- A full-column-rank physical measurement at a single positive point suffices.
P can have more rows than columns. Equal curves must identify its values on the
regular set q≠0 in a neighborhood of each positive regular point. -/
theorem generic_of_full_rank_somewhere {m} {o : Type*} [Fintype o] [DecidableEq o]
    (i j k ℓ : Chamber m) (P : o → PRate m) (q : PRate m)
    (a : Params m) (hq : q ≠ 0)
    (hinj : Function.Injective (fderiv ℝ (polynomialValues P) a))
    (hread : ∀ x : Params m, Positive x → eval x q ≠ 0 →
      ∃ e : ℝ, 0 < e ∧ ∀ y : Params m, Positive y → dist y x < e →
        SameCurves i j k ℓ x y → polynomialValues P x = polynomialValues P y) :
    GenericLocalID i j k ℓ := by
  classical
  let L := fderiv ℝ (polynomialValues P) a
  obtain ⟨T,hT⟩ := L.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let Q (r : IRate m) : PRate m := ∑ t : o, C ((T (Pi.single t 1)) r) * P t
  have evalQ : polynomialValues Q = T ∘ polynomialValues P := by
    funext x r
    let b := polynomialValues P x
    have hb : (∑ t : o, b t • (Pi.single t (1:ℝ) : o → ℝ)) = b := by
      funext c
      simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,mul_ite,smul_eq_mul,eq_comm]
    have e := congrArg (fun v => T v r) hb
    simp only [map_sum, map_smul, Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at e
    simpa only [Q,polynomialValues,map_sum,map_mul,eval_C,Function.comp_apply,b,mul_comm] using e
  have hM : DifferentiableAt ℝ (polynomialValues P) a := by
    apply differentiableAt_pi.mpr
    intro r
    obtain ⟨_,h,_⟩ := polynomial_strict_jet (P r) a
    exact h.hasFDerivAt.differentiableAt
  have derivQ : HasFDerivAt (polynomialValues Q) (ContinuousLinearMap.id ℝ (Params m)) a := by
    rw [evalQ]
    have hf := T.toContinuousLinearMap.hasFDerivAt.comp a hM.hasFDerivAt
    convert hf using 1
    ext v r
    exact (congrFun (congrArg (fun f : Params m →ₗ[ℝ] Params m => f v) hT) r).symm
  have hQ : eval a (polynomialJacobianDet Q) ≠ 0 := by
    obtain ⟨D,hD,hd⟩ := square_polynomial_jet Q a
    have eq := hD.hasFDerivAt.unique derivQ
    rw [hd,eq]
    change LinearMap.det (LinearMap.id : Params m →ₗ[ℝ] Params m) ≠ 0
    simp
  have nz : polynomialJacobianDet Q ≠ 0 := by intro e; simp [e] at hQ
  obtain ⟨x₀,hpos,hq₀,hJ⟩ := Obstruction.positive_common_witness q (polynomialJacobianDet Q) hq nz
  apply genericLocalID_of_readable_polynomials i j k ℓ Q q x₀ hpos hq₀ hJ
  intro x hpos hreg
  obtain ⟨e,he,hr⟩ := hread x hpos hreg
  exact ⟨e,he,fun y hy hd h => by simpa only [evalQ,Function.comp_apply] using congrArg T (hr y hy hd h)⟩

theorem generic_of_full_rank {m} {o : Type*} [Fintype o] [DecidableEq o]
    (i j k ℓ : Chamber m) (P : o → PRate m) (q : PRate m)
    (a : Params m) (_ha : Positive a) (hq : eval a q ≠ 0)
    (hinj : Function.Injective (fderiv ℝ (polynomialValues P) a))
    (hread : ∀ x : Params m, Positive x → eval x q ≠ 0 →
      ∃ e : ℝ, 0 < e ∧ ∀ y : Params m, Positive y → dist y x < e →
        SameCurves i j k ℓ x y → polynomialValues P x = polynomialValues P y) :
    GenericLocalID i j k ℓ :=
  generic_of_full_rank_somewhere i j k ℓ P q a (by intro h; simp [h] at hq) hinj hread

/-- In particular the full physical finite Markov map suffices, without a
manually chosen row minor. -/
theorem generic_of_markov_full_rank {m} (i j k ℓ : Chamber m) (a : Params m)
    (ha : Positive a) (h : Function.Injective
      (fderiv ℝ (polynomialValues (observedPolynomial i j k ℓ)) a)) : GenericLocalID i j k ℓ := by
  apply generic_of_full_rank i j k ℓ _ 1 a ha (by simp) h
  intro x _ _
  refine ⟨1,zero_lt_one,?_⟩
  intro y _ _ hs
  obtain ⟨hj,hk⟩ := (sameCurves_iff_markov i j k ℓ x y).mp hs
  funext r
  simp only [polynomialValues, eval_observedPolynomial]
  split <;> first | apply hj | apply hk

end Catenary
