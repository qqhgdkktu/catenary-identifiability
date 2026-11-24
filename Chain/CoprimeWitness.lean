import Chain.MiddleRecovery
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Polynomial certificates for coprimality of parameter-dependent univariate
polynomials. A Bézout identity at one point gives a determinant equal to 1
at that point. Its nonvanishing certifies coprimality at every parameter. -/

noncomputable section
namespace Catenary.CoprimeWitness
open Polynomial
open scoped Polynomial BigOperators Matrix

private def multMatrix {R : Type*} [CommRing R] (n : ℕ) (p h : R[X]) : Matrix (Fin n) (Fin n) R :=
  fun i j => ((X^j.val*h) %ₘ p).coeff i.val

private theorem map_multMatrix {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p h : R[X]) (hp : p.Monic) (n : ℕ) :
    φ.mapMatrix (multMatrix n p h) = multMatrix n (p.map φ) (h.map φ) := by
  ext i j
  change φ (((X^j.val*h) %ₘ p).coeff i.val) = _
  rw [← Polynomial.coeff_map, map_modByMonic φ hp, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X]
  rfl

private theorem multMatrix_one {R : Type*} [CommRing R] [Nontrivial R]
    (p : R[X]) (hp : p.Monic) (n : ℕ) (hn : p.natDegree = n) : multMatrix n p 1 = 1 := by
  ext i j
  change ((X^j.val*1) %ₘ p).coeff i.val = _
  rw [mul_one, (modByMonic_eq_self_iff hp).mpr (by
    rw [degree_X_pow, degree_eq_natDegree hp.ne_zero, hn]
    exact_mod_cast j.isLt)]
  simp [coeff_X_pow, Matrix.one_apply, Fin.ext_iff]

private theorem coprime_of_det {K : Type*} [Field K]
    {p q a b : K[X]} (hp : p.Monic) {n : ℕ} (hdeg : p.natDegree = n)
    (hdet : (multMatrix n p (a*p+b*q)).det ≠ 0) : IsCoprime p q := by
  classical
  by_cases hn : n = 0
  · rw [hp.natDegree_eq_zero.mp (hdeg.trans hn)]
    exact isCoprime_one_left
  let h := a*p+b*q
  let f (j : Fin n) : K[X] := (X^j.val*h) %ₘ p
  let z (i : Fin n) := (1 : K[X]).coeff i.val
  let A := multMatrix n p h
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))) z
  have he : ∑ j : Fin n, C (v j) * f j = 1 := by
    apply Polynomial.ext
    intro k
    simp only [finset_sum_coeff, coeff_C_mul]
    by_cases hk : k < n
    · have hk' := congrFun hv ⟨k,hk⟩
      simpa only [A, Matrix.mulVec, dotProduct, multMatrix, f, z, mul_comm] using hk'
    · have hl (j : Fin n) : (f j).degree < k := by
        apply (degree_modByMonic_lt _ hp).trans_le
        rw [degree_eq_natDegree hp.ne_zero, hdeg]
        exact_mod_cast (Nat.le_of_not_lt hk)
      have hk₀ : k ≠ 0 := by omega
      simp [coeff_eq_zero_of_degree_lt (hl _), coeff_one, hk₀]
  let I : Ideal K[X] := Ideal.span {p,q}
  have hpI : p ∈ I := Ideal.subset_span (by simp)
  have hqI : q ∈ I := Ideal.subset_span (by simp)
  have hh : h ∈ I := I.add_mem (I.mul_mem_left a hpI) (I.mul_mem_left b hqI)
  have hf (j : Fin n) : f j ∈ I := by
    dsimp only [f]
    rw [modByMonic_eq_sub_mul_div _ hp]
    exact I.sub_mem (I.mul_mem_left _ hh) (I.mul_mem_right _ hpI)
  apply Ideal.mem_span_pair.mp
  rw [← he]
  exact Submodule.sum_mem I fun j _ => I.mul_mem_left _ (hf j)

/-- Only the first polynomial has to be monic. The certificate is normalized
to have value 1 at the specified witness; constant or empty intervals work. -/
theorem monic_pair_certificate {σ : Type*} (P Q : (MvPolynomial σ ℝ)[X])
    (hp : P.Monic) (a : σ → ℝ)
    (h : IsCoprime (P.map (MvPolynomial.eval a)) (Q.map (MvPolynomial.eval a))) :
    ∃ q : MvPolynomial σ ℝ, MvPolynomial.eval a q = 1 ∧ ∀ x : σ → ℝ,
      MvPolynomial.eval x q ≠ 0 →
        IsCoprime (P.map (MvPolynomial.eval x)) (Q.map (MvPolynomial.eval x)) := by
  obtain ⟨u,v,huv⟩ := h
  let inc : ℝ →+* MvPolynomial σ ℝ := MvPolynomial.C
  have hil (z : ℝ[X]) (x : σ → ℝ) : (z.map inc).map (MvPolynomial.eval x) = z := by
    ext i
    simp only [coeff_map, inc, MvPolynomial.eval_C]
  let H := u.map inc * P + v.map inc * Q
  let A := multMatrix P.natDegree P H
  have hs (x : σ → ℝ) : MvPolynomial.eval x A.det =
      (multMatrix P.natDegree (P.map (MvPolynomial.eval x))
        (u * P.map (MvPolynomial.eval x) + v * Q.map (MvPolynomial.eval x))).det := by
    dsimp only [A]
    rw [RingHom.map_det, map_multMatrix _ _ _ hp]
    simp only [H, Polynomial.map_add, Polynomial.map_mul, hil]
  refine ⟨A.det, ?_, fun x hx => ?_⟩
  · rw [hs, huv, multMatrix_one _ (hp.map _) _ (hp.natDegree_map _), Matrix.det_one]
  · apply coprime_of_det (a := u) (b := v) (hp.map _) (hp.natDegree_map _)
    simpa only [hs] using hx

/-- One polynomial certifies both physical coprimality conditions. -/
theorem middle_coprime_certificate {m} (ℓ i j : Chamber m) (a : Params m)
    (hb : IsCoprime (Middle.prefix ℓ a i.val) (Middle.suffix ℓ a i.val))
    (hl : IsCoprime (Middle.full ℓ a) (Middle.prefix ℓ a j.val * Middle.suffix ℓ a i.val)) :
    ∃ q : Obstruction.RatePoly m, MvPolynomial.eval a q = 1 ∧
      ∀ x : Params m, MvPolynomial.eval x q ≠ 0 →
        IsCoprime (Middle.prefix ℓ x i.val) (Middle.suffix ℓ x i.val) ∧
        IsCoprime (Middle.full ℓ x) (Middle.prefix ℓ x j.val * Middle.suffix ℓ x i.val) := by
  obtain ⟨p, hp, hB⟩ := monic_pair_certificate (Middle.symbolicPrefix ℓ i.val)
    (Middle.symbolicSuffix ℓ i.val) (Matrix.charpoly_monic _) a (by simpa using hb)
  obtain ⟨q, hq, hL⟩ := monic_pair_certificate (Middle.symbolicFull ℓ)
    (Middle.symbolicPrefix ℓ j.val * Middle.symbolicSuffix ℓ i.val)
    (Matrix.charpoly_monic _) a (by simpa using hl)
  refine ⟨p*q, by simp only [map_mul, hp, hq, mul_one], fun x hx => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hx
  exact ⟨by simpa using hB x hx.1, by simpa using hL x hx.2⟩

/-- A single positive physical witness with the two required coprimality
properties gives a polynomial exceptional set and generic identifiability. -/
theorem generic_middle_of_witness {m} (i j k ℓ : Chamber m)
    (hi : 0 < i.val) (hi' : i.val < m) (hji : j ≤ i) (hik : i ≤ k)
    (a : Params m) (ha : Positive a)
    (hb : IsCoprime (Middle.prefix ℓ a i.val) (Middle.suffix ℓ a i.val))
    (hl : IsCoprime (Middle.full ℓ a) (Middle.prefix ℓ a j.val * Middle.suffix ℓ a i.val)) :
    GenericLocalID i j k ℓ := by
  obtain ⟨q, hq, h⟩ := middle_coprime_certificate ℓ i j a hb hl
  refine ⟨q, ⟨a, ha, hq.trans_ne one_ne_zero⟩, fun x hx hqx => ?_⟩
  obtain ⟨hB, hL⟩ := h x hqx
  exact Middle.local_middle_of_coprime i j k ℓ x hx hi hi' hji hik hB hL

end Catenary.CoprimeWitness
