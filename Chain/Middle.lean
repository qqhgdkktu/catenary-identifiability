import Chain.PolynomialReconstruction
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Topology.Separation.Basic

/-! Local splitting of monic transfer numerators and reconstruction at an
interior vertex of a Jacobi chain. -/

noncomputable section

open Polynomial Catenary.Continuant Set Filter
open scoped Polynomial Topology

namespace Catenary.Middle

variable {K : Type*} [Field K]

/-- A fixed polynomial has finitely many monic divisors. A coefficientwise
continuous monic divisor near a specified parameter is therefore locally fixed
on the fiber, even when the two factors have a common root. -/
theorem eventually_eq_monic_divisor [TopologicalSpace K] [T1Space K]
    {T : Type*} [TopologicalSpace T] {a : T}
    (f : T → K[X]) (p : K[X]) (hp : p ≠ 0)
    (hc : ∀ n, ContinuousAt (fun x => (f x).coeff n) a) :
    ∀ᶠ x in 𝓝 a, (f x).Monic → f x ∣ p → f x = f a := by
  classical
  letI := fintypeSubtypeMonicDvd p hp
  have he : ∀ q : {q : K[X] // q.Monic ∧ q ∣ p},
      ∀ᶠ x in 𝓝 a, f x = q.val → q.val = f a := by
    intro q
    by_cases h : q.val = f a
    · exact Eventually.of_forall (fun _ _ => h)
    obtain ⟨n, hn⟩ : ∃ n, (f a).coeff n ≠ q.val.coeff n := by
      by_contra! hn
      exact h ((Polynomial.ext hn).symm)
    filter_upwards [(hc n).eventually_ne hn] with x hx heq
    exact False.elim (hx (congrArg (fun q : K[X] => q.coeff n) heq))
  filter_upwards [eventually_all.mpr he] with x hx hm hd
  exact hx ⟨f x, hm, hd⟩ rfl

/-- Both factors of a fixed nonzero product are locally identified by their
product. Only coefficientwise continuity of the first factor is needed. -/
theorem locally_split_product [TopologicalSpace K] [T1Space K]
    {T : Type*} [TopologicalSpace T] {a : T}
    (f g : T → K[X]) (hf : (f a).Monic) (hg : g a ≠ 0)
    (hc : ∀ n, ContinuousAt (fun x => (f x).coeff n) a) :
    ∀ᶠ x in 𝓝 a, (f x).Monic → f x * g x = f a * g a →
      f x = f a ∧ g x = g a := by
  filter_upwards [eventually_eq_monic_divisor f (f a * g a) (mul_ne_zero hf.ne_zero hg) hc]
    with x hx hm heq
  have h₁ := hx hm ⟨g x, heq.symm⟩
  rw [h₁] at heq
  exact ⟨h₁, mul_left_cancel₀ hf.ne_zero heq⟩

/-- Injectivity of the derivative of monic multiplication at a coprime pair.
Its two summands are the first variations in the coefficient coordinates. -/
theorem monic_product_tangent {L R u v : K[X]} (hL : L.Monic)
    (hcop : IsCoprime L R) (hdeg : u.degree < L.degree)
    (hker : u * R + L * v = 0) : u = 0 ∧ v = 0 := by
  have hd : L ∣ R * u := ⟨-v, by linear_combination hker⟩
  have hu := eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_left hd) hdeg
  refine ⟨hu, (mul_eq_zero.mp ?_).resolve_left hL.ne_zero⟩
  simpa only [hu, zero_mul, zero_add] using hker

/-- For every variation of the monic product, of degree strictly below the
product degree, there is exactly one admissible variation of its two factors. -/
theorem monic_product_tangent_bijective {L R z : K[X]} (hL : L.Monic) (hR : R.Monic)
    (hc : IsCoprime L R) (hz : z.degree < (L * R).degree) :
    ∃! uv : K[X] × K[X], uv.1.degree < L.degree ∧ uv.2.degree < R.degree ∧
      uv.1 * R + L * uv.2 = z := by
  obtain ⟨u, ⟨hu, t, ht⟩, _⟩ := existsUnique_bounded_modular_solution z hL hc
  have he : u * R + L * (-t) = z := by linear_combination ht
  have small : (u * R).degree < (L * R).degree := by
    rw [degree_mul, degree_mul]
    exact WithBot.add_lt_add_right (degree_ne_bot.mpr hR.ne_zero) hu
  have hv : (-t).degree < R.degree := by
    have hs := (degree_sub_le z (u * R)).trans_lt (max_lt hz small)
    rw [show z - u * R = L * (-t) by linear_combination -he, degree_mul, degree_mul] at hs
    exact lt_of_add_lt_add_left hs
  refine ⟨⟨u, -t⟩, ⟨hu, hv, he⟩, ?_⟩
  rintro ⟨a,b⟩ ⟨ha, _, e⟩
  change a * R + L * b = z at e
  have hdiff : (a-u)*R+L*(b-(-t)) = 0 := by linear_combination e-he
  obtain ⟨ea, eb⟩ := monic_product_tangent hL hc ((degree_sub_le _ _).trans_lt (max_lt ha hu)) hdiff
  exact Prod.ext (sub_eq_zero.mp ea) (sub_eq_zero.mp eb)

/-- For monic numerators and denominators, a reduced reference fraction with
a nonzero gain determines all three quantities among models of the same order.
The competing fraction need not have been assumed reduced. -/
theorem scaled_fraction_of_cross {D D' N N' : K[X]} {g g' : K}
    (hd : D.Monic) (hd' : D'.Monic) (hn : N.Monic) (hn' : N'.Monic)
    (hdegree : D'.natDegree ≤ D.natDegree) (hc : IsCoprime D N) (hg : g ≠ 0)
    (h : C g * N * D' = C g' * N' * D) :
    D' = D ∧ N' = N ∧ g' = g := by
  have gain : g = g' := by
    simpa only [leadingCoeff_mul, leadingCoeff_C, hd.leadingCoeff, hd'.leadingCoeff,
      hn.leadingCoeff, hn'.leadingCoeff, mul_one] using congrArg leadingCoeff h
  subst g'
  rw [mul_assoc, mul_assoc] at h
  have e := mul_left_cancel₀ (C_ne_zero.mpr hg) h
  have hv : D ∣ D' := hc.dvd_of_dvd_mul_left ⟨N', by simpa only [mul_comm] using e⟩
  have eq := eq_of_monic_of_dvd_of_natDegree_le hd hd' hv hdegree
  rw [eq] at e
  exact ⟨eq, (mul_right_cancel₀ hd.ne_zero e).symm, rfl⟩

/-- The three-term expansion of the actual finite path at an arbitrary
interior vertex. The two outer lists may be empty. -/
theorem central_determinant (left right : List (PathSite K)) (u c v : PathSite K) :
    intervalCharpoly (left ++ u :: c :: v :: right) =
      (X - C c.diag) * intervalCharpoly (left ++ [u]) * intervalCharpoly (v :: right) -
      C u.weight * intervalCharpoly left * intervalCharpoly (v :: right) -
      C c.weight * intervalCharpoly (left ++ [u]) * intervalCharpoly right := by
  have h₁ := charpoly_cut left (v :: right) u c
  have h₂ := charpoly_cut [] right c v
  have hsingle : intervalCharpoly [c] = X - C c.diag :=
    (charpoly_eq_cont [c]).trans (cont_singleton _)
  have hempty : intervalCharpoly ([] : List (PathSite K)) = 1 :=
    (charpoly_eq_cont _).trans cont_nil
  change intervalCharpoly (left ++ u :: c :: v :: right) =
    intervalCharpoly (left ++ [u]) * intervalCharpoly (c :: v :: right) -
    C u.weight * intervalCharpoly left * intervalCharpoly (v :: right) at h₁
  change intervalCharpoly (c :: v :: right) =
    intervalCharpoly [c] * intervalCharpoly (v :: right) -
    C c.weight * intervalCharpoly [] * intervalCharpoly right at h₂
  rw [h₁, h₂, hsingle, hempty]
  ring

/-- A nonempty left and right branch, each stored away from the central
vertex. The two extra units are the products of rates on the connecting edges. -/
structure Joined (K : Type*) [Field K] (l r : ℕ) where
  left : JacobiData K l
  right : JacobiData K r
  diagonal : K
  leftEdge : Kˣ
  rightEdge : Kˣ

namespace Joined

variable {l r : ℕ}

def determinant (x : Joined K l r) : K[X] :=
  (X - C x.diagonal) * x.left.boundaryPair.1 * x.right.boundaryPair.1 -
  C (x.leftEdge : K) * x.left.boundaryPair.2 * x.right.boundaryPair.1 -
  C (x.rightEdge : K) * x.left.boundaryPair.1 * x.right.boundaryPair.2

/-- With disjoint branch spectra the central diagonal transfer has no
cancellation. This uses coprimality of consecutive determinants in each arm. -/
theorem coprime_central (x : Joined K l r)
    (hc : IsCoprime x.left.boundaryPair.1 x.right.boundaryPair.1) :
    IsCoprime (x.left.boundaryPair.1 * x.right.boundaryPair.1) x.determinant := by
  have left : IsCoprime x.left.boundaryPair.1
      (C (x.leftEdge : K) * x.left.boundaryPair.2 * x.right.boundaryPair.1) := by
    apply IsCoprime.mul_right _ hc
    exact (isCoprime_mul_unit_left_right (x.leftEdge.isUnit.map (C : K →+* K[X])) _ _).mpr
      x.left.consecutive_coprime
  have right : IsCoprime x.right.boundaryPair.1
      (C (x.rightEdge : K) * x.right.boundaryPair.2 * x.left.boundaryPair.1) := by
    apply IsCoprime.mul_right _ hc.symm
    exact (isCoprime_mul_unit_left_right (x.rightEdge.isUnit.map (C : K →+* K[X])) _ _).mpr
      x.right.consecutive_coprime
  apply IsCoprime.mul_left
  · convert left.neg_right.add_mul_left_right
        ((X - C x.diagonal) * x.right.boundaryPair.1 -
        C (x.rightEdge : K) * x.right.boundaryPair.2) using 1
    unfold determinant
    ring
  · convert right.neg_right.add_mul_left_right
        ((X - C x.diagonal) * x.left.boundaryPair.1 -
        C (x.leftEdge : K) * x.left.boundaryPair.2) using 1
    unfold determinant
    ring

private theorem edge_tail_inj {b b' : Kˣ} {p q : K[X]} (hp : p.Monic) (hq : q.Monic)
    (h : C (b : K) * p = C (b' : K) * q) : b = b' ∧ p = q := by
  have hb : b = b' := by
    apply Units.ext
    simpa only [leadingCoeff_C_mul_of_isUnit b.isUnit, leadingCoeff_C_mul_of_isUnit b'.isUnit,
      hp.leadingCoeff, hq.leadingCoeff, mul_one] using congrArg leadingCoeff h
  subst b'
  exact ⟨rfl, (b.isUnit.map (C : K →+* K[X])).mul_left_cancel h⟩

/-- Knowing the full determinant and the characteristic polynomial of each
branch recovers both Jacobi branches, both connecting weights and the central
diagonal, provided the branch polynomials are coprime. -/
theorem eq_of_determinant_and_branches (x y : Joined K l r)
    (hc : IsCoprime x.left.boundaryPair.1 x.right.boundaryPair.1)
    (hD : x.determinant = y.determinant)
    (hL : x.left.boundaryPair.1 = y.left.boundaryPair.1)
    (hR : x.right.boundaryPair.1 = y.right.boundaryPair.1) : x = y := by
  unfold determinant at hD
  rw [← hL, ← hR] at hD
  have hl (x : Joined K l r) : (C (x.leftEdge : K) * x.left.boundaryPair.2).degree <
      x.left.boundaryPair.1.degree := by
    rw [degree_C_mul_of_isUnit x.leftEdge.isUnit]
    exact x.left.boundary_degree
  have hr (x : Joined K l r) : (C (x.rightEdge : K) * x.right.boundaryPair.2).degree <
      x.right.boundaryPair.1.degree := by
    rw [degree_C_mul_of_isUnit x.rightEdge.isUnit]
    exact x.right.boundary_degree
  have eL : C (x.leftEdge : K) * x.left.boundaryPair.2 =
      C (y.leftEdge : K) * y.left.boundaryPair.2 := by
    apply bounded_modular_unique hc (hl x) (hL ▸ hl y)
    refine ⟨(C y.diagonal - C x.diagonal) * x.right.boundaryPair.1 -
      C (x.rightEdge : K) * x.right.boundaryPair.2 +
      C (y.rightEdge : K) * y.right.boundaryPair.2, ?_⟩
    linear_combination -hD
  have eR : C (x.rightEdge : K) * x.right.boundaryPair.2 =
      C (y.rightEdge : K) * y.right.boundaryPair.2 := by
    apply bounded_modular_unique hc.symm (hr x) (hR ▸ hr y)
    refine ⟨(C y.diagonal - C x.diagonal) * x.left.boundaryPair.1 -
      C (x.leftEdge : K) * x.left.boundaryPair.2 +
      C (y.leftEdge : K) * y.left.boundaryPair.2, ?_⟩
    linear_combination -hD
  obtain ⟨ble, plt⟩ := edge_tail_inj (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) eL
  obtain ⟨bre, prt⟩ := edge_tail_inj (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) eR
  have bl := JacobiData.boundaryPair_injective l (Prod.ext hL plt)
  have br := JacobiData.boundaryPair_injective r (Prod.ext hR prt)
  have ce : x.diagonal = y.diagonal := by
    apply C_injective
    apply mul_right_cancel₀ (Matrix.charpoly_monic _).ne_zero (b := x.right.boundaryPair.1)
    apply mul_right_cancel₀ (Matrix.charpoly_monic _).ne_zero (b := x.left.boundaryPair.1)
    rw [← bl, ← br, ← ble, ← bre] at hD
    linear_combination -hD
  cases x
  cases y
  simp_all

/-- With the denominator fixed, the two straddling output numerators isolate
the full central Jacobi data. The outer factors may have arbitrary roots. -/
theorem locally_identified_by_products [TopologicalSpace K] [T1Space K]
    {T : Type*} [TopologicalSpace T] {a : T} (x : T → Joined K l r)
    (P Q : T → K[X]) (hP : P a ≠ 0) (hQ : Q a ≠ 0)
    (hc : IsCoprime (x a).left.boundaryPair.1 (x a).right.boundaryPair.1)
    (cL : ∀ n, ContinuousAt (fun t => (x t).left.boundaryPair.1.coeff n) a)
    (cR : ∀ n, ContinuousAt (fun t => (x t).right.boundaryPair.1.coeff n) a) :
    ∀ᶠ t in 𝓝 a, (x t).determinant = (x a).determinant →
      P t * (x t).right.boundaryPair.1 = P a * (x a).right.boundaryPair.1 →
      (x t).left.boundaryPair.1 * Q t = (x a).left.boundaryPair.1 * Q a → x t = x a := by
  have ml (t : T) : (x t).left.boundaryPair.1.Monic := Matrix.charpoly_monic _
  have mr (t : T) : (x t).right.boundaryPair.1.Monic := Matrix.charpoly_monic _
  filter_upwards [locally_split_product (fun t => (x t).left.boundaryPair.1) Q (ml a) hQ cL,
    locally_split_product (fun t => (x t).right.boundaryPair.1) P (mr a) hP cR]
    with t htL htR eD eR eL
  apply Eq.symm
  exact eq_of_determinant_and_branches _ _ hc eD.symm (htL (ml t) eL).1.symm
    (htR (mr t) (by simpa only [mul_comm] using eR)).1.symm

end Joined
end Catenary.Middle
