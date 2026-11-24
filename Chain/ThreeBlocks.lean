import Chain.PolynomialReconstruction

/-! Reconstruction of all three blocks in §4, over a ring with unit edge
weights. Sites are ordered from the left in every actual determinant. The
two blocks reconstructed from their right endpoint keep their data in
reverse order internally, with the edge stored on its actual left endpoint. -/

noncomputable section
namespace Catenary.ThreeBlocks
open Polynomial Continuant
open scoped Polynomial
variable {R : Type*} [CommRing R]

def lastDiagonal {n} : JacobiData R n → R
  | .single a => a
  | .extend a _ _ => a

def lastSite {n} (t : JacobiData R n) (c : R) : PathSite R := ⟨lastDiagonal t, c, 1⟩

/-- Sites preceding the last vertex, with edge weights in physical left-to-right order. -/
def before {n} : JacobiData R n → List (PathSite R)
  | .single _ => []
  | .extend _ b t => before t ++ [lastSite t (b : R)]

def internalWeights {n} : JacobiData R n → Rˣ
  | .single _ => 1
  | .extend _ b t => internalWeights t * b

theorem edgeProduct_before {n} (t : JacobiData R n) :
    edgeProduct (before t) = (internalWeights t : R) := by
  induction t with
  | single => simp [before, edgeProduct, internalWeights]
  | extend a b t ih =>
    simpa [before, edgeProduct, lastSite, PathSite.weight, internalWeights] using
      congrArg (fun r : R => r * (b : R)) ih

private theorem chi_nil : intervalCharpoly ([] : List (PathSite R)) = 1 :=
  (charpoly_eq_cont _).trans cont_nil

private theorem chi_one (a : PathSite R) : intervalCharpoly [a] = X - C a.diag :=
  (charpoly_eq_cont _).trans (cont_singleton _)

/-- The reversal moves the weights to the preceding vertex. Both polynomials
are the characteristic polynomials of the physically ordered interval. -/
theorem rightBoundary {n} (t : JacobiData R n) :
    (∀ c, intervalCharpoly (before t ++ [lastSite t c]) = t.boundaryPair.1) ∧
      intervalCharpoly (before t) = t.boundaryPair.2 := by
  induction t with
  | single a =>
    exact ⟨fun c => (chi_one _).trans (JacobiData.boundaryPair_single a).symm, rfl⟩
  | extend a b t ih =>
    refine ⟨fun c => ?_, ih.1 (b : R)⟩
    let u := lastSite t (b : R)
    let v := lastSite (JacobiData.extend a b t) c
    change intervalCharpoly ((before t ++ [u]) ++ [v]) = _
    rw [List.append_assoc]
    change intervalCharpoly (before t ++ u :: v :: []) = _
    rw [show intervalCharpoly (before t ++ u :: v :: []) =
      intervalCharpoly (before t ++ [u]) * intervalCharpoly [v] -
        C u.weight * intervalCharpoly (before t) * intervalCharpoly [] from
      charpoly_cut (before t) [] u v]
    rw [ih.1, ih.2, chi_one, chi_nil, JacobiData.boundaryPair_extend]
    simp only [u, v, lastSite, lastDiagonal, PathSite.weight, mul_one]
    ring

/-- A tail of r vertices. Its entrance edge exists exactly when r>0. -/
inductive Tail (R : Type*) [CommRing R] : ℕ → Type _
  | empty : Tail R 0
  | nonempty {n} (entrance : Rˣ) (block : JacobiData R n) : Tail R (n+1)

namespace Tail

def sites {r} : Tail R r → List (PathSite R)
  | .empty => []
  | .nonempty _ t => t.sites

def entrance {r} : Tail R r → R
  | .empty => 0
  | .nonempty b _ => b

def U {r} (t : Tail R r) : R[X] := intervalCharpoly t.sites

def V {r} : Tail R r → R[X]
  | .empty => 0
  | .nonempty b t => C (b : R) * t.boundaryPair.2

theorem V_degree [Nontrivial R] {r} (x : Tail R r) : x.V.degree < x.U.degree := by
  cases x with
  | empty => simp [V, U, sites, chi_nil]
  | nonempty b t =>
    change (C (b : R) * t.boundaryPair.2).degree < t.boundaryPair.1.degree
    rw [degree_C_mul_of_isUnit b.isUnit]
    exact t.boundary_degree

end Tail

private theorem unit_monic_factors {a b : Rˣ} {p q : R[X]} (hp : p.Monic) (hq : q.Monic)
    (h : C (a : R) * p = C (b : R) * q) : a = b ∧ p = q := by
  have hab : a = b := by
    apply Units.ext
    simpa only [leadingCoeff_C_mul_of_isUnit a.isUnit, leadingCoeff_C_mul_of_isUnit b.isUnit,
      hp.leadingCoeff, hq.leadingCoeff, mul_one] using congrArg leadingCoeff h
  subst b
  exact ⟨rfl, (a.isUnit.map (C : R →+* R[X])).mul_left_cancel h⟩

theorem Tail.recover [Nontrivial R] {r} (x y : Tail R r)
    (hU : x.U = y.U) (hV : x.V = y.V) : x = y := by
  cases x with
  | empty => cases y; rfl
  | nonempty b t =>
    cases y with
    | nonempty c u =>
      obtain ⟨hb, ht⟩ := unit_monic_factors (a := b) (b := c)
        (p := t.boundaryPair.2) (q := u.boundaryPair.2)
        (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) hV
      rw [hb, JacobiData.boundaryPair_injective _ (Prod.ext hU ht)]

def rightPart {g r} (mid : JacobiData R g) (tail_ : Tail R r) : List (PathSite R) :=
  before mid ++ lastSite mid tail_.entrance :: tail_.sites

private theorem sites_cons {n} (t : JacobiData R n) : ∃ a xs, t.sites = a :: xs := by
  cases t <;> exact ⟨_, _, rfl⟩

theorem right_cut {g r} (mid : JacobiData R g) (tail_ : Tail R r) :
    intervalCharpoly (rightPart mid tail_) =
      tail_.U * mid.boundaryPair.1 - tail_.V * mid.boundaryPair.2 := by
  cases tail_ with
  | empty =>
    simpa [rightPart, Tail.sites, Tail.U, Tail.V, Tail.entrance, chi_nil] using
      (rightBoundary mid).1 0
  | nonempty b t =>
    obtain ⟨u, us, hus⟩ := sites_cons t
    let k := lastSite mid (b : R)
    have h := charpoly_cut (before mid) us k u
    change intervalCharpoly (before mid ++ k :: t.sites) =
      intervalCharpoly t.sites * mid.boundaryPair.1 -
      (C (b : R) * intervalCharpoly t.sites.tail) * mid.boundaryPair.2
    rw [hus, List.tail_cons]
    change intervalCharpoly (before mid ++ k :: u :: us) =
      intervalCharpoly (before mid ++ [k]) * intervalCharpoly (u :: us) -
      C k.weight * intervalCharpoly (before mid) * intervalCharpoly us at h
    rw [(rightBoundary mid).1, (rightBoundary mid).2] at h
    rw [h]
    simp only [k, lastSite, PathSite.weight, mul_one]
    ring

/-- d=j-1, g=k-j-1 and r=n-k. Both d=0 and g=0 are legitimate
single-vertex blocks. Their stored edges are all units. -/
structure Blocks (R : Type*) [CommRing R] (d g r : ℕ) where
  left : JacobiData R d
  bridge : Rˣ
  middle : JacobiData R g
  tail_ : Tail R r

namespace Blocks

def full {d g r} (x : Blocks R d g r) : List (PathSite R) :=
  before x.left ++ lastSite x.left (x.bridge : R) :: rightPart x.middle x.tail_

def K {d g r} (x : Blocks R d g r) : Rˣ := x.bridge * internalWeights x.middle

def P {d g r} (x : Blocks R d g r) : R[X] :=
  C (x.K : R) * intervalCharpoly (before x.left)

theorem left_cut {d g r} (x : Blocks R d g r) :
    intervalCharpoly x.full = x.left.boundaryPair.1 * intervalCharpoly (rightPart x.middle x.tail_) -
      C (x.bridge : R) * x.left.boundaryPair.2 *
        intervalCharpoly (rightPart x.middle x.tail_).tail := by
  let v := lastSite x.left (x.bridge : R)
  obtain ⟨z, zs, hzs⟩ : ∃ z zs, rightPart x.middle x.tail_ = z :: zs := by
    unfold rightPart
    cases before x.middle <;> exact ⟨_, _, rfl⟩
  change intervalCharpoly (before x.left ++ v :: rightPart x.middle x.tail_) = _
  rw [hzs, List.tail_cons]
  have h := charpoly_cut (before x.left) zs v z
  change intervalCharpoly (before x.left ++ v :: z :: zs) =
    intervalCharpoly (before x.left ++ [v]) * intervalCharpoly (z :: zs) -
    C v.weight * intervalCharpoly (before x.left) * intervalCharpoly zs at h
  rw [(rightBoundary x.left).1, (rightBoundary x.left).2] at h
  simpa only [v, lastSite, PathSite.weight, mul_one] using h

end Blocks

structure Five (R : Type*) [CommRing R] where
  D : R[X]
  W : R[X]
  U : R[X]
  B : R[X]
  P : R[X]

def data {d g r} (x : Blocks R d g r) : Five R :=
  ⟨intervalCharpoly x.full, intervalCharpoly (rightPart x.middle x.tail_), x.tail_.U,
   intervalCharpoly (before x.middle), x.P⟩

/-- Uniqueness modulo a monic polynomial also holds over nonreduced rings. -/
theorem bounded_recovery [Nontrivial R] {u b v w : R[X]} (hu : u.Monic)
    (hc : IsCoprime u b) (hv : v.degree < u.degree) (hw : w.degree < u.degree)
    (h : u ∣ b * (v-w)) : v = w := by
  apply sub_eq_zero.mp
  have h₁ := (modByMonic_eq_zero_iff_dvd hu).mpr (hc.dvd_of_dvd_mul_left h)
  rwa [(modByMonic_eq_self_iff hu).mpr ((degree_sub_le _ _).trans_lt (max_lt hv hw))] at h₁

/-- The five actual polynomials recover all diagonal entries and all unit
weights. Coprimality at the first chain suffices. -/
theorem data_injective_at [Nontrivial R] {d g r} (x y : Blocks R d g r)
    (hc : IsCoprime (data x).B (data x).U) (he : data x = data y) : x = y := by
  have hD := congrArg Five.D he
  have hW := congrArg Five.W he
  have hU : x.tail_.U = y.tail_.U := congrArg Five.U he
  have hB : x.middle.boundaryPair.2 = y.middle.boundaryPair.2 :=
    ((rightBoundary x.middle).2.symm.trans (congrArg Five.B he)).trans (rightBoundary y.middle).2
  have hP := congrArg Five.P he
  obtain ⟨hK, hE'⟩ := unit_monic_factors (a := x.K) (b := y.K)
    (p := intervalCharpoly (before x.left)) (q := intervalCharpoly (before y.left))
    (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) hP
  have hE := ((rightBoundary x.left).2.symm.trans hE').trans (rightBoundary y.left).2
  change intervalCharpoly (rightPart x.middle x.tail_) = intervalCharpoly (rightPart y.middle y.tail_) at hW
  obtain ⟨hV, hM⟩ : x.tail_.V = y.tail_.V ∧ x.middle.boundaryPair.1 = y.middle.boundaryPair.1 := by
    rw [right_cut, right_cut, ← hU, ← hB] at hW
    have hmod : x.tail_.U ∣ x.middle.boundaryPair.2 * (x.tail_.V-y.tail_.V) := by
      refine ⟨x.middle.boundaryPair.1-y.middle.boundaryPair.1, ?_⟩
      linear_combination -hW
    have hcop : IsCoprime x.tail_.U x.middle.boundaryPair.2 := by
      rw [← (rightBoundary x.middle).2]
      exact hc.symm
    have hydeg : y.tail_.V.degree < x.tail_.U.degree := by rw [hU]; exact y.tail_.V_degree
    have hV := bounded_recovery (u := x.tail_.U) (Matrix.charpoly_monic _) hcop
      x.tail_.V_degree hydeg hmod
    refine ⟨hV, (Matrix.charpoly_monic _ : x.tail_.U.Monic).isRegular.1 ?_⟩
    rw [hV] at hW
    exact sub_left_inj.mp hW
  have ht := Tail.recover x.tail_ y.tail_ hU hV
  have hm := JacobiData.boundaryPair_injective _ (Prod.ext hM hB)
  have hb : x.bridge = y.bridge := by
    change x.bridge * internalWeights x.middle = y.bridge * internalWeights y.middle at hK
    rw [hm] at hK
    exact mul_right_cancel hK
  change intervalCharpoly x.full = intervalCharpoly y.full at hD
  rw [Blocks.left_cut, Blocks.left_cut, hm, ht, hb, hE] at hD
  have hL := (Matrix.charpoly_monic _ : (intervalCharpoly (rightPart y.middle y.tail_)).Monic).isRegular.2
    (sub_left_inj.mp hD)
  have hl := JacobiData.boundaryPair_injective _ (Prod.ext hL hE)
  cases x; cases y; congr

theorem dual_data_injective_at [Nontrivial R] {d g r} (x y : Blocks (DualNumber R) d g r)
    (hc : IsCoprime (data x).B (data x).U) (he : data x = data y) : x = y :=
  data_injective_at x y hc he

/-- Reduction modulo ε on the coefficient ring. -/
def residue : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom

private theorem square_zero_of_residue (q : (DualNumber R)[X]) (hq : q.map residue = 0) :
    q*q = 0 := by
  have hcoeff (i : ℕ) : (q.coeff i).fst = 0 := by
    simpa only [coeff_map, coeff_zero] using congrArg (fun f : R[X] => f.coeff i) hq
  apply Polynomial.ext
  intro i
  rw [coeff_mul, coeff_zero]
  apply Finset.sum_eq_zero
  intro uv _
  apply TrivSqZeroExt.ext <;> simp [hcoeff]

/-- Coprimality of real/base values suffices for coprimality after arbitrary
first variations. The error of the lifted Bézout identity squares to zero. -/
theorem dual_coprime_of_residue (b u : (DualNumber R)[X])
    (hc : IsCoprime (b.map residue) (u.map residue)) : IsCoprime b u := by
  obtain ⟨a, c, h⟩ := hc
  let incl := TrivSqZeroExt.inlHom R R
  have hi (f : R[X]) : (f.map incl).map residue = f := by
    ext i
    simp only [coeff_map]
    rfl
  let e := 1 - (a.map incl * b + c.map incl * u)
  have he : e.map residue = 0 := by simp [e, hi, h]
  have hn := square_zero_of_residue e he
  refine ⟨(1+e)*a.map incl, (1+e)*c.map incl, ?_⟩
  calc
    _ = (1+e)*(1-e) := by dsimp [e]; ring
    _ = 1 := by linear_combination -hn

theorem recover_first_variations [Nontrivial R] {d g r} (x y : Blocks (DualNumber R) d g r)
    (hc : IsCoprime ((data x).B.map residue) ((data x).U.map residue))
    (he : data x = data y) : x = y :=
  dual_data_injective_at x y (dual_coprime_of_residue _ _ hc) he

end Catenary.ThreeBlocks
