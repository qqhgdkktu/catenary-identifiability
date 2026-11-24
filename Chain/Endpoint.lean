import Chain.PhysicalInverse
import Chain.PolynomialReconstruction
import Chain.Obstruction
import Chain.ResolventData

noncomputable section
open Polynomial
open scoped Polynomial
namespace Catenary.Endpoint
open Continuant

private def encode (d : ℕ → ℝ) (w : ℕ → ℝˣ) (u : ℕ) : (q : ℕ) → JacobiData ℝ q
  | 0 => .single (d u)
  | q+1 => .extend (d u) (w u) (encode d w (u+1) q)

private def physicalWeight {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ) (t : ℕ) : ℝˣ :=
  if ht : t < m then Units.mk0 ((physicalSite ℓ θ t).weight) (by
    simp [PathSite.weight,physicalSite,ht,(hp (fwd ⟨t,ht⟩)).ne',(hp (back ⟨t,ht⟩)).ne']) else 1

private def block {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ) (u q : ℕ) :=
  encode (fun t => (physicalSite ℓ θ t).diag) (physicalWeight ℓ θ hp) u q

private theorem weight_eq {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ) (u : ℕ) (hu : u < m) :
    (physicalWeight ℓ θ hp u : ℝ) = (physicalSite ℓ θ u).weight := by simp [physicalWeight,hu]

/-- Evaluate the Jacobi encoding on the actual two physical intervals. -/
private theorem block_eval {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ)
    (s : ℝ) (q u : ℕ) (hu : u+q ≤ m) :
    let f := fun t => shiftedSite s (physicalSite ℓ θ t)
    ((block ℓ θ hp u q).boundaryPair.1.eval s, (block ℓ θ hp u q).boundaryPair.2.eval s) =
      (cont (sitesFrom f u (q+1)), cont (sitesFrom f (u+1) q)) := by
  dsimp only
  induction q generalizing u with
  | zero =>
    have hx : (JacobiData.single (physicalSite ℓ θ u).diag).boundaryPair.2 = 1 :=
      (charpoly_eq_cont ([] : List (PathSite ℝ))).trans cont_nil
    simp [block,encode,JacobiData.boundaryPair_single,hx,sitesFrom,shiftedSite]
  | succ q ih =>
    have e := ih (u+1) (by omega)
    have h₁ := congrArg Prod.fst e
    have h₂ := congrArg Prod.snd e
    dsimp only [Prod.fst,Prod.snd] at h₁ h₂
    let f := fun t => shiftedSite s (physicalSite ℓ θ t)
    have hc : cont (sitesFrom f u (q+2)) =
        (s-(physicalSite ℓ θ u).diag)*cont (sitesFrom f (u+1) (q+1)) -
        (physicalSite ℓ θ u).weight*cont (sitesFrom f ((u+1)+1) q) := by
      change cont (f u :: f (u+1) :: sitesFrom f ((u+1)+1) q) = _
      rw [cont_cons_cons]
      simp [f,shiftedSite,PathSite.weight,sitesFrom]
    apply Prod.ext
    · change ((JacobiData.extend (physicalSite ℓ θ u).diag (physicalWeight ℓ θ hp u)
        (block ℓ θ hp (u+1) q)).boundaryPair.1.eval s) = cont (sitesFrom f u (q+2))
      rw [JacobiData.boundaryPair_extend]
      simp only [eval_sub,eval_mul,eval_X,eval_C,h₁,h₂,weight_eq ℓ θ hp u (by omega)]
      exact hc.symm
    · exact h₁

private theorem read_encode (d d' : ℕ → ℝ) (w w' : ℕ → ℝˣ) (q u : ℕ)
    (he : encode d w u q = encode d' w' u q) :
    (∀ t : ℕ, t ≤ q → d (u+t) = d' (u+t)) ∧
    (∀ t : ℕ, t < q → w (u+t) = w' (u+t)) := by
  induction q generalizing u with
  | zero =>
    have hd : d u = d' u := JacobiData.single.inj he
    constructor
    · intro t ht
      have h : t = 0 := by omega
      simpa [h] using hd
    · intro t ht; omega
  | succ q ih =>
    have ⟨hd,hw,ht⟩ := JacobiData.extend.inj he
    obtain ⟨ed,ew⟩ := ih (u+1) ht
    constructor
    · intro t h
      cases t with
      | zero => exact hd
      | succ t => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ed t (by omega)
    · intro t h
      cases t with
      | zero => exact hw
      | succ t => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ew t (by omega)

private theorem rates_of_equal_block {m} (ℓ : Chamber m) (θ η : Params m)
    (hp : Positive θ) (hp' : Positive η) (he : block ℓ θ hp 0 m = block ℓ η hp' 0 m) : θ = η := by
  obtain ⟨d,w⟩ := read_encode _ _ _ _ _ _ he
  apply PhysicalInverse.rates_of_diagonal_and_products ℓ θ η hp hp'
  · intro c
    simpa [physicalSite,c.isLt] using d c.val (Nat.le_of_lt_succ c.isLt)
  · intro r
    have e := congrArg (fun x : ℝˣ => (x : ℝ)) (w r.val r.isLt)
    simpa [weight_eq, PathSite.weight,physicalSite,r.isLt,mul_comm] using e

private theorem endpoint_fraction {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ)
    (s : ℝ) (hdet : (s • (1 : Mat m) - generator ℓ θ).det ≠ 0) :
    (s • (1 : Mat m) - generator ℓ θ)⁻¹ 0 0 =
      (block ℓ θ hp 0 m).boundaryPair.2.eval s / (block ℓ θ hp 0 m).boundaryPair.1.eval s := by
  have e := block_eval ℓ θ hp s m 0 (by omega)
  have h₁ := congrArg Prod.fst e
  have h₂ := congrArg Prod.snd e
  dsimp only [Prod.fst,Prod.snd] at h₁ h₂
  rw [h₁,h₂]
  have h := (physical_transfer_formula ℓ 0 0 θ s hp le_rfl hdet).1
  simpa [physicalSites, sitesFrom_map, sitesFrom, directedProduct] using h

private theorem block_denominator {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ)
    (s : ℝ) :
    (block ℓ θ hp 0 m).boundaryPair.1.eval s = (s • (1 : Mat m) - generator ℓ θ).det := by
  have e := congrArg Prod.fst (block_eval ℓ θ hp s m 0 (by omega))
  rw [physical_pencil_eq_pathMatrix, Matrix.det_submatrix_equiv_self,det_eq_cont,physicalSites,sitesFrom_map]
  exact e

/-- The two monic consecutive polynomials are uniquely determined by their ratio.
This works at every positive choice of the edge weights. -/
private theorem pair_of_cross {m} (x y : JacobiData ℝ m)
    (h : x.boundaryPair.2 * y.boundaryPair.1 = y.boundaryPair.2 * x.boundaryPair.1) :
    x = y := by
  have hp : x.boundaryPair.1 ∣ y.boundaryPair.1 := by
    apply x.consecutive_coprime.dvd_of_dvd_mul_left
    rw [h]
    exact dvd_mul_left _ _
  have hdg (b : JacobiData ℝ m) : b.boundaryPair.1.natDegree = m+1 :=
    (intervalCharpoly_natDegree _).trans b.sites_length
  have eq : y.boundaryPair.1 = x.boundaryPair.1 :=
    eq_of_monic_of_dvd_of_natDegree_le (p:=x.boundaryPair.1) (q:=y.boundaryPair.1)
      (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) hp (by rw [hdg,hdg])
  have tail : x.boundaryPair.2 = y.boundaryPair.2 := by
    rw [eq] at h
    exact mul_right_cancel₀ (Matrix.charpoly_monic _).ne_zero h
  exact JacobiData.boundaryPair_injective m (Prod.ext eq.symm tail)

/-- At an observed end, for every positive vector, the endpoint transfer alone
determines all directed rates and the one leak. Regular frequencies suffice. -/
theorem rates_of_endpoint_transfer {m} (ℓ : Chamber m) (θ η : Params m)
    (hp : Positive θ) (hp' : Positive η) (he : ∀ s : ℝ,
      (s • (1 : Mat m) - generator ℓ θ).det ≠ 0 → (s • (1 : Mat m) - generator ℓ η).det ≠ 0 →
      (s • (1 : Mat m) - generator ℓ θ)⁻¹ 0 0 = (s • (1 : Mat m) - generator ℓ η)⁻¹ 0 0) :
    θ = η := by
  let x := block ℓ θ hp 0 m
  let y := block ℓ η hp' 0 m
  have hx : x.boundaryPair.1 ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hy : y.boundaryPair.1 ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hinf := (finite_setOf_isRoot (mul_ne_zero hx hy)).infinite_compl
  apply rates_of_equal_block ℓ θ η hp hp'
  apply pair_of_cross x y
  apply eq_of_infinite_eval_eq
  apply hinf.mono
  intro s hs
  change (x.boundaryPair.1*y.boundaryPair.1).eval s ≠ 0 at hs
  rw [eval_mul] at hs
  obtain ⟨hsx,hsy⟩ := mul_ne_zero_iff.mp hs
  have hdx := (block_denominator ℓ θ hp s) ▸ hsx
  have hdy := (block_denominator ℓ η hp' s) ▸ hsy
  have h := he s hdx hdy
  rw [endpoint_fraction ℓ θ hp s hdx,endpoint_fraction ℓ η hp' s hdy] at h
  change x.boundaryPair.2.eval s / x.boundaryPair.1.eval s =
      y.boundaryPair.2.eval s / y.boundaryPair.1.eval s at h
  change (x.boundaryPair.2 * y.boundaryPair.1).eval s = (y.boundaryPair.2 * x.boundaryPair.1).eval s
  simpa only [eval_mul] using (div_eq_div_iff hsx hsy).mp h

/-- Input at the first chamber and either sensor at that chamber.
The result is global for each pair of positive physical rate vectors. -/
theorem observed_endpoint_global {m} (k ℓ : Chamber m) (θ η : Params m)
    (hθ : Positive θ) (hη : Positive η) (h : SameCurves (m:=m) 0 0 k ℓ θ η) : θ = η := by
  apply rates_of_endpoint_transfer ℓ θ η hθ hη
  intro s hs hs'
  exact ((sameCurves_iff_common_regular (m:=m) 0 0 k ℓ θ η).mp h s hs hs').1

theorem observed_endpoint_generic {m} (k ℓ : Chamber m) : GenericLocalID (m:=m) 0 0 k ℓ := by
  refine ⟨1, ⟨fun _ => 1,fun _ => zero_lt_one,by simp⟩,?_⟩
  intro θ hθ _
  exact ⟨1,zero_lt_one,fun η hη _ h => (observed_endpoint_global k ℓ θ η hθ hη h).symm⟩

end Catenary.Endpoint
