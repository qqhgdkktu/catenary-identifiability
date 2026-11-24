import Chain.MiddlePhysical
import Chain.Obstruction

/-! The two actual output curves recover an interior input's Jacobi branches
and hence the original rates under explicit coprimality conditions. -/

noncomputable section

open Polynomial Catenary.Continuant Catenary.Obstruction
open Filter Set
open scoped Polynomial Topology

namespace Catenary.Middle

def full {m} (ℓ : Chamber m) (θ : Params m) : ℝ[X] := intervalCharpoly (physicalSites ℓ θ)
def «prefix» {m} (ℓ : Chamber m) (θ : Params m) (u : ℕ) : ℝ[X] :=
  intervalCharpoly ((physicalSites ℓ θ).take u)
def suffix {m} (ℓ : Chamber m) (θ : Params m) (u : ℕ) : ℝ[X] :=
  intervalCharpoly ((physicalSites ℓ θ).drop (u+1))

private def symbolicSites {m} (ℓ : Chamber m) : List (PathSite (RatePoly m)) :=
  sitesFrom (symbolicSite ℓ) 0 (m+1)

def symbolicFull {m} (ℓ : Chamber m) : (RatePoly m)[X] := intervalCharpoly (symbolicSites ℓ)
def symbolicPrefix {m} (ℓ : Chamber m) (u : ℕ) : (RatePoly m)[X] :=
  intervalCharpoly ((symbolicSites ℓ).take u)
def symbolicSuffix {m} (ℓ : Chamber m) (u : ℕ) : (RatePoly m)[X] :=
  intervalCharpoly ((symbolicSites ℓ).drop (u+1))

private theorem eval_sites {m} (ℓ : Chamber m) (θ : Params m) :
    (symbolicSites ℓ).map (mapSite (MvPolynomial.eval θ)) = physicalSites ℓ θ := by
  simp only [symbolicSites, physicalSites, sitesFrom_map, eval_symbolicSite]

@[simp] theorem eval_symbolicFull {m} (ℓ : Chamber m) (θ : Params m) :
    (symbolicFull ℓ).map (MvPolynomial.eval θ) = full ℓ θ := by
  simp only [symbolicFull, full, map_interval, eval_sites]

@[simp] theorem eval_symbolicPrefix {m} (ℓ : Chamber m) (θ : Params m) (u : ℕ) :
    (symbolicPrefix ℓ u).map (MvPolynomial.eval θ) = «prefix» ℓ θ u := by
  simp only [symbolicPrefix, «prefix», map_interval, List.map_take, eval_sites]

@[simp] theorem eval_symbolicSuffix {m} (ℓ : Chamber m) (θ : Params m) (u : ℕ) :
    (symbolicSuffix ℓ u).map (MvPolynomial.eval θ) = suffix ℓ θ u := by
  simp only [symbolicSuffix, suffix, map_interval, List.map_drop, eval_sites]

theorem drop_from {R : Type*} (f : ℕ → PathSite R) (u n k : ℕ) (hk : k ≤ n) :
    (sitesFrom f u n).drop k = sitesFrom f (u+k) (n-k) := by
  induction k generalizing u n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [sitesFrom,List.drop_succ_cons,Nat.succ_sub_succ_eq_sub]
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (u+1) n (by omega)

theorem interval_coefficient_continuous {m} (ℓ : Chamber m) (u q n : ℕ) :
    Continuous (fun θ : Params m => (intervalCharpoly (sitesFrom (physicalSite ℓ θ) u q)).coeff n) := by
  let p := (intervalCharpoly (sitesFrom (symbolicSite ℓ) u q)).coeff n
  convert (MvPolynomial.continuous_eval p) using 1
  funext θ
  have e := congrArg (fun p : ℝ[X] => p.coeff n)
    (map_interval (MvPolynomial.eval θ) (sitesFrom (symbolicSite ℓ) u q))
  simpa only [p, coeff_map, sitesFrom_map, eval_symbolicSite] using e.symm

private theorem full_eval {m} (ℓ : Chamber m) (θ : Params m) (s : ℝ) :
    (full ℓ θ).eval s = (s • 1 - generator ℓ θ).det := by
  rw [← TransferData.eval_charpoly_eq_det, physical_charpoly_eq_cont]
  exact congrArg (Polynomial.eval s) (charpoly_eq_cont _)

private def gain {m} (ℓ : Chamber m) (θ : Params m) (u v : ℕ) : ℝ :=
  pathGain (((physicalSites ℓ θ).drop u).take (v-u))
private def reverseGain {m} (ℓ : Chamber m) (θ : Params m) (u v : ℕ) : ℝ :=
  pathGain ((((physicalSites ℓ θ).drop u).take (v-u)).map swapSite)

private theorem comm_shift (s : ℝ) (xs : List (PathSite ℝ)) :
    (xs.map (shiftedSite s)).map swapSite = (xs.map swapSite).map (shiftedSite s) := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
    simp only [List.map_cons, ih]
    rfl

private theorem transfer_fractions {m} (ℓ u v : Chamber m) (θ : Params m) (hθ : Positive θ)
    (huv : u ≤ v) (s : ℝ) (hs : (s • 1 - generator ℓ θ).det ≠ 0) :
    (s • (1 : Mat m) - generator ℓ θ)⁻¹ v u =
      gain ℓ θ u.val v.val * («prefix» ℓ θ u.val * suffix ℓ θ v.val).eval s / (full ℓ θ).eval s ∧
    (s • (1 : Mat m) - generator ℓ θ)⁻¹ u v =
      reverseGain ℓ θ u.val v.val * («prefix» ℓ θ u.val * suffix ℓ θ v.val).eval s / (full ℓ θ).eval s := by
  obtain ⟨h₁,h₂⟩ := physical_transfer_formula ℓ u v θ s hθ huv hs
  rw [h₁,h₂]
  simp only [gain, reverseGain, «prefix», suffix, full, eval_mul, interval_eval,
    ← List.map_take, ← List.map_drop, comm_shift, directedProduct_shift, mul_left_comm, and_self]

private theorem good_gains {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ)
    (u v : Chamber m) (huv : u ≤ v) : gain ℓ θ u.val v.val ≠ 0 ∧ reverseGain ℓ θ u.val v.val ≠ 0 := by
  let f := physicalSite ℓ θ
  have along (a n : ℕ) (h : a+n ≤ m) :
      pathGain (sitesFrom f a n) ≠ 0 ∧ pathGain ((sitesFrom f a n).map swapSite) ≠ 0 := by
    induction n generalizing a with
    | zero => simp [sitesFrom,pathGain]
    | succ n ih =>
      obtain ⟨hf,hr⟩ := ih (a+1) (by omega)
      have ha : a < m := by omega
      exact ⟨mul_ne_zero (by simpa [f,physicalSite,ha] using (hp (fwd ⟨a,ha⟩)).ne') hf,
             mul_ne_zero (by simpa [f,physicalSite,ha,swapSite] using (hp (back ⟨a,ha⟩)).ne') hr⟩
  have hu := u.isLt
  have hv := v.isLt
  have hval : u.val ≤ v.val := huv
  have e : ((physicalSites ℓ θ).drop u.val).take (v.val - u.val) =
      sitesFrom f u.val (v.val-u.val) := by
    rw [physicalSites,drop_from _ _ _ _ (by omega),sitesFrom_take _ _ _ _ (by omega)]
    simp [f]
  unfold gain reverseGain
  rw [e]
  exact along _ _ (by omega)

private theorem curves_cross {m} (i j k ℓ : Chamber m) (θ η : Params m)
    (hθ : Positive θ) (hη : Positive η) (hji : j ≤ i) (hik : i ≤ k)
    (h : SameCurves i j k ℓ θ η) :
    C (reverseGain ℓ θ j.val i.val) * («prefix» ℓ θ j.val * suffix ℓ θ i.val) * full ℓ η =
      C (reverseGain ℓ η j.val i.val) * («prefix» ℓ η j.val * suffix ℓ η i.val) * full ℓ θ ∧
    C (gain ℓ θ i.val k.val) * («prefix» ℓ θ i.val * suffix ℓ θ k.val) * full ℓ η =
      C (gain ℓ η i.val k.val) * («prefix» ℓ η i.val * suffix ℓ η k.val) * full ℓ θ := by
  have he := (sameCurves_iff_common_regular i j k ℓ θ η).mp h
  have hi := TransferData.common_regular_infinite (generator ℓ θ) (generator ℓ η)
  constructor
  · apply eq_of_infinite_eval_eq
    apply hi.mono
    intro s hs
    have e := (he s hs.1 hs.2).1
    rw [(transfer_fractions ℓ j i θ hθ hji s hs.1).2,
      (transfer_fractions ℓ j i η hη hji s hs.2).2] at e
    have z := (div_eq_div_iff (by rw [full_eval]; exact hs.1) (by rw [full_eval]; exact hs.2)).mp e
    simpa only [Set.mem_setOf_eq, eval_mul, eval_C] using z
  · apply eq_of_infinite_eval_eq
    apply hi.mono
    intro s hs
    have e := (he s hs.1 hs.2).2
    rw [(transfer_fractions ℓ i k θ hθ hik s hs.1).1,
      (transfer_fractions ℓ i k η hη hik s hs.2).1] at e
    have z := (div_eq_div_iff (by rw [full_eval]; exact hs.1) (by rw [full_eval]; exact hs.2)).mp e
    simpa only [Set.mem_setOf_eq, eval_mul, eval_C] using z

theorem prefix_coeff_continuous {m} (ℓ u : Chamber m) (n : ℕ) :
    Continuous (fun θ : Params m => («prefix» ℓ θ u.val).coeff n) := by
  simpa only [«prefix»,physicalSites,sitesFrom_take _ 0 (m+1) u.val u.isLt.le]
    using interval_coefficient_continuous ℓ 0 u.val n

theorem suffix_coeff_continuous {m} (ℓ u : Chamber m) (n : ℕ) :
    Continuous (fun θ : Params m => (suffix ℓ θ u.val).coeff n) := by
  have hu : u.val+1 ≤ m+1 := u.isLt
  simpa only [suffix,physicalSites,drop_from _ 0 (m+1) (u.val+1) hu,Nat.zero_add]
    using interval_coefficient_continuous ℓ (u.val+1) (m+1-(u.val+1)) n

theorem joined_parts {m} (ℓ i : Chamber m) (θ : Params m) (hθ : Positive θ)
    (l r : ℕ) (hn : l+r+2=m) (hi : i.val=l+1) :
    let x := physicalJoined ℓ θ hθ l r
    x.left.boundaryPair.1 = «prefix» ℓ θ i.val ∧ x.right.boundaryPair.1 = suffix ℓ θ i.val := by
  obtain ⟨hL,hR⟩ := physicalJoined_branches ℓ θ hθ l r hn
  have h1 := congrArg Prod.fst hL
  have h2 := congrArg Prod.fst hR
  have hui : i.val+1 ≤ m+1 := i.isLt
  simp only [Prod.fst] at h1 h2
  dsimp only [«prefix»,suffix,physicalSites]
  rw [sitesFrom_take _ 0 (m+1) i.val i.isLt.le, drop_from _ 0 (m+1) (i.val+1) hui]
  simpa only [Nat.zero_add, hi, show m+1-(l+1+1)=r+1 by omega] using And.intro h1 h2

/-- At an interior input, any two outputs straddling it locally determine all
positive physical rates if the two arms have coprime spectra and the reference
left transfer is reduced. The leak position and the competing parameter are
unrestricted. Either output may coincide with the input. -/
theorem local_middle_of_coprime {m} (i j k ℓ : Chamber m) (θ : Params m) (hθ : Positive θ)
    (hinnerL : 0 < i.val) (hinnerR : i.val < m) (hji : j ≤ i) (hik : i ≤ k)
    (hc : IsCoprime («prefix» ℓ θ i.val) (suffix ℓ θ i.val))
    (hj : IsCoprime (full ℓ θ) («prefix» ℓ θ j.val * suffix ℓ θ i.val)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : Params m, Positive η → dist η θ < ε →
      SameCurves i j k ℓ θ η → η = θ := by
  let l := i.val-1
  let r := m-(i.val+1)
  have hn : l+r+2=m := by dsimp [l,r]; omega
  have hi : i.val=l+1 := by dsimp [l]; omega
  have mP (a : Params m) (q : ℕ) : («prefix» ℓ a q).Monic := Matrix.charpoly_monic _
  have mS (a : Params m) (q : ℕ) : (suffix ℓ a q).Monic := Matrix.charpoly_monic _
  have mD (a : Params m) : (full ℓ a).Monic := Matrix.charpoly_monic _
  have splitL := locally_split_product (fun a => «prefix» ℓ a i.val)
    (fun a => suffix ℓ a k.val) (mP θ i.val) (mS θ k.val).ne_zero
    (fun n => (prefix_coeff_continuous ℓ i n).continuousAt)
  have splitR := locally_split_product (fun a => suffix ℓ a i.val)
    (fun a => «prefix» ℓ a j.val) (mS θ i.val) (mP θ j.val).ne_zero
    (fun n => (suffix_coeff_continuous ℓ i n).continuousAt)
  have localID : ∀ᶠ η in 𝓝 θ, Positive η → SameCurves i j k ℓ θ η → η = θ := by
    filter_upwards [splitL,splitR] with η hxL hxR hp hcurves
    obtain ⟨eL,eR⟩ := curves_cross i j k ℓ θ η hθ hp hji hik hcurves
    have hdg : (full ℓ η).natDegree ≤ (full ℓ θ).natDegree := by
      simp only [full, intervalCharpoly_natDegree, physicalSites_length, le_refl]
    obtain ⟨hD, hN, _⟩ := scaled_fraction_of_cross (mD θ) (mD η)
      ((mP θ _).mul (mS θ _)) ((mP η _).mul (mS η _)) hdg hj (good_gains ℓ θ hθ j i hji).2 eL
    have rightNum : «prefix» ℓ θ i.val * suffix ℓ θ k.val =
        «prefix» ℓ η i.val * suffix ℓ η k.val := by
      rw [hD] at eR
      have e := mul_right_cancel₀ (mD θ).ne_zero eR
      have g : gain ℓ θ i.val k.val = gain ℓ η i.val k.val := by
        simpa only [leadingCoeff_mul, leadingCoeff_C, (mP _ _).leadingCoeff,
          (mS _ _).leadingCoeff, mul_one] using congrArg leadingCoeff e
      rw [← g] at e
      exact mul_left_cancel₀ (C_ne_zero.mpr (good_gains ℓ θ hθ i k hik).1) e
    have left := (hxL (mP η _) rightNum.symm).1
    have right := (hxR (mS η _) (by simpa only [mul_comm] using hN)).1
    obtain ⟨lθ,rθ⟩ := joined_parts ℓ i θ hθ l r hn hi
    obtain ⟨lη,rη⟩ := joined_parts ℓ i η hp l r hn hi
    apply rates_of_physicalJoined ℓ η θ hp hθ l r hn
    apply Eq.symm
    apply Joined.eq_of_determinant_and_branches
    · rwa [lθ,rθ]
    · rw [physicalJoined_determinant _ _ _ _ _ hn, physicalJoined_determinant _ _ _ _ _ hn]
      exact hD.symm
    · exact lθ.trans (left.symm.trans lη.symm)
    · exact rθ.trans (right.symm.trans rη.symm)
  obtain ⟨ε,hε,hall⟩ := Metric.eventually_nhds_iff_ball.mp localID
  exact ⟨ε,hε,fun η hp hd hs => hall η hd hp hs⟩

/-- Two coprimality certificates valid and nonzero at a common positive
witness give the physical generic statement at any interior straddled input. -/
theorem generic_middle_of_certificates {m} (i j k ℓ : Chamber m)
    (hinnerL : 0 < i.val) (hinnerR : i.val < m) (hji : j ≤ i) (hik : i ≤ k)
    (p q : RatePoly m) (a : Params m) (ha : Positive a)
    (hp : MvPolynomial.eval a p ≠ 0) (hq : MvPolynomial.eval a q ≠ 0)
    (hbranch : ∀ θ : Params m, MvPolynomial.eval θ p ≠ 0 →
      IsCoprime («prefix» ℓ θ i.val) (suffix ℓ θ i.val))
    (hleft : ∀ θ : Params m, MvPolynomial.eval θ q ≠ 0 →
      IsCoprime (full ℓ θ) («prefix» ℓ θ j.val * suffix ℓ θ i.val)) :
    GenericLocalID i j k ℓ := by
  refine ⟨p*q, ⟨a,ha,by simpa only [map_mul] using mul_ne_zero hp hq⟩,?_⟩
  intro θ hθ h
  rw [map_mul, mul_ne_zero_iff] at h
  exact local_middle_of_coprime i j k ℓ θ hθ hinnerL hinnerR hji hik (hbranch θ h.1) (hleft θ h.2)

end Catenary.Middle
