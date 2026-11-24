import Chain.Dynamics
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fin.Rev

noncomputable section
open scoped Matrix BigOperators
namespace Catenary.Reflection

/-- Reverse the 2m transport rates; the last (leak) coordinate stays fixed. -/
def param {m : ℕ} (p : Fin (2*m+1)) : Fin (2*m+1) :=
  if h : p.val < 2*m then ⟨2*m-1-p.val,by omega⟩ else p

def rates {m} (θ : Params m) : Params m := fun p => θ (param p)

@[simp] theorem param_twice {m : ℕ} (p : Fin (2*m+1)) : param (param p) = p := by
  by_cases h : p.val < 2*m
  · have h' : 2*m-1-p.val < 2*m := by omega
    apply Fin.ext
    simp [param,h,h']
    omega
  · simp [param,h]

@[simp] theorem rates_twice {m} (θ : Params m) : rates (rates θ) = θ := by
  funext p; simp [rates]

@[simp] theorem param_fwd {m} (r : Fin m) : param (fwd r) = back r.rev := by
  have hr := r.isLt
  have ht : r.val < 2*m := by omega
  apply Fin.ext
  simp [param,fwd,back,ht,Fin.rev]
  omega

@[simp] theorem param_back {m} (r : Fin m) : param (back r) = fwd r.rev := by
  have hr := r.isLt
  have ht : m+r.val < 2*m := by omega
  apply Fin.ext
  simp [param,fwd,back,ht,Fin.rev]
  omega

@[simp] theorem param_loss (m) : param (loss m) = loss m := by simp [loss,param]

theorem generator_reflect {m} (ℓ : Chamber m) (θ : Params m) :
    generator ℓ.rev (rates θ) =
    (generator ℓ θ).submatrix Fin.revPerm Fin.revPerm := by
  ext row col
  change _ = generator ℓ θ row.rev col.rev
  have er (a b : Chamber m) :
      directedEdge a b row col = directedEdge a.rev b.rev row.rev col.rev := by
    simp only [directedEdge, Fin.rev_inj]
  let f (r : Fin m) :=
    θ (fwd r) * directedEdge r.castSucc r.succ row.rev col.rev +
    θ (back r) * directedEdge r.succ r.castSucc row.rev col.rev
  have hs (r : Fin m) :
    rates θ (fwd r) * directedEdge r.castSucc r.succ row col +
    rates θ (back r) * directedEdge r.succ r.castSucc row col = f r.rev := by
    rw [er r.castSucc r.succ, er r.succ r.castSucc]
    simp [rates,f,Fin.rev_succ,Fin.rev_castSucc,add_comm]
  have sumEq : (∑ r : Fin m, f r.rev) = ∑ r : Fin m, f r := Equiv.sum_comp Fin.revPerm f
  simp only [generator,hs]
  rw [sumEq]
  simp only [rates,param_loss,Fin.rev_eq_iff,f]

theorem markov_reflect {m} (ℓ i v : Chamber m) (θ : Params m) (q : ℕ) :
    (generator ℓ.rev (rates θ)^q) v.rev i.rev = (generator ℓ θ ^ q) v i := by
  rw [generator_reflect]
  have h : ((generator ℓ θ).submatrix Fin.revPerm Fin.revPerm)^q =
      (generator ℓ θ ^ q).submatrix Fin.revPerm Fin.revPerm := by
    induction q with
    | zero => simp [Matrix.submatrix_one_equiv]
    | succ q ih => rw [pow_succ,ih,pow_succ,Matrix.submatrix_mul_equiv]
  rw [h]
  simp [Matrix.submatrix,Fin.revPerm]

theorem curves_reflect {m} (i j k ℓ : Chamber m) (θ η : Params m) :
    SameCurves i.rev k.rev j.rev ℓ.rev (rates θ) (rates η) ↔ SameCurves i j k ℓ θ η := by
  rw [sameCurves_iff_markov,sameCurves_iff_markov]
  simp only [markov_reflect,and_comm]

private theorem dist_lt {m} (θ η : Params m) {ε : ℝ} (he : 0 < ε) (h : dist θ η < ε) :
    dist (rates θ) (rates η) < ε := by
  apply (dist_pi_lt_iff he).2
  intro p
  exact (dist_pi_lt_iff he).1 h (param p)

private theorem reflect_one_way {m} (i j k ℓ : Chamber m) :
    GenericLocalID i j k ℓ → GenericLocalID i.rev k.rev j.rev ℓ.rev := by
  rintro ⟨p,⟨x,hx,hpx⟩,h⟩
  have ev (y : Params m) : MvPolynomial.eval y (MvPolynomial.rename param p) =
      MvPolynomial.eval (rates y) p := by
    rw [MvPolynomial.eval_rename]
    rfl
  refine ⟨MvPolynomial.rename param p,⟨rates x,fun t => hx (param t),?_⟩,?_⟩
  · simpa [ev] using hpx
  intro θ hp ht
  obtain ⟨ε,he,hclose⟩ := h (rates θ) (fun t => hp (param t)) (by simpa [ev] using ht)
  refine ⟨ε,he,?_⟩
  intro η hη hd hc
  have hcurves : SameCurves i j k ℓ (rates θ) (rates η) := by
    apply (curves_reflect i j k ℓ (rates θ) (rates η)).mp
    simpa only [rates_twice] using hc
  have hres := hclose (rates η) (fun t => hη (param t)) (dist_lt η θ he hd) hcurves
  simpa only [rates_twice] using congrArg rates hres

/-- Reflection of the physical experiment, including both curves, leak index,
positive domain, the local neighborhood and the exceptional polynomial. -/
theorem generic_reflect {m} (i j k ℓ : Chamber m) :
    GenericLocalID i.rev k.rev j.rev ℓ.rev ↔ GenericLocalID i j k ℓ := by
  constructor
  · simpa only [Fin.rev_rev] using reflect_one_way i.rev k.rev j.rev ℓ.rev
  · exact reflect_one_way i j k ℓ

end Catenary.Reflection
