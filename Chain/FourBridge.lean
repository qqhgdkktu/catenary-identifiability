import Chain.Dynamics
import Chain.FourPencil

/-! From measured amount curves to the exact 7 observations.
The proof uses only the early Markov parameters of the physical generator. -/
noncomputable section
open scoped Matrix BigOperators
namespace Catenary
namespace FourBridge

private def next (ℓ : Fin 4) (θ : Params 3) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let d := Four.diagonal ℓ θ
  ![-(d 0)*v 0 + θ 3*v 1, θ 0*v 0 - d 1*v 1 + θ 4*v 2,
    θ 1*v 1 - d 2*v 2 + θ 5*v 3, θ 2*v 2 - d 3*v 3]

private def state (ℓ : Fin 4) (θ : Params 3) (q : ℕ) : Fin 4 → ℝ :=
  fun v => (generator ℓ θ ^ q) v 0

private theorem next_eq (ℓ : Fin 4) (θ : Params 3) (v : Fin 4 → ℝ) :
    (generator ℓ θ).mulVec v = next ℓ θ v := by
  have h : generator ℓ θ = -(Four.pencil ℓ θ 0) := by
    rw [Four.pencil_eq_generator]
    simp
  rw [h]
  funext r
  change (∑ x : Fin 4, (-(Four.pencil ℓ θ 0)) r x * v x) = next ℓ θ v r
  rw [Fin.sum_univ_four]
  fin_cases r <;>
    simp [Four.pencil, next,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_three, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem state_zero (ℓ : Fin 4) (θ : Params 3) :
    state ℓ θ 0 = ![1,0,0,0] := by
  funext v
  fin_cases v <;> simp [state, Matrix.one_apply]

private theorem state_next (ℓ : Fin 4) (θ : Params 3) (q : ℕ) :
    state ℓ θ (q+1) = next ℓ θ (state ℓ θ q) := by
  rw [← next_eq]
  funext v
  simp [state, pow_succ', Matrix.mul_apply, Matrix.mulVec, dotProduct]

private theorem initial (ℓ : Fin 4) (θ : Params 3) :
    state ℓ θ 0 3 = 0 ∧ state ℓ θ 1 3 = 0 ∧ state ℓ θ 2 3 = 0 ∧
    state ℓ θ 3 3 = θ 0 * θ 1 * θ 2 ∧ state ℓ θ 2 2 = θ 0 * θ 1 ∧
    state ℓ θ 3 2 + Four.coefficients ℓ θ 0 * (θ 0 * θ 1) =
      θ 0 * θ 1 * Four.diagonal ℓ θ 3 := by
  have s1 : state ℓ θ 1 = _ := state_next ℓ θ 0
  have s2 : state ℓ θ 2 = _ := state_next ℓ θ 1
  have s3 : state ℓ θ 3 = _ := state_next ℓ θ 2
  simp only [s3, s2, s1, state_zero]
  dsimp [next, Four.coefficients]
  repeat' apply And.intro
  all_goals ring

private theorem recurrence (ℓ : Fin 4) (θ : Params 3) (t : ℕ) :
    state ℓ θ (t+4) 3 + Four.coefficients ℓ θ 0 * state ℓ θ (t+3) 3
    + Four.coefficients ℓ θ 1 * state ℓ θ (t+2) 3
    + Four.coefficients ℓ θ 2 * state ℓ θ (t+1) 3
    + Four.coefficients ℓ θ 3 * state ℓ θ t 3 = 0 := by
  rw [show t+4 = (t+3)+1 from rfl, state_next,
      show t+3 = (t+2)+1 from rfl, state_next,
      show t+2 = (t+1)+1 from rfl, state_next, state_next]
  dsimp [next, Four.coefficients]
  ring

/-- A monic four-step recurrence is determined by a sequence which has its
first nonzero term at index 3. Each application uses the next time point. -/
private theorem unique_coeff (x : ℕ → ℝ) (c d : Fin 4 → ℝ)
    (h0 : x 0 = 0) (h1 : x 1 = 0) (h2 : x 2 = 0) (h3 : x 3 ≠ 0)
    (h : ∀ t : ℕ, (c 0-d 0)*x (t+3) + (c 1-d 1)*x (t+2)
                       + (c 2-d 2)*x (t+1) + (c 3-d 3)*x t = 0) : c = d := by
  have a : c 0-d 0 = 0 := by
    have e := h 0
    norm_num [h0,h1,h2] at e
    exact e.resolve_right h3
  have b : c 1-d 1 = 0 := by
    have e := h 1
    norm_num [a,h1,h2] at e
    exact e.resolve_right h3
  have f : c 2-d 2 = 0 := by
    have e := h 2
    norm_num [a,b,h2] at e
    exact e.resolve_right h3
  have g : c 3-d 3 = 0 := by
    have e := h 3
    simp [a,b,f] at e
    exact e.resolve_right h3
  funext r
  fin_cases r
  · exact sub_eq_zero.mp a
  · exact sub_eq_zero.mp b
  · exact sub_eq_zero.mp f
  · exact sub_eq_zero.mp g

/-- Both outputs recover the actual polynomial observation map F on the
positive domain. In particular, unreduced fractions are never presumed visible. -/
theorem equal_F_of_sameCurves (ℓ : Fin 4) (θ η : Params 3) (hθ : Positive θ)
    (h : SameCurves (m:=3) 0 2 3 ℓ θ η) : Four.F ℓ θ = Four.F ℓ η := by
  obtain ⟨hj,hk⟩ := (sameCurves_iff_markov (m:=3) 0 2 3 ℓ θ η).mp h
  change ∀ t, state ℓ θ t 2 = state ℓ η t 2 at hj
  change ∀ t, state ℓ θ t 3 = state ℓ η t 3 at hk
  obtain ⟨h0,h1,h2,h3,hp,hm⟩ := initial ℓ θ
  obtain ⟨_,_,_,h3',hp',hm'⟩ := initial ℓ η
  have h3nz : state ℓ θ 3 3 ≠ 0 := by
    rw [h3]
    exact ne_of_gt (mul_pos (mul_pos (hθ 0) (hθ 1)) (hθ 2))
  have he : Four.coefficients ℓ θ = Four.coefficients ℓ η := by
    apply unique_coeff (fun t => state ℓ θ t 3) _ _ h0 h1 h2 h3nz
    intro t
    have hh := recurrence ℓ η t
    simp only [← hk] at hh
    linear_combination recurrence ℓ θ t - hh
  have hd (s : ℝ) : Four.characteristic ℓ θ s = Four.characteristic ℓ η s := by
    simp only [Four.characteristic_eq_coefficients, he]
  have he0 := congrFun he (0 : Fin 4)
  have hP : θ 0 * θ 1 = η 0 * η 1 := hp.symm.trans ((hj 2).trans hp')
  have hP3 := h3.symm.trans ((hk 3).trans h3')
  have hPd : θ 0 * θ 1 * Four.diagonal ℓ θ 3 = η 0 * η 1 * Four.diagonal ℓ η 3 := by
    rw [← hm, ← hm', he0, hP, hj]
  rw [Four.F_eq_observations, Four.F_eq_observations]
  funext r
  fin_cases r <;> first | exact hd _ | exact hP | exact hPd | exact hP3

/-- Full physical four-chamber assertion, including the quantifiers over
continuous inputs, all nonnegative times, and a proper algebraic exceptional set. -/
theorem four_genericLocalID (ℓ : Fin 4) : GenericLocalID (m:=3) 0 2 3 ℓ := by
  refine ⟨Four.exceptionPolynomial ℓ, ⟨Four.witness,Four.witness_positive,Four.witness_nonzero ℓ⟩, ?_⟩
  intro θ hθ hx
  obtain ⟨U,hU,hmem,hinj⟩ := Four.locally_injective ℓ θ hx
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU θ hmem
  refine ⟨ε,hε,?_⟩
  intro η _ hdist hs
  exact (hinj hmem (hball hdist) (equal_F_of_sameCurves ℓ θ η hθ hs)).symm

end FourBridge
end Catenary
