import Chain.JacobiSamples
import Chain.PrefixExtension
import Chain.PrefixNodes

/-! Concrete finite samples and coupling line for an interior inlet with
both sensors to its right. The prefix has p+1 vertices, the tail n edges. -/

noncomputable section
open Polynomial Catenary.Continuant
open scoped Polynomial
namespace Catenary.PrefixInstantiation
open JacobiSamples

def grid (n : ℕ) (a : Fin (n+2)) : ℝ := a.val

theorem grid_injective (n : ℕ) : Function.Injective (grid n) := by
  intro a b h
  apply Fin.ext
  change (a.val : ℝ) = (b.val : ℝ) at h
  exact_mod_cast h

def rows (n : ℕ) : Row n → ℝ := Sum.elim (grid n) (fun _ => 0)

def rowLen {n} (j k : Chamber n) : Row n → ℕ :=
  Sum.elim (fun _ => n+1) (fun b => if b then k.val else j.val)

def tailPoly {n} (x : Coords n) (u q : ℕ) : ℝ[X] :=
  intervalCharpoly (sitesFrom (site x) u q)

def chart {n p} (j k : Chamber n) (nodes : Fin (p+1) → ℝ) (S : ℝ[X]) :=
  PrefixExtension.sampleChart (fun a => PrefixExtension.interpolateAt nodes (rows n a))
    (fun a => S.eval (rows n a))
    (fun x a => seg x 0 (n+1) (nodes a)) (fun x a => seg x 1 n (nodes a))
    (fun x a => seg x 1 (rowLen j k a - 1) (rows n a)) (data j k (grid n))

theorem chart_exact {n p} (j k : Chamber n) (nodes : Fin (p+1) → ℝ) (hn : Function.Injective nodes)
    (S s v : ℝ[X]) (hz : ∀ a, S.eval (nodes a)=0)
    (hs : (s-S).degree < (p+1:ℕ)) (hv : v.degree < (p+1:ℕ)) (x : Coords n) :
    chart j k nodes S ((fun a => (s-S).eval (nodes a)),(fun a => v.eval (nodes a)),x) =
      ((fun a => s.eval (nodes a)),
       (fun a => (s*tailPoly x 0 (n+1) - v*tailPoly x 1 n).eval (nodes a)),
       (fun a => (s*tailPoly x 0 (rowLen j k a)-v*tailPoly x 1 (rowLen j k a - 1)).eval (rows n a)),
       (data j k (grid n) x).2) := by
  have he (y : Coords n) : (fun a => (tailPoly y 0 (rowLen j k a)).eval (rows n a)) =
      (data j k (grid n) y).1 := by funext a; cases a <;> rfl
  have e := PrefixExtension.sampleChart_exact nodes hn (rows n) S s v hz (by simpa using hs)
    (by simpa using hv) (fun y : Coords n => tailPoly y 0 (n+1)) (fun y => tailPoly y 1 n)
    (fun y a => tailPoly y 0 (rowLen j k a)) (fun y a => tailPoly y 1 (rowLen j k a-1))
    (fun y => (data j k (grid n) y).2) x
  simpa only [he] using e

def leftPoly (start q : ℕ) : ℝ[X] := Spectral.block (List.range' start q)

def shift (n : ℕ) (T S : ℝ[X]) : Coords n :=
  (fun c => if c=0 then -(T.eval 0/S.eval 0) else 0,0)

/-- One set of finite samples gives an actual signed full-rank witness for
the joined system at a strictly positive, arbitrarily small coupling. -/
theorem instantiated_rank {n} (p : ℕ) (j k : Chamber n) (hj : 0<j.val) (hjk : j<k)
    (small : j.val ≤ n-k.val+2) (δ : ℝ) (hδ : 0<δ) :
    ∃ z, (Spectral.block (List.range' 1 (n+1))).eval z=0 ∧
      ∃ start : ℕ, 0<start ∧ ∃ nodes : Fin (p+1) → ℝ, Function.Injective nodes ∧
      (∀ a, (leftPoly start (p+1)).eval (nodes a)=0) ∧
      ∃ β : ℝ, 0<β ∧ β<δ ∧ Function.Injective
        (fderiv ℝ (chart j k nodes (leftPoly start (p+1)))
          (0,(fun a => β*(leftPoly start p).eval (nodes a)),
            base n z+β • shift n (leftPoly start p) (leftPoly start (p+1)))) := by
  obtain ⟨z,hz,hrank⟩ := JacobiSamples.rank j k hj hjk small
  let a := base n z
  let R := tailPoly a 1 n
  have hR : R ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  obtain ⟨start,hstart,nodes,hn,hroots,hr,_⟩ := PrefixNodes.choose (p+1) R hR
  let S := leftPoly start (p+1)
  let T := leftPoly start p
  have spos (c : Row n) : 0 < S.eval (rows n c) := by
    apply Spectral.positive_on_ray
    · intro u hu
      exact hstart.trans_le (List.left_le_of_mem_range' hu)
    · cases c with
      | inl a => exact Nat.cast_nonneg _
      | inr b => exact le_rfl
  have hA : ContDiff ℝ 1 (fun x : Coords n => fun u => seg x 0 (n+1) (nodes u)) :=
    contDiff_pi.mpr fun u => (seg_smooth _ _ _).of_le (by norm_num)
  have hR' : ContDiff ℝ 1 (fun x : Coords n => fun u => seg x 1 n (nodes u)) :=
    contDiff_pi.mpr fun u => (seg_smooth _ _ _).of_le (by norm_num)
  have hQ : ContDiff ℝ 1 (fun x : Coords n => fun u => seg x 1 (rowLen j k u-1) (rows n u)) :=
    contDiff_pi.mpr fun u => (seg_smooth _ _ _).of_le (by norm_num)
  obtain ⟨β,hb,hbδ,hbRank⟩ := PrefixExtension.signed_chart_witness
    (fun u => PrefixExtension.interpolateAt nodes (rows n u)) (fun u => S.eval (rows n u))
    _ _ _ (data j k (grid n)) a (shift n T S) (fun u => T.eval (nodes u))
    hA hR' hQ ((data_smooth _ _ _).of_le (by norm_num)) (fun u => (spos u).ne')
    hr (hrank _ (grid_injective n)) δ hδ
  exact ⟨z,hz,start,hstart,nodes,hn,hroots,β,hb,hbδ,hbRank⟩

end Catenary.PrefixInstantiation
