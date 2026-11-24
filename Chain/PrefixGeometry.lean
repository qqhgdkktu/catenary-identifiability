import Chain.PrefixNodes
import Chain.PrefixExtension
import Chain.SignedWitness
import Chain.JacobiSamples
import Chain.PrefixPhysical

/-! # Физическая реализация присоединённого префикса при нулевой утечке -/

noncomputable section
open Polynomial
open Catenary.Continuant
open scoped Polynomial
namespace Catenary.PrefixGeometry

abbrev lead (f : ℕ → PathSite ℝ) (q : ℕ) := intervalCharpoly (sitesFrom f 0 q)

/-- Любая реальная дискретная матрица Якоби с ненулевыми β, нулевым det(-J)
    и ненулевыми собственными ведущими минорами реализуется как знакопеременная
    физическая цепь без утечки. Место разрешённой утечки произвольно. -/
theorem realize (m : ℕ) (ℓ : Chamber m) (f : ℕ → PathSite ℝ)
    (hfull : (lead f (m+1)).eval 0 = 0)
    (hproper : ∀ q, q ≤ m → (lead f q).eval 0 ≠ 0)
    (hβ : ∀ r : Fin m, (f r.val).weight ≠ 0) :
    ∃ x : Params m, x (loss m) = 0 ∧
      (∀ c : Chamber m, (physicalSite ℓ x c.val).diag = (f c.val).diag) ∧
      (∀ r : Fin m, (physicalSite ℓ x r.val).weight = (f r.val).weight) ∧
      ∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0 := by
  let L (q : ℕ) := (lead f q).eval 0
  let β (r : Fin m) := (f r.val).weight
  let x := Closed.signedRates L β
  have he := Closed.signed_edges L β hproper hβ
  refine ⟨x, Closed.signed_loss _ _, ?_, ?_, fun r => ⟨(he r).1, (he r).2.1⟩⟩
  · intro c
    have hdiag := Closed.signed_diagonal ℓ L (fun i => -(f i).diag) β
    have h0 : L 0 = 1 := by simp [L, lead, sitesFrom, intervalCharpoly, charpoly_eq_cont]
    have h1 : L 1 = -(f 0).diag := by
      simp [L, lead, sitesFrom, intervalCharpoly, charpoly_eq_cont, pencilSite]
    have hs (r : Fin m) : L (r.val+2) = -(f (r.val+1)).diag * L (r.val+1) - β r * L r.val := by
      simpa only [L, lead, β, eval_sub, eval_mul, eval_X, eval_C, zero_sub] using
        congrArg (Polynomial.eval 0) (Closed.prefix_recurrence f r.val)
    simpa only [physicalSite, c.isLt, dite_true, neg_neg, x] using
      hdiag h0 h1 hfull hproper hs c
  · intro r
    simpa only [physicalSite, r.isLt, dite_true, PathSite.weight, mul_comm, x, β] using (he r).2.2

theorem leading_match {m : ℕ} (f g : ℕ → PathSite ℝ)
    (hd : ∀ c : Chamber m, (f c.val).diag = (g c.val).diag)
    (hw : ∀ r : Fin m, (f r.val).weight = (g r.val).weight) (q : ℕ) (hq : q ≤ m+1) :
    lead f q = lead g q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    match q with
    | 0 => rfl
    | 1 =>
      simp only [lead, sitesFrom, intervalCharpoly, charpoly_eq_cont, List.map_cons, List.map_nil,
        cont_singleton, pencilSite]
      rw [hd ⟨0, by omega⟩]
    | q+2 =>
      have e₁ : intervalCharpoly (sitesFrom f 0 (q+1)) = intervalCharpoly (sitesFrom g 0 (q+1)) :=
        ih (q+1) (by omega) (by omega)
      have e₀ : intervalCharpoly (sitesFrom f 0 q) = intervalCharpoly (sitesFrom g 0 q) :=
        ih q (by omega) (by omega)
      rw [lead, lead, Closed.prefix_recurrence f, Closed.prefix_recurrence g, hd ⟨q+1, by omega⟩,
        hw ⟨q, by omega⟩, e₁, e₀]

def seed (start u : ℕ) := Spectral.site (start+u)

theorem seed_sites (start u q : ℕ) :
    sitesFrom (seed start) u q = (List.range' (start+u) q).map Spectral.site := by
  induction q generalizing u with
  | zero => rfl
  | succ q ih => simp [sitesFrom, seed, List.range'_succ, ih, Nat.add_assoc]

theorem seed_lead (start q : ℕ) :
    lead (seed start) q = Spectral.block (List.range' start q) := by
  simp only [lead, seed_sites, Nat.add_zero, Spectral.block]

abbrev initial (start p : ℕ) := sitesFrom (seed start) 0 p

def correction (start p : ℕ) (β : ℝ) :=
  PrefixExtension.compensation (initial start p) (seed start p) β

theorem correction_eq (start p : ℕ) (β : ℝ) :
    correction start p β = β * (Spectral.block (List.range' start p)).eval 0 /
      (Spectral.block (List.range' start (p+1))).eval 0 := by
  have h := Closed.sites_snoc (seed start) 0 p
  simp only [Nat.zero_add] at h
  simp only [correction, PrefixExtension.compensation, initial, ← h, ← seed_lead, lead]

/-- В префиксе p+1 вершин. Связующее ребро находится на позиции p и
    первый диагональный элемент хвоста получает вычитаемую поправку. -/
def glue (start p : ℕ) (tail : ℕ → PathSite ℝ) (β : ℝ) (u : ℕ) : PathSite ℝ :=
  if u < p then seed start u else
  if u = p then PrefixExtension.linkSite (seed start p) β else
  if u = p+1 then PrefixExtension.shiftDiagonal (tail 0) (correction start p β) else
    tail (u-(p+1))

private theorem from_congr {R : Type*} {f g : ℕ → PathSite R} (u q : ℕ)
    (h : ∀ a, u ≤ a → a < u+q → f a = g a) : sitesFrom f u q = sitesFrom g u q := by
  induction q generalizing u with
  | zero => rfl
  | succ q ih =>
    simp only [sitesFrom]
    rw [h u le_rfl (by omega), ih (u+1) (fun a ha hb => h a (by omega) (by omega))]

private theorem from_offset {R : Type*} (f : ℕ → PathSite R) (offset u q : ℕ) :
    sitesFrom (fun a => f (offset+a)) u q = sitesFrom f (offset+u) q := by
  induction q generalizing u with
  | zero => rfl
  | succ q ih => simp only [sitesFrom, ih, Nat.add_assoc]

private theorem short_prefix (start p : ℕ) (tail : ℕ → PathSite ℝ) (β : ℝ) (q : ℕ) (hq : q ≤ p) :
    sitesFrom (glue start p tail β) 0 q = initial start q := by
  apply from_congr
  intro a _ ha
  simp [glue, show a < p by omega]

theorem lead_prefix (start p : ℕ) (tail : ℕ → PathSite ℝ) (β : ℝ) :
    lead (glue start p tail β) (p+1) = Spectral.block (List.range' start (p+1)) := by
  rw [← seed_lead, lead, lead, Closed.sites_snoc, Closed.sites_snoc]
  simp only [Nat.zero_add, short_prefix _ _ _ _ _ le_rfl, glue, lt_irrefl, if_false, if_true]
  exact PrefixExtension.same_last _ _ _

theorem lead_before (start p : ℕ) (tail : ℕ → PathSite ℝ) (β : ℝ) (q : ℕ) (hq : q ≤ p) :
    lead (glue start p tail β) q = Spectral.block (List.range' start q) := by
  rw [← seed_lead, lead, short_prefix _ _ _ _ _ hq]

theorem split_sites (start p : ℕ) (tail : ℕ → PathSite ℝ) (β : ℝ) (q : ℕ) :
    sitesFrom (glue start p tail β) 0 ((p+1)+(q+1)) =
      initial start p ++ PrefixExtension.linkSite (seed start p) β ::
      PrefixExtension.shiftDiagonal (tail 0) (correction start p β) :: sitesFrom tail 1 q := by
  let f := glue start p tail β
  have ht : sitesFrom f (p+1+1) q = sitesFrom tail 1 q := by
    rw [← from_offset f (p+1) 1]
    apply from_congr
    intro a ha _
    simp [f, glue, show a ≠ 0 by omega, show ¬p+1+a<p by omega, show p+1+a≠p by omega,
      show p+1+a≠p+1 by omega]
  change sitesFrom (glue start p tail β) (p+1+1) q = _ at ht
  rw [Middle.from_append _ 0 (p+1) (q+1), Closed.sites_snoc, Nat.zero_add, Nat.zero_add,
    short_prefix _ _ _ _ _ le_rfl]
  simp only [sitesFrom, List.append_assoc, List.cons_append, List.nil_append, ht,
    glue, lt_irrefl, if_false, if_true, Nat.not_lt_of_ge (Nat.le_succ p), Nat.succ_ne_self]

theorem long_leading (start p : ℕ) (tail : ℕ → PathSite ℝ) (β : ℝ)
    (hS : (Spectral.block (List.range' start (p+1))).eval 0 ≠ 0) (q : ℕ) :
    (lead (glue start p tail β) ((p+1)+(q+1))).eval 0 =
      (Spectral.block (List.range' start (p+1))).eval 0 * (lead tail (q+1)).eval 0 := by
  have split : initial start p ++ [seed start p] = initial start (p+1) := by
    simpa [initial] using (Closed.sites_snoc (seed start) 0 p).symm
  have he : intervalCharpoly (initial start p ++ [seed start p]) =
      Spectral.block (List.range' start (p+1)) := split ▸ seed_lead start (p+1)
  rw [lead, split_sites]
  simpa only [he, correction, lead, sitesFrom] using
    PrefixExtension.signed_splice_at_zero (initial start p) (sitesFrom tail 1 q)
      (seed start p) (tail 0) β (by simpa only [he] using hS)

theorem seed_positive {start : ℕ} (hs : 0 < start) (q : ℕ) :
    0 < (Spectral.block (List.range' start q)).eval 0 := by
  apply Spectral.positive_on_ray _ le_rfl
  exact fun u hu => hs.trans_le (List.left_le_of_mem_range' hu)

/-- Склейка с произвольным хвостом. Для любого ненулевого соединительного
    β все собственные ведущие миноры и физические прямые и обратные скорости ненулевые.
    Перечень совпадений фиксирует каждую диагональ и каждое настоящее ребро. -/
theorem glue_realization {m : ℕ} (ℓ : Chamber m) (p n : ℕ) (hm : p+1+n=m)
    (start : ℕ) (hs : 0 < start) (tail : ℕ → PathSite ℝ) (β : ℝ) (hb : β ≠ 0)
    (hfull : (lead tail (n+1)).eval 0 = 0)
    (hproper : ∀ q, q ≤ n → (lead tail q).eval 0 ≠ 0)
    (hw : ∀ e : Fin n, (tail e.val).weight ≠ 0) :
    ∃ x : Params m, x (loss m) = 0 ∧
      (∀ c : Chamber m, (physicalSite ℓ x c.val).diag = (glue start p tail β c.val).diag) ∧
      (∀ r : Fin m, (physicalSite ℓ x r.val).weight = (glue start p tail β r.val).weight) ∧
      ∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0 := by
  have hS := (seed_positive hs (p+1)).ne'
  apply realize
  · rw [show m+1 = (p+1)+(n+1) by omega, long_leading _ _ _ _ hS n, hfull, mul_zero]
  · intro q hq
    by_cases h₁ : q ≤ p
    · rw [lead_before _ _ _ _ _ h₁]
      exact (seed_positive hs q).ne'
    by_cases h₂ : q = p+1
    · rw [h₂, lead_prefix]
      exact hS
    let a := q-(p+2)
    have e : q = (p+1)+(a+1) := by dsimp [a]; omega
    rw [e, long_leading _ _ _ _ hS a]
    exact mul_ne_zero hS (hproper _ (by omega))
  · intro r
    by_cases hr : r.val < p
    · simp [glue, hr, seed, Spectral.site, PathSite.weight]
    by_cases he : r.val = p
    · simp [glue, hr, he, PrefixExtension.linkSite, PathSite.weight, hb]
    have hlen := r.isLt
    have hpos := hw ⟨r.val-(p+1), by omega⟩
    by_cases h₀ : r.val = p+1
    · simpa [glue, h₀, PrefixExtension.shiftDiagonal, PathSite.weight] using hpos
    · simpa [glue, hr, he, h₀] using hpos

abbrev S (start p : ℕ) := Spectral.block (List.range' start (p+1))
abbrev T (start p : ℕ) := Spectral.block (List.range' start p)

/-- Корректируется единственная диагональ хвоста. При β=0 эта точка —
    исходные координаты `JacobiSamples.base n z`. -/
def tailShift (n start p : ℕ) : JacobiSamples.Coords n :=
  (fun c => if c = 0 then -((T start p).eval 0 / (S start p).eval 0) else 0, 0)

theorem tail_base_full (n : ℕ) (z : ℝ)
    (hz : (Spectral.block (List.range' 1 (n+1))).eval z = 0) :
    (lead (JacobiSamples.site (JacobiSamples.base n z)) (n+1)).eval 0 = 0 ∧
    (∀ q, q ≤ n → (lead (JacobiSamples.site (JacobiSamples.base n z)) q).eval 0 ≠ 0) ∧
    ∀ e : Fin n, (JacobiSamples.site (JacobiSamples.base n z) e.val).weight ≠ 0 := by
  constructor
  · exact (JacobiSamples.base_prefix (m:=n) z _ le_rfl).trans hz
  constructor
  · intro q hq
    exact (JacobiSamples.base_prefix (m:=n) z q (by omega)).trans_ne (Closed.prefix_nonzero z hz q hq)
  · intro e
    simp [JacobiSamples.site, JacobiSamples.base, PathSite.weight, e.isLt]

/-- Тот же β, который выбран по непрерывности якобиана в §7, реализуется
    физическими направленными скоростями. Узлы произвольны и могут быть
    выбранными по `PrefixNodes.choose`; m=p+1+n без ограничений на положение утечки. -/
theorem physical_chart {m : ℕ} (ℓ : Chamber m) (p n : ℕ) (hm : p+1+n=m)
    (start : ℕ) (hs : 0 < start) (nodes : Fin (p+1) → ℝ)
    (z β : ℝ) (hz : (Spectral.block (List.range' 1 (n+1))).eval z = 0) (hb : 0 < β) :
    ∃ x : Params m, x (loss m) = 0 ∧ (∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0) ∧
      PrefixPhysical.coordinates ℓ p n nodes (S start p) x =
        (0, (fun a => β * (T start p).eval (nodes a)),
          JacobiSamples.base n z + β • tailShift n start p) := by
  let tail := JacobiSamples.site (JacobiSamples.base n z)
  let f := glue start p tail β
  obtain ⟨hz₁, hz₂, hz₃⟩ := tail_base_full n z hz
  obtain ⟨x, hx, hd, hw, he⟩ := glue_realization ℓ p n hm start hs tail β hb.ne' hz₁ hz₂ hz₃
  refine ⟨x, hx, he, ?_⟩
  have hS : PrefixPhysical.leading (physicalSite ℓ x) (p+1) = S start p :=
    (leading_match (physicalSite ℓ x) f hd hw _ (by omega)).trans (lead_prefix _ _ _ _)
  have hT : PrefixPhysical.leading (physicalSite ℓ x) p = T start p :=
    (leading_match (physicalSite ℓ x) f hd hw _ (by omega)).trans (lead_before _ _ _ _ _ le_rfl)
  have hbr : (physicalSite ℓ x p).weight = β := by
    simpa [glue, PrefixExtension.linkSite, PathSite.weight] using hw ⟨p, by omega⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext a
    change (PrefixPhysical.leading (physicalSite ℓ x) (p+1) - S start p).eval (nodes a) = 0
    rw [hS, sub_self, eval_zero]
  · funext a
    change (C (physicalSite ℓ x p).weight * PrefixPhysical.leading (physicalSite ℓ x) p).eval
      (nodes a) = _
    rw [hbr, hT, eval_mul, eval_C]
  · apply Prod.ext
    · funext c
      change (physicalSite ℓ x (p+1+c.val)).diag =
        (JacobiSamples.base n z).1 c + β * (tailShift n start p).1 c
      rw [hd ⟨p+1+c.val, by have := c.isLt; omega⟩]
      by_cases hc : c = 0
      · subst c
        simp [glue, tail, tailShift, correction_eq, JacobiSamples.site, JacobiSamples.base,
          PrefixExtension.shiftDiagonal, S, T, div_eq_mul_inv]
        ring
      · have hn : c.val ≠ 0 := fun h => hc (Fin.ext h)
        simp [glue, tail, tailShift, JacobiSamples.site, JacobiSamples.base, hc, hn,
          show ¬p+1+c.val<p by omega, show p+1+c.val≠p by omega, c.isLt]
    · funext r
      change (physicalSite ℓ x (p+1+r.val)).weight =
        (JacobiSamples.base n z).2 r + β * (tailShift n start p).2 r
      rw [hw ⟨p+1+r.val, by have := r.isLt; omega⟩]
      by_cases hr : r.val = 0 <;>
        simp [glue, tail, tailShift, JacobiSamples.site, JacobiSamples.base,
          PrefixExtension.shiftDiagonal, PathSite.weight, hr,
          show ¬p+1+r.val<p by omega, show p+1+r.val≠p by omega, r.isLt]

/-- Совместный выбор префикса и его узлов до выбора веса соединения и
    положения разрешённой утечки. Все узлы избегают корней указанного R. -/
theorem choose_physical_chart {m : ℕ} (p n : ℕ) (hm : p+1+n=m) (R : ℝ[X]) (hR : R ≠ 0)
    (z : ℝ) (hz : (Spectral.block (List.range' 1 (n+1))).eval z = 0) :
    ∃ start : ℕ, 0 < start ∧ ∃ nodes : Fin (p+1) → ℝ, Function.Injective nodes ∧
      (∀ a, (S start p).eval (nodes a) = 0) ∧ (∀ a, R.eval (nodes a) ≠ 0) ∧
      ∀ (β : ℝ), 0 < β → ∀ ℓ : Chamber m,
      ∃ x : Params m, x (loss m) = 0 ∧ (∀ r : Fin m, x (fwd r) ≠ 0 ∧ x (back r) ≠ 0) ∧
        PrefixPhysical.coordinates ℓ p n nodes (S start p) x =
          (0, (fun a => β * (T start p).eval (nodes a)),
            JacobiSamples.base n z + β • tailShift n start p) := by
  obtain ⟨start, hs, nodes, hdist, hnodes, hregular, _⟩ := PrefixNodes.choose (p+1) R hR
  exact ⟨start, hs, nodes, hdist, hnodes, hregular, fun β hβ ℓ =>
    physical_chart ℓ p n hm start hs nodes z β hz hβ⟩

end Catenary.PrefixGeometry
