import checkpoints.shen_extension.Supplier54
import checkpoints.shen_extension.FragmentBudget
import checkpoints.shen_extension.Close54
import checkpoints.shen_extension.SupplierFat54

/-!
# The supplier laws of order 54 on the whole row `r = q + 3`

`free : QFree D V q`, `6 ≤ q`, every out-degree `r = q + 3`. Assembled from
`Supplier54` (`s5_generic`, `layer_ball`, `zRows`), `ThinSuppliers` and `FragmentBudget`
(`exterior_floor`, `thin_floor`).

* T1 `thin_supplier_row` (generic): a root with layers `(r - 1, r - 1)` has at least `q - 1`
  rows in `zRows D V (layer D V 3 u)` with `|B_3| ≥ 3r + 1`.
* T2 `complete_head_row` (generic): every complete head of a thin root with `|Z| = r` has
  `|B_3| ≥ 3r + 2`.
* T4 (instances `q = 6`): `s5_54` and `l9_54` are the fields `Laws54.s5`, `Laws54.l9`;
  `laws54_of_s2` and `no54_of_s2`: order 54 from the row laws and S2.

* T3 `fat_supplier_row` (generic, under the ancestor hypothesis `(aSet D V u).Nonempty` of
  `SupplierFat54`): a root with layers `(r, r - 1)` has at least two rows in
  `zRows D V (layer D V 3 u)` with `|B_3| ≥ 3r + 1` (`SupplierFat54.two_suppliers`,
  `SupplierFat54.no_return`, `FragmentBudget.exterior_floor`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.SupplierRow
open Finset BRq2 BRq3 ThinSuppliers OneHead
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open Supplier54 (zRows three_layers layer_ball s5_generic no_back_x_g no_back_u_g)

variable {D : CH.Digraph} {V : Finset ℕ} {q u : ℕ}

/-- A label of the `2`-ball is the root, a head or in layer `2`. -/
theorem out_two (hu : u ∈ V) {t : ℕ} (h : t ∈ ball D V u 2) (nu : t ≠ u)
    (nx : t ∉ outN D V u) (ny : t ∉ layer D V 2 u) : False := by
  by_cases b1 : t ∈ ball D V u 1
  · rcases (mem_ball_one hu).mp b1 with e | hx
    · exact nu e
    · exact nx hx
  · exact ny (mem_layer.mpr ⟨h, b1⟩)

/-- **T1 (generic).** -/
theorem thin_supplier_row (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) (hu : u ∈ V) (tight : TightR D V (q + 3) u) :
    q ≤ ((zRows D V (layer D V 3 u)).filter
      (fun s => 3 * (q + 3) + 1 ≤ (ball D V s 3).card)).card + 1 := by
  obtain ⟨noXU, noY, ykeep, cnt, each⟩ := s5_generic free hq reg hu tight (by omega) le_rfl
  have z8 := tight_third free (by omega) reg hu tight (by omega)
  have y8 := tight.1
  have hZ : ∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u := by
    intro z hz t ht
    obtain ⟨tV, zt⟩ := mem_outN.mp ht
    have t4 : t ∈ ball D V u (3 + 1) := ball_step (mem_layer.mp hz).1 tV zt
    have n2 : t ∉ ball D V u 2 := fun h => out_two hu h
      (fun e => noXU 3 (by norm_num) (by norm_num) z hz u (mem_insert_self _ _) (e ▸ zt))
      (fun hx => noXU 3 (by norm_num) (by norm_num) z hz t (mem_insert_of_mem hx) zt)
      (fun hy => noY 3 le_rfl (by norm_num) z hz t hy zt)
    have := three_layers (k := 2) (t := t) (ball_mono_radius (by norm_num) t4) n2
    rcases mem_union.mp this with h | h
    · exact h
    · exact absurd t4 (mem_layer.mp h).2
  have hW : ∀ w ∈ layer D V 4 u,
      outN D V w ⊆ layer D V 3 u ∪ layer D V 4 u ∪ layer D V 5 u := by
    intro w hw t ht
    obtain ⟨tV, wt⟩ := mem_outN.mp ht
    have t5 : t ∈ ball D V u (4 + 1) := ball_step (mem_layer.mp hw).1 tV wt
    have n2 : t ∉ ball D V u 2 := fun h => out_two hu h
      (fun e => noXU 4 (by norm_num) le_rfl w hw u (mem_insert_self _ _) (e ▸ wt))
      (fun hx => noXU 4 (by norm_num) le_rfl w hw t (mem_insert_of_mem hx) wt)
      (fun hy => noY 4 (by norm_num) le_rfl w hw t hy wt)
    exact three_layers (k := 2) (t := t) t5 n2
  have c1 := FragmentBudget.exterior_floor free hq reg (u := u) (by omega) hZ hW
  have sub : good D (layer D V 2 u) ⊆ (zRows D V (layer D V 3 u)).filter
      (fun s => 3 * (q + 3) + 1 ≤ (ball D V s 3).card) := by
    intro s hs
    obtain ⟨full, rest, full'⟩ := each s hs
    have sY := lone_subset (mem_good.mp hs).1
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨layer_subset sY, full, by rw [rest, card_singleton],
      fun e he => by rw [rest, mem_singleton] at he; rw [he]; exact full'⟩, ?_⟩
    have lb := layer_ball free hu (A := layer D V 2 u) (i := 2) (s := s) (k := 3) (by norm_num)
      layer_subset (fun v hv => (mem_layer.mp hv).1) sY (fun v hv => (ykeep v hv).2) full
      (by omega)
    simp only [sum_range_succ, sum_range_zero] at lb
    norm_num at lb
    omega
  have := card_le_card sub
  omega

/-- **T2 (generic).** -/
theorem complete_head_row (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) (hu : u ∈ V) (thin : Thin D V (q + 3) u)
    (hZc : (layer D V 3 u).card = q + 3) {x : ℕ} (hx : x ∈ complete D V u) :
    3 * (q + 3) + 2 ≤ (ball D V x 3).card := by
  have yc := thin
  unfold Thin at yc
  have n1 : ∀ {j v t : ℕ}, 2 ≤ j → j + 2 ≤ q → v ∈ layer D V j u → D v t = true →
      t ∉ ball D V u 1 := by
    intro j v t hj2 hj hv vt h
    rcases (mem_ball_one hu).mp h with e | hx'
    · exact no_back_u_g free hu (by omega) hv (e ▸ vt)
    · exact no_back_x_g free (by omega) reg hu thin (by omega) (by omega) hj2 hj hv hx' vt
  have hY : ∀ y ∈ layer D V 2 u, outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u := by
    intro y hy t ht
    obtain ⟨tV, yt⟩ := mem_outN.mp ht
    have t3 : t ∈ ball D V u (2 + 1) := ball_step (mem_layer.mp hy).1 tV yt
    have := three_layers (k := 1) (t := t) (ball_mono_radius (by norm_num) t3)
      (n1 le_rfl (by omega) hy yt)
    rcases mem_union.mp this with h | h
    · exact h
    · exact absurd t3 (mem_layer.mp h).2
  have hZ : ∀ z ∈ layer D V 3 u,
      outN D V z ⊆ layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u := by
    intro z hz t ht
    obtain ⟨tV, zt⟩ := mem_outN.mp ht
    have t4 : t ∈ ball D V u (3 + 1) := ball_step (mem_layer.mp hz).1 tV zt
    exact three_layers (k := 1) (t := t) t4 (n1 (by norm_num) (by omega) hz zt)
  have c2 := FragmentBudget.thin_floor free hq reg (u := u) (by omega) hZc hY hZ
  have lb := layer_ball free hu (A := outN D V u) (i := 1) (s := x) (k := 3) le_rfl outN_subset
    (fun v hv => (mem_ball_one hu).mpr (Or.inr hv)) (complete_subset hx)
    (x_heads_r free (by omega) reg hu thin) (complete_full free (by omega) reg hu thin hx)
    (by omega)
  simp only [sum_range_succ, sum_range_zero] at lb
  norm_num at lb
  omega

/-- **T3 (generic).** -/
theorem fat_supplier_row (free : QFree D V q) (hq : 6 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 3) (hu : u ∈ V)
    (hY : (layer D V 2 u).card = q + 3) (hZc : (layer D V 3 u).card = q + 2)
    (ne : (SupplierFat54.aSet D V u).Nonempty) :
    2 ≤ ((zRows D V (layer D V 3 u)).filter
      (fun s => 3 * (q + 3) + 1 ≤ (ball D V s 3).card)).card := by
  have nr : ∀ {j t v : ℕ}, 3 ≤ j → j ≤ 4 → t ∈ layer D V j u → D t v = true →
      v ∉ ball D V u 2 := by
    intro j t v hj3 hj4 ht tv h
    exact out_two hu h
      (fun e => SupplierFat54.no_return free hu hq reg hY hZc ne hj3 hj4 ht (Or.inl e) tv)
      (fun hx => SupplierFat54.no_return free hu hq reg hY hZc ne hj3 hj4 ht (Or.inr (Or.inl hx)) tv)
      (fun hy => SupplierFat54.no_return free hu hq reg hY hZc ne hj3 hj4 ht (Or.inr (Or.inr hy)) tv)
  have hZ : ∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u := by
    intro z hz t ht
    obtain ⟨tV, zt⟩ := mem_outN.mp ht
    have t4 : t ∈ ball D V u (3 + 1) := ball_step (mem_layer.mp hz).1 tV zt
    have := three_layers (k := 2) (t := t) (ball_mono_radius (by norm_num) t4)
      (nr le_rfl (by norm_num) hz zt)
    rcases mem_union.mp this with h | h
    · exact h
    · exact absurd t4 (mem_layer.mp h).2
  have hW : ∀ w ∈ layer D V 4 u,
      outN D V w ⊆ layer D V 3 u ∪ layer D V 4 u ∪ layer D V 5 u := by
    intro w hw t ht
    obtain ⟨tV, wt⟩ := mem_outN.mp ht
    have t5 : t ∈ ball D V u (4 + 1) := ball_step (mem_layer.mp hw).1 tV wt
    exact three_layers (k := 2) (t := t) t5 (nr (by norm_num) le_rfl hw wt)
  have c1 := FragmentBudget.exterior_floor free hq reg (u := u) hZc hZ hW
  have two := SupplierFat54.two_suppliers free hu hq reg hY hZc ne (b := 3 * (q + 3) + 1)
    (by omega)
  refine two.trans (card_le_card (fun s hs => ?_))
  obtain ⟨sV, hb, a, b, c⟩ := mem_filter.mp hs
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨sV, a, b, c⟩, hb⟩

/-! ### T4: the instances at `q = 6` -/

/-- `Laws54.s5` from T1. -/
theorem s5_54 (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) :
    ∀ u ∈ V, TightR D V 9 u → 5 ≤ (Supplier54.zSet D V (layer D V 3 u)).card := by
  intro u hu tight
  have t1 := thin_supplier_row (q := 6) free le_rfl reg hu tight
  refine le_trans (b := ((zRows D V (layer D V 3 u)).filter
    (fun s => 3 * (6 + 3) + 1 ≤ (ball D V s 3).card)).card) (by omega)
    (card_le_card (fun s hs => ?_))
  obtain ⟨hz, hb⟩ := mem_filter.mp hs
  obtain ⟨sV, a, b, c⟩ := mem_filter.mp hz
  exact mem_filter.mpr ⟨sV, by omega, a, b, c⟩

/-- `Laws54.l9` from T2. -/
theorem l9_54 (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) :
    ∀ u ∈ V, Thin D V 9 u → (ball D V u 3).card = 27 → ∀ x ∈ complete D V u,
      29 ≤ (ball D V x 3).card := by
  intro u hu thin b3 x hx
  have L := (balls_by_layers free (by norm_num) reg hu).2.2
  have yc := thin
  unfold Thin at yc
  have := complete_head_row (q := 6) free le_rfl reg hu thin (by omega) hx
  omega

/-- The laws of `Close54` from the row laws and S2. -/
theorem laws54_of_s2 (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (s2 : ∀ u ∈ V, ¬ Thin D V 9 u → (layer D V 2 u).card = 9 → (layer D V 3 u).card = 8 →
      2 ≤ (Supplier54.zSet D V (layer D V 3 u)).card) : Close54.Laws54 D V :=
  ⟨s5_54 free reg, s2, l9_54 free reg⟩

/-- **Order 54 from the row laws and S2.** -/
theorem no54_of_s2 (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 54)
    (s2 : ∀ u ∈ V, ¬ Thin D V 9 u → (layer D V 2 u).card = 9 → (layer D V 3 u).card = 8 →
      2 ≤ (Supplier54.zSet D V (layer D V 3 u)).card) : False :=
  Close54.no54_of_laws free reg n (laws54_of_s2 free reg s2)

#print axioms out_two
#print axioms thin_supplier_row
#print axioms complete_head_row
#print axioms fat_supplier_row
#print axioms s5_54
#print axioms l9_54
#print axioms laws54_of_s2
#print axioms no54_of_s2

end LeanCH.BR.SupplierRow
