import checkpoints.shen_extension.TopRow

/-!
# Thin and fat savers in one count

`TopRow.no_short_thin_sharp` pays the short thin rows through their complete heads. Here a second
family of savers `F` (rows that are not thin) is paid at the same time through banks `Bk u`:

* `supplier_score` (generic): a complete head `x` of the thin roots of `R` (pairwise different
  second layers) scores at least
  `|B (i+1) c| + |B (j+1) c| + min (|R| + i - 1) (q + 1) + min (|R| + j - 1) (q + 1) - 2r`.
* `no_short_mixed` (generic): savers are the short thin rows (classes by second layer, banks the
  complete heads) and the rows of `F` (classes by bank, banks `Bk`). Hypotheses: fat banks are
  equal or disjoint (`sep`), same-bank fat rows are gaps (`gapF`), fat bank rows are one above
  the level (`payF`), the thin `bankrow` with one more unit (a complete head may also sit in one fat
  bank), and the class conditions `m (δ + 1) < m² + b`, `m (δF + 1) < m² + b` with `b` at most
  `2q + 2 - r` and at most every fat bank. Conclusion: no saver at all.
* `loop_complete` (generic): the counting half of Law Z (a third layer of `q + 1` labels with no
  return is a single loop complete to the next layer).
* `FatBank`: the fat-bank law as one hypothesis (savers = the rows that are not thin and below
  the level).
* `no62_of_bank`, `no72_of_bank`: at `r = 9`, orders `62` (`q = 7`) and `72` (`q = 8`) follow
  from `FatBank` with banks of at least `7` (resp. `8`) rows and the floors.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.TopRowFat
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ReachLedger (gap mem_gap)
open ThinSuppliers (Thin complete complete_subset x_heads_r complete_count complete_ball
  supplier_gain twins_gap_r)
open TopRow (grow_from)

variable {D : CH.Digraph} {q : ℕ} {V : Finset ℕ}

/-- The score of a complete head serving the thin roots of `R`. -/
theorem supplier_score {r i j : ℕ} (free : QFree D V q) (hq : 3 ≤ q) (hr : r + 1 ≤ 2 * q)
    (reg : ∀ v ∈ V, (outN D V v).card = r) (hi : 2 ≤ i) (hj : 2 ≤ j) (hiq : i ≤ q) (hjq : j ≤ q)
    {R : Finset ℕ} (RV : R ⊆ V) (thin : ∀ w ∈ R, Thin D V r w) {x : ℕ}
    (hx : ∀ w ∈ R, x ∈ complete D V w)
    (inj : ∀ w ∈ R, ∀ w' ∈ R, layer D V 2 w = layer D V 2 w' → w = w') {c : ℕ} (hc : c ∈ R) :
    (ball D V c (i + 1)).card + (ball D V c (j + 1)).card +
        min (R.card + (i - 1)) (q + 1) + min (R.card + (j - 1)) (q + 1) ≤
      (ball D V x i).card + (ball D V x j).card + 2 * r ∧ R.card ≤ r := by
  have cV := RV hc
  have ct := thin c hc
  have xc := hx c hc
  have xX := complete_subset xc
  obtain ⟨b0, hb0⟩ := card_pos.mp (x_heads_r free (by omega) reg cV ct x xX)
  have gain := supplier_gain free hq reg hr RV thin hx inj hc hb0
  have bi := complete_ball free (by omega) reg cV ct xc hb0 (j := i) (by omega) hiq
  have bj := complete_ball free (by omega) reg cV ct xc hb0 (j := j) (by omega) hjq
  have XV : outN D V c ⊆ V := outN_subset
  have b0X := (mem_outN.mp hb0).1
  have gi := grow_from (free.mono_set XV) (by omega) (x_heads_r free (by omega) reg cV ct)
    b0X (i - 1) (by omega)
  have gj := grow_from (free.mono_set XV) (by omega) (x_heads_r free (by omega) reg cV ct)
    b0X (j - 1) (by omega)
  have dle : (outN D (outN D V c) b0).card ≤ r := by
    rw [← reg c cV]
    exact card_le_card outN_subset
  have mi : min (R.card + (i - 1)) (q + 1) ≤
      min ((outN D (outN D V c) b0).card + (i - 1)) (q + 1) := min_le_min_right _ (by omega)
  have mj : min (R.card + (j - 1)) (q + 1) ≤
      min ((outN D (outN D V c) b0).card + (j - 1)) (q + 1) := min_le_min_right _ (by omega)
  exact ⟨by omega, by omega⟩

/-- **Thin and fat savers together.** See the module docstring. -/
theorem no_short_mixed {r i j δ δF b : ℕ} (free : QFree D V q)
    (hq : 3 ≤ q) (hr : r + 1 ≤ 2 * q) (reg : ∀ v ∈ V, (outN D V v).card = r) (hij : i + j ≤ q)
    (hi : 2 ≤ i) (hj : 2 ≤ j)
    {F : Finset ℕ} (FV : F ⊆ V) (Fthin : ∀ u ∈ F, ¬ Thin D V r u)
    {Bk : ℕ → Finset ℕ} (BkV : ∀ u ∈ F, Bk u ⊆ V) (Bkc : ∀ u ∈ F, b ≤ (Bk u).card)
    (hb : b ≤ 2 * q + 2 - r)
    (rest : ∀ v ∈ V, ¬ Thin D V r v → v ∉ F →
      V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card)
    (shortF : ∀ u ∈ F, V.card + 1 ≤ (ball D V u i).card + (ball D V u j).card + δF)
    (short : ∀ v ∈ V, Thin D V r v →
      V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card + δ)
    (bankrow : ∀ v ∈ V, Thin D V r v →
      (ball D V v i).card + (ball D V v j).card < V.card + 1 → ∀ s, 1 ≤ s → s ≤ r →
      V.card + 2 + s + 2 * r ≤ (ball D V v (i + 1)).card + (ball D V v (j + 1)).card +
        min (s + (i - 1)) (q + 1) + min (s + (j - 1)) (q + 1))
    (payF : ∀ u ∈ F, ∀ x ∈ Bk u, V.card + 2 ≤ (ball D V x i).card + (ball D V x j).card)
    (sep : ∀ u ∈ F, ∀ u' ∈ F, Bk u = Bk u' ∨ Disjoint (Bk u) (Bk u'))
    (gapF : ∀ u ∈ F, ∀ u' ∈ F, Bk u = Bk u' → u ≠ u' → u' ∈ gap D V i j u)
    (pay : ∀ m, m * (δ + 1) < m * m + b) (payFm : ∀ m, m * (δF + 1) < m * m + b) :
    F = ∅ ∧ ∀ v ∈ V, Thin D V r v → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card := by
  classical
  set T := V.filter (fun v => Thin D V r v ∧
    (ball D V v i).card + (ball D V v j).card < V.card + 1) with hT
  set S := T ∪ F with hS
  have TV : T ⊆ V := filter_subset _ _
  have ofT : ∀ u ∈ T, u ∈ V ∧ Thin D V r u ∧
      (ball D V u i).card + (ball D V u j).card < V.card + 1 := fun u hu => mem_filter.mp hu
  have TF : ∀ u ∈ T, u ∉ F := fun u hu hF => Fthin u hF (ofT u hu).2.1
  set repT : ℕ → ℕ := fun u => (T.filter (fun w => layer D V 2 w = layer D V 2 u)).sup id
    with hrepT
  set repF : ℕ → ℕ := fun u => (F.filter (fun w => Bk w = Bk u)).sup id with hrepF
  have rT : ∀ u ∈ T, repT u ∈ T ∧ layer D V 2 (repT u) = layer D V 2 u := by
    intro u hu
    obtain ⟨w, hw, he⟩ := exists_mem_eq_sup (T.filter (fun w => layer D V 2 w = layer D V 2 u))
      ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩ id
    have : repT u = w := he
    rw [this]
    exact mem_filter.mp hw
  have rF : ∀ u ∈ F, repF u ∈ F ∧ Bk (repF u) = Bk u := by
    intro u hu
    obtain ⟨w, hw, he⟩ := exists_mem_eq_sup (F.filter (fun w => Bk w = Bk u))
      ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩ id
    have : repF u = w := he
    rw [this]
    exact mem_filter.mp hw
  have congT : ∀ u u', layer D V 2 u = layer D V 2 u' → repT u = repT u' := by
    intro u u' h; simp only [hrepT, h]
  have congF : ∀ u u', Bk u = Bk u' → repF u = repF u' := by
    intro u u' h; simp only [hrepF, h]
  have FT : ∀ u ∈ F, u ∉ T := fun u hu hT => TF u hT hu
  set cls : ℕ → ℕ := fun u => if u ∈ T then repT u else repF u with hcls
  set bank : ℕ → Finset ℕ := fun c => if c ∈ T then complete D V c else Bk c with hbank
  set d : ℕ → ℕ := fun u => if u ∈ T then δ else δF with hd
  have clsT : ∀ u ∈ T, cls u = repT u := fun u hu => if_pos hu
  have clsF : ∀ u ∈ F, cls u = repF u := fun u hu => if_neg (FT u hu)
  have SV : S ⊆ V := union_subset TV FV
  have memS : ∀ u ∈ S, u ∈ T ∨ u ∈ F := fun u hu => mem_union.mp hu
  have bankT : ∀ c ∈ T, bank c = complete D V c := fun c hc => if_pos hc
  have bankF : ∀ c, c ∉ T → bank c = Bk c := fun c hc => if_neg hc
  -- the class of a saver keeps its family
  have fam : ∀ u ∈ S, (cls u ∈ T ↔ u ∈ T) := by
    intro u hu
    rcases memS u hu with h | h
    · rw [clsT u h]; exact ⟨fun _ => h, fun _ => (rT u h).1⟩
    · rw [clsF u h]; exact ⟨fun h' => absurd h' (FT _ (rF u h).1), fun h' => absurd h' (FT u h)⟩
  have empty : S = ∅ := by
    refine BankCount.bank_count_gen (b := b) (π := 1) (d := d) (cls := cls) (bank := bank)
      free hij SV (fun u hu => ?_) (fun u hu => ?_) (fun u hu => ?_) (fun v hv vS => ?_)
      (fun x hx hp => ?_) (fun u hu u' hu' hc ne => ?_) (fun u hu => ?_)
    · -- bankV
      rcases memS u hu with h | h
      · rw [clsT u h, bankT _ (rT u h).1]; exact complete_subset.trans outN_subset
      · rw [clsF u h, bankF _ (FT _ (rF u h).1), (rF u h).2]; exact BkV u h
    · -- bcard
      rcases memS u hu with h | h
      · rw [clsT u h, bankT _ (rT u h).1]
        obtain ⟨wV, wt, -⟩ := ofT _ (rT u h).1
        have := complete_count free (by omega) reg wV wt (by omega)
        omega
      · rw [clsF u h, bankF _ (FT _ (rF u h).1), (rF u h).2]; exact Bkc u h
    · -- short
      rcases memS u hu with h | h
      · have e : d u = δ := if_pos h
        rw [e]; exact short u (TV h) (ofT u h).2.1
      · have e : d u = δF := if_neg (FT u h)
        rw [e]; exact shortF u h
    · -- rest
      by_cases vt : Thin D V r v
      · by_contra low
        exact vS (mem_union_left _ (mem_filter.mpr ⟨hv, vt, by omega⟩))
      · exact rest v hv vt (fun h => vS (mem_union_right _ h))
    · -- pays
      change V.card + 1 + 1 * ((S.image cls).filter (fun c => x ∈ bank c)).card ≤ _
      change 0 < ((S.image cls).filter (fun c => x ∈ bank c)).card at hp
      set I := (S.image cls).filter (fun c => x ∈ bank c) with hI
      set IT := I.filter (fun c => c ∈ T) with hIT
      set IF := I.filter (fun c => c ∉ T) with hIF
      have split : IT.card + IF.card = I.card := card_filter_add_card_filter_not (s := I) (fun c => c ∈ T)
      have ofI : ∀ c ∈ I, ∃ u ∈ S, cls u = c ∧ x ∈ bank c := by
        intro c hc
        obtain ⟨cI, xc⟩ := mem_filter.mp hc
        obtain ⟨u, hu, rfl⟩ := mem_image.mp cI
        exact ⟨u, hu, rfl, xc⟩
      -- fat classes at `x`: at most one
      have oneF : IF.card ≤ 1 := by
        refine card_le_one.mpr (fun c hc c' hc' => ?_)
        obtain ⟨cI, cT⟩ := mem_filter.mp hc
        obtain ⟨cI', cT'⟩ := mem_filter.mp hc'
        obtain ⟨u, hu, rfl, xc⟩ := ofI _ cI
        obtain ⟨u', hu', rfl, xc'⟩ := ofI _ cI'
        have uF : u ∈ F := (memS u hu).resolve_left (fun h => cT ((fam u hu).mpr h))
        have uF' : u' ∈ F := (memS u' hu').resolve_left (fun h => cT' ((fam u' hu').mpr h))
        rw [bankF _ cT, clsF u uF, (rF u uF).2] at xc
        rw [bankF _ cT', clsF u' uF', (rF u' uF').2] at xc'
        rw [clsF u uF, clsF u' uF']
        rcases sep u uF u' uF' with e | dj
        · exact congF u u' e
        · exact absurd xc' (disjoint_left.mp dj xc)
      by_cases tpos : 0 < IT.card
      · -- a complete head of the thin classes in `IT`
        have ITrep : ∀ c ∈ IT, c ∈ T ∧ x ∈ complete D V c := by
          intro c hc
          obtain ⟨cI, cT⟩ := mem_filter.mp hc
          obtain ⟨-, -, -, xc⟩ := ofI _ cI
          rw [bankT _ cT] at xc
          exact ⟨cT, xc⟩
        have ITV : IT ⊆ V := fun c hc => TV (ITrep c hc).1
        have inj : ∀ c ∈ IT, ∀ c' ∈ IT, layer D V 2 c = layer D V 2 c' → c = c' := by
          intro c hc c' hc' e
          obtain ⟨u, hu, hcu, -⟩ := ofI _ (mem_filter.mp hc).1
          obtain ⟨u', hu', hcu', -⟩ := ofI _ (mem_filter.mp hc').1
          have uT : u ∈ T := (fam u hu).mp (hcu ▸ (ITrep c hc).1)
          have uT' : u' ∈ T := (fam u' hu').mp (hcu' ▸ (ITrep c' hc').1)
          rw [← hcu, ← hcu', clsT u uT, clsT u' uT'] at e ⊢
          rw [(rT u uT).2, (rT u' uT').2] at e
          exact congT u u' e
        obtain ⟨c, hc⟩ := card_pos.mp tpos
        obtain ⟨cT, -⟩ := ITrep c hc
        obtain ⟨cV, ct, clow⟩ := ofT c cT
        obtain ⟨sc, sr⟩ := supplier_score free hq hr reg hi hj (by omega) (by omega) ITV
          (fun w hw => (ofT w (ITrep w hw).1).2.1) (fun w hw => (ITrep w hw).2) inj hc
        have := bankrow c cV ct clow IT.card tpos sr
        omega
      · -- only fat classes: exactly one, and its bank rows pay
        have i1 : I.card = 1 := by omega
        obtain ⟨c, hc⟩ : IF.Nonempty := card_pos.mp (by omega)
        obtain ⟨cI, cT⟩ := mem_filter.mp hc
        obtain ⟨u, hu, rfl, xc⟩ := ofI _ cI
        have uF : u ∈ F := (memS u hu).resolve_left (fun h => cT ((fam u hu).mpr h))
        rw [bankF _ cT, clsF u uF, (rF u uF).2] at xc
        have := payF u uF x xc
        rw [i1]
        omega
    · -- gaps
      rcases memS u hu with h | h
      · have uT' : u' ∈ T := (fam u' hu').mp (hc ▸ (fam u hu).mpr h)
        have same : layer D V 2 u = layer D V 2 u' := by
          rw [← (rT u h).2, ← (rT u' uT').2, ← clsT u h, ← clsT u' uT', hc]
        exact twins_gap_r free (by omega) reg (SV hu) (SV hu') (Ne.symm ne) same
          (by omega) (by omega)
      · have uT : u ∉ T := FT u h
        have uF' : u' ∈ F := (memS u' hu').resolve_left (fun h' =>
          uT ((fam u hu).mp (hc ▸ (fam u' hu').mpr h')))
        have same : Bk u = Bk u' := by
          rw [← (rF u h).2, ← (rF u' uF').2, ← clsF u h, ← clsF u' uF', hc]
        exact gapF u h u' uF' same (Ne.symm ne)
    · -- classpay
      have each : ∀ w ∈ BankCount.fiber S cls (cls u), d w = d u := by
        intro w hw
        obtain ⟨wS, wc⟩ := mem_filter.mp hw
        have : (w ∈ T ↔ u ∈ T) := by rw [← fam w wS, ← fam u hu, wc]
        simp only [hd, this]
      rw [sum_congr rfl each, sum_const, smul_eq_mul, mul_one]
      rcases memS u hu with h | h
      · have e : d u = δ := if_pos h
        have := pay (BankCount.fiber S cls (cls u)).card
        rw [e]
        nlinarith
      · have e : d u = δF := if_neg (FT u h)
        have := payFm (BankCount.fiber S cls (cls u)).card
        rw [e]
        nlinarith
  refine ⟨?_, fun v hv vt => ?_⟩
  · exact subset_empty.mp (empty ▸ subset_union_right)
  · by_contra low
    have : v ∈ S := mem_union_left _ (mem_filter.mpr ⟨hv, vt, by omega⟩)
    rw [empty] at this
    simp at this

/-! ### Law Z from no return -/

/-- **Law Z, the counting half** (generic). A set `Z` of `q + 1` labels whose rows have out-degree
`r` and keep all their heads in `Z ∪ W`, `|W| + 1 ≤ r`, `Z ∩ W = ∅`: `Z` is a single loop (one
head in `Z` per row) and every row of `Z` heads all of `W`, which has exactly `r - 1` labels.
SAT (scratch `l4.py`, prop `zret`): at a root with layer widths `(r, r, q + 1, q + 1)`, `r = q + 2`,
no row of the third layer heads the first or second layer — UNSAT at `q = 4` (142 s) and `q = 5`
(1181 s). That half (no return) is not proved here. -/
theorem loop_complete {Z W : Finset ℕ} {r : ℕ} (free : QFree D V q) (hq : 1 ≤ q) (ZV : Z ⊆ V)
    (cZ : Z.card = q + 1) (dj : Disjoint Z W) (cW : W.card + 1 ≤ r)
    (deg : ∀ z ∈ Z, (outN D V z).card = r) (keep : ∀ z ∈ Z, outN D V z ⊆ Z ∪ W) :
    ∀ z ∈ Z, (outN D Z z).card = 1 ∧ W ⊆ outN D V z ∧ W.card + 1 = r := by
  have split : ∀ z ∈ Z, (outN D Z z).card + (outN D V z ∩ W).card = r := by
    intro z hz
    have e : outN D V z = outN D Z z ∪ (outN D V z ∩ W) := by
      ext w
      simp only [mem_union, mem_inter, mem_outN]
      constructor
      · intro h
        rcases mem_union.mp (keep z hz (mem_outN.mpr h)) with h' | h'
        · exact Or.inl ⟨h', h.2⟩
        · exact Or.inr ⟨h, h'⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
        · exact ⟨ZV h1, h2⟩
        · exact h1
    have d : Disjoint (outN D Z z) (outN D V z ∩ W) :=
      disjoint_left.mpr (fun w h1 h2 => disjoint_left.mp dj (mem_outN.mp h1).1 (mem_inter.mp h2).2)
    have h := deg z hz
    rw [e, card_union_of_disjoint d] at h
    exact h
  have m1 : ∀ z ∈ Z, 1 ≤ (outN D Z z).card := by
    intro z hz
    have := split z hz
    have := card_le_card (inter_subset_right (s₁ := outN D V z) (s₂ := W))
    omega
  have one := LoopCollar.loop_unique_head (free.mono_set ZV) hq cZ m1
  intro z hz
  have s := split z hz
  rw [one z hz] at s
  have le := card_le_card (inter_subset_right (s₁ := outN D V z) (s₂ := W))
  have eqW : outN D V z ∩ W = W := eq_of_subset_of_card_le inter_subset_right (by omega)
  refine ⟨one z hz, fun w hw => ?_, by omega⟩
  have : w ∈ outN D V z ∩ W := by rw [eqW]; exact hw
  exact (mem_inter.mp this).1

/-! ### The fat-bank law and the instances at `r = 9` -/

/-- **The fat-bank law** at radii `(i, j)`, degree `r`, bank size `b`: every row `u` that is not
thin and falls below the level has a bank `Bk u` of at least `b` rows, each at least one above the
level; banks of two such rows are equal or disjoint; two such rows with the same bank are gaps. -/
structure FatBank (D : CH.Digraph) (V : Finset ℕ) (r i j b : ℕ) (Bk : ℕ → Finset ℕ) : Prop where
  sub : ∀ u ∈ V, ¬ Thin D V r u → (ball D V u i).card + (ball D V u j).card < V.card + 1 →
    Bk u ⊆ V ∧ b ≤ (Bk u).card ∧
      ∀ x ∈ Bk u, V.card + 2 ≤ (ball D V x i).card + (ball D V x j).card
  sep : ∀ u ∈ V, ∀ u' ∈ V, ¬ Thin D V r u → ¬ Thin D V r u' →
    (ball D V u i).card + (ball D V u j).card < V.card + 1 →
    (ball D V u' i).card + (ball D V u' j).card < V.card + 1 →
    Bk u = Bk u' ∨ Disjoint (Bk u) (Bk u')
  gap : ∀ u ∈ V, ∀ u' ∈ V, ¬ Thin D V r u → ¬ Thin D V r u' →
    (ball D V u i).card + (ball D V u j).card < V.card + 1 →
    (ball D V u' i).card + (ball D V u' j).card < V.card + 1 →
    Bk u = Bk u' → u ≠ u' → u' ∈ gap D V i j u

open Classical in
/-- The fat savers, as a set. -/
noncomputable def fatSavers (D : CH.Digraph) (V : Finset ℕ) (r i j : ℕ) : Finset ℕ :=
  V.filter (fun u => ¬ Thin D V r u ∧ (ball D V u i).card + (ball D V u j).card < V.card + 1)

/-- The fat savers are empty under the fat-bank law, given the thin data. -/
theorem fat_empty {r i j δ δF b : ℕ} {Bk : ℕ → Finset ℕ} (free : QFree D V q)
    (hq : 3 ≤ q) (hr : r + 1 ≤ 2 * q) (reg : ∀ v ∈ V, (outN D V v).card = r) (hij : i + j ≤ q)
    (hi : 2 ≤ i) (hj : 2 ≤ j) (fb : FatBank D V r i j b Bk) (hb : b ≤ 2 * q + 2 - r)
    (shortF : ∀ v ∈ V, ¬ Thin D V r v → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card + δF)
    (short : ∀ v ∈ V, Thin D V r v →
      V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card + δ)
    (bankrow : ∀ v ∈ V, Thin D V r v →
      (ball D V v i).card + (ball D V v j).card < V.card + 1 → ∀ s, 1 ≤ s → s ≤ r →
      V.card + 2 + s + 2 * r ≤ (ball D V v (i + 1)).card + (ball D V v (j + 1)).card +
        min (s + (i - 1)) (q + 1) + min (s + (j - 1)) (q + 1))
    (pay : ∀ m, m * (δ + 1) < m * m + b) (payFm : ∀ m, m * (δF + 1) < m * m + b) :
    ∀ v ∈ V, ¬ Thin D V r v → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card := by
  classical
  have mem : ∀ u, u ∈ fatSavers D V r i j ↔ u ∈ V ∧ ¬ Thin D V r u ∧
      (ball D V u i).card + (ball D V u j).card < V.card + 1 := fun u => by
    unfold fatSavers; exact mem_filter
  obtain ⟨e, -⟩ := no_short_mixed (F := fatSavers D V r i j) (Bk := Bk) free hq hr reg hij hi hj
    (fun u hu => ((mem u).mp hu).1) (fun u hu => ((mem u).mp hu).2.1)
    (fun u hu => (fb.sub u ((mem u).mp hu).1 ((mem u).mp hu).2.1 ((mem u).mp hu).2.2).1)
    (fun u hu => (fb.sub u ((mem u).mp hu).1 ((mem u).mp hu).2.1 ((mem u).mp hu).2.2).2.1) hb
    (fun v hv vt vF => by
      by_contra low
      exact vF ((mem v).mpr ⟨hv, vt, by omega⟩))
    (fun u hu => shortF u ((mem u).mp hu).1 ((mem u).mp hu).2.1) short bankrow
    (fun u hu => (fb.sub u ((mem u).mp hu).1 ((mem u).mp hu).2.1 ((mem u).mp hu).2.2).2.2)
    (fun u hu u' hu' => fb.sep u ((mem u).mp hu).1 u' ((mem u').mp hu').1 ((mem u).mp hu).2.1
      ((mem u').mp hu').2.1 ((mem u).mp hu).2.2 ((mem u').mp hu').2.2)
    (fun u hu u' hu' => fb.gap u ((mem u).mp hu).1 u' ((mem u').mp hu').1 ((mem u).mp hu).2.1
      ((mem u').mp hu').2.1 ((mem u).mp hu).2.2 ((mem u').mp hu').2.2) pay payFm
  intro v hv vt
  by_contra low
  have : v ∈ fatSavers D V r i j := (mem v).mpr ⟨hv, vt, by omega⟩
  rw [e] at this
  simp at this

/-- **Order 62 from the fat-bank law** (banks of at least five rows, each scoring `≥ 64`). -/
theorem no62_of_bank {Bk : ℕ → Finset ℕ} (free : QFree D V 7)
    (reg : ∀ v ∈ V, (outN D V v).card = 9) (n : V.card = 62) (fl : TopRow.Floors7 D V)
    (fb : FatBank D V 9 3 4 5 Bk) : False := by
  have fat := fat_empty (δ := 3) (δF := 2) free (by norm_num) (by norm_num) reg (by norm_num)
    (by norm_num) (by norm_num) fb (by norm_num)
    (fun v hv nt => by have := fl.fat3 v hv nt; have := fl.f4 v hv; omega)
    (fun v hv _ => by have := fl.f3 v hv; have := fl.f4 v hv; omega)
    (fun v hv vt low s s1 s9 => by
      show V.card + 2 + s + 2 * 9 ≤ (ball D V v 4).card + (ball D V v 5).card +
        min (s + 2) 8 + min (s + 3) 8
      have := fl.thin45 v hv vt
      omega)
    (TopRow.pay_le (fun m hm => by interval_cases m <;> norm_num))
    (TopRow.pay_le (fun m hm => by interval_cases m <;> norm_num))
  exact TopRow.no62_of_fat free reg n fl (fun v hv nt => by have := fat v hv nt; omega)

/-- **Order 72 from the fat-bank law** (banks of at least five rows, each scoring `≥ 74`). -/
theorem no72_of_bank {Bk : ℕ → Finset ℕ} (free : QFree D V 8)
    (reg : ∀ v ∈ V, (outN D V v).card = 9) (n : V.card = 72)
    (f4 : ∀ v ∈ V, 35 ≤ (ball D V v 4).card) (f5 : ∀ v ∈ V, 43 ≤ (ball D V v 5).card)
    (fb : FatBank D V 9 4 4 5 Bk) : False := by
  have fat := fat_empty (δ := 3) (δF := 3) free (by norm_num) (by norm_num) reg (by norm_num)
    (by norm_num) (by norm_num) fb (by norm_num)
    (fun v hv nt => by have := f4 v hv; omega)
    (fun v hv _ => by have := f4 v hv; omega)
    (fun v hv vt low s s1 s9 => by
      show V.card + 2 + s + 2 * 9 ≤ (ball D V v 5).card + (ball D V v 5).card +
        min (s + 3) 9 + min (s + 3) 9
      have := f5 v hv
      omega)
    (TopRow.pay_le (fun m hm => by interval_cases m <;> norm_num))
    (TopRow.pay_le (fun m hm => by interval_cases m <;> norm_num))
  exact TopRow.no72_of_fat free reg n f4 f5 (fun v hv nt => by have := fat v hv nt; omega)

#print axioms loop_complete
#print axioms supplier_score
#print axioms no_short_mixed
#print axioms fat_empty
#print axioms no62_of_bank
#print axioms no72_of_bank
end LeanCH.BR.TopRowFat
