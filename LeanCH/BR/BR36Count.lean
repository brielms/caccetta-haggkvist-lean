import LeanCH.BR.BR36Local

/-!
# BR(3,6), part 3: counting lemmas at the root (Lean 4.35.0)

Paper sources: `BR36_attempt_subagent.md` (Lemmas 2.1, 2.2) and `BR36_residual_subagent.md` (Lemmas N1, N2).

* `small_two` (generic): if `S ⊆ T`, `|T| ≤ |S| + 1`, `1 ≤ |S| ≤ 3`, and every vertex of `S` has two heads in `T`,
  there is a short cycle. Used for Lemma 2.2: a row `m` heading `y ∈ O` forces all `O`-heads of `y` (at least two)
  into `Z_m`, so `out_O(m) = 0` or `out_O(m) + 2 ≤ δ_m` when `δ_m ≤ 4` (`MO_le`).
* `full_heads`, `k0_bound` (Lemma 2.1): full rows head only `(M ∖ m) ∪ I₀`, and `n_F ≥ 1, 2, 3` give
  `k₀ ≥ 2, 3, 4`.
* `p_le` (L3): a row heading `w ∈ I` has `p_w + a_m ≤ 6`; `head_of_J`: under saturation every `w ∈ I` missing a
  vertex of `O` is headed by such a row (Lemma 5.1).
* `N1a`, `N1` (Lemma N1, I-trap): a vertex `w ∈ I` of in-degree 7 heads only rows `m` with `out_O(m) ≥ 3`; if it
  heads none, every head of `w` in `O` has a head among the heads of `w` in `O`, so `p_w ≥ 4`.
* `N2` (Lemma N2): the global identity with `I = J ⊔ H`, `H` = vertices of `I` heading all of `O`.
-/

namespace LeanCH.BR.BR36

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of

/-- Vertices of `I` heading nothing in `O`. -/
def I0 (G : CH.Digraph) (I O : Finset Nat) : Finset Nat := I.filter (fun w => oc G O w = 0)

/-- Vertices of `I` heading all of `O`. -/
def HH (G : CH.Digraph) (I O : Finset Nat) : Finset Nat := I.filter (fun w => oc G O w = 6)

/-- The other vertices of `I`. -/
def JJ (G : CH.Digraph) (I O : Finset Nat) : Finset Nat := I.filter (fun w => oc G O w ≠ 6)

section generic

variable {G : CH.Digraph} {n : Nat}

/-- Two heads each inside a set with at most one extra vertex: a short cycle. -/
theorem small_two (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {S T : Finset Nat} (hT : T ⊆ Finset.range n) (hST : S ⊆ T) (hcard : T.card ≤ S.card + 1)
    (hS3 : S.card ≤ 3) (hne : S.Nonempty) (h2 : ∀ y ∈ S, 2 ≤ oc G T y) : False := by
  apply small_out loopless noShort (hST.trans hT) hS3 hne
  intro y hy
  have h1 := oc_sdiff (G := G) hST y
  have h3 := oc_le (G := G) (T \ S) y
  rw [Finset.card_sdiff_of_subset hST] at h3
  have := h2 y hy
  exact exists_of_oc (by omega)

end generic

namespace Root

variable {G : CH.Digraph} {u : Nat} {I O M : Finset Nat} (R : Root G u I O M)
include R

theorem I0_sub : I0 G I O ⊆ I := Finset.filter_subset _ _
theorem HH_sub : HH G I O ⊆ I := Finset.filter_subset _ _
theorem JJ_sub : JJ G I O ⊆ I := Finset.filter_subset _ _

theorem I0_JJ : I0 G I O ⊆ JJ G I O := fun w hw => by
  obtain ⟨hwI, h0⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hwI, by omega⟩

theorem HH_all {w : Nat} (hw : w ∈ HH G I O) : ∀ x ∈ O, G w x = true :=
  all_of_oc (by rw [R.cO]; exact le_of_eq (Finset.mem_filter.mp hw).2.symm)

theorem JJ_HH_card : (JJ G I O).card + (HH G I O).card = 7 := by
  have := Finset.card_filter_add_card_filter_not (s := I) (fun w => oc G O w ≠ 6)
  simp only [not_not] at this
  rw [R.cI] at this
  exact this

theorem JJ_union : JJ G I O ∪ HH G I O = I := by
  ext w
  simp only [JJ, HH, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    by_cases h6 : oc G O w = 6
    · exact Or.inr ⟨h, h6⟩
    · exact Or.inl ⟨h, h6⟩

theorem JJ_HH_disj : Disjoint (JJ G I O) (HH G I O) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2

theorem pO_le {w : Nat} : oc G O w ≤ 6 := R.cO ▸ oc_le O w

/-- Heads of a row in `O` lie in `Z_m`. -/
theorem MO_Z {m : Nat} (hm : m ∈ M) : oc G O m + ic G O m ≤ 6 := by
  have := oc_ic_le R.H.loopless R.H.noShort R.subO (R.ltM hm) (B := O) (fun v hv _ => hv)
  rwa [R.cO] at this

/-- (L3) A row heading `w ∈ I` misses every head of `w` in `O`. -/
theorem p_le {m w : Nat} (hm : m ∈ M) (hw : w ∈ I) (hmw : G m w = true) : oc G O w + ic G O m ≤ 6 := by
  have h1 : oc G O w ≤ (O.filter (fun v => ¬ G v m = true)).card := oc_le_of_sub (fun x hx hwx => by
    refine Finset.mem_filter.mpr ⟨hx, ?_⟩
    rw [R.L3 hm hw hx hmw hwx]
    exact Bool.false_ne_true)
  have h2 := Finset.card_filter_add_card_filter_not (s := O) (fun v => G v m = true)
  rw [R.cO] at h2
  unfold ic
  omega

/-- Lemma 5.1: a vertex of `I` missing some vertex of `O` is headed by a row. -/
theorem head_of_J {w : Nat} (hw : w ∈ I) (hp : oc G O w ≠ 6) : ∃ m ∈ M, G m w = true := by
  have : ∃ x ∈ O, G w x = false := by
    by_contra hcon
    push Not at hcon
    apply hp
    have := oc_full (G := G) (A := O) (w := w) (fun x hx => by simpa using hcon x hx)
    rw [this, R.cO]
  obtain ⟨x, hx, hwx⟩ := this
  obtain ⟨m, hm, _, hmw⟩ := R.lemma51 hw hx hwx
  exact ⟨m, hm, hmw⟩

/-- **Lemma 2.2.** A row heading a vertex of `O` misses at least two more vertices of `O` (when `δ_m ≤ 4`). -/
theorem MO_le {m : Nat} (hm : m ∈ M) (h2 : 2 ≤ ic G O m) : oc G O m = 0 ∨ oc G O m + ic G O m + 2 ≤ 6 := by
  classical
  have hZc : (O.filter (fun v => ¬ G v m = true)).card + ic G O m = 6 := by
    have := Finset.card_filter_add_card_filter_not (s := O) (fun v => G v m = true)
    rw [R.cO] at this; unfold ic; omega
  have hZO : O.filter (fun v => ¬ G v m = true) ⊆ O := Finset.filter_subset _ _
  set Z := O.filter (fun v => ¬ G v m = true) with hZ
  set Y := O.filter (fun v => G m v = true) with hY
  have hYZ : Y ⊆ Z := by
    intro y hy
    obtain ⟨hyO, hmy⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨hyO, ?_⟩
    rw [R.H.back (R.ltM hm) (R.ltO hyO) hmy]; exact Bool.false_ne_true
  -- every head of a vertex of `Y` in `O` lies in `Z`; there are at least two
  have hY2 : ∀ y ∈ Y, 2 ≤ oc G Z y := by
    intro y hy
    obtain ⟨hyO, hmy⟩ := Finset.mem_filter.mp hy
    have hym : G y m = false := R.H.back (R.ltM hm) (R.ltO hyO) hmy
    have h1 := R.O_out hyO
    have h3 : oc G M y ≤ 4 := by
      rw [← oc_erase_eq (G := G) (A := M) hym]
      have := oc_le (G := G) (M.erase m) y
      rw [Finset.card_erase_of_mem hm, R.cM] at this
      exact this
    have h4 : oc G O y = oc G Z y := by
      rw [oc_sdiff (G := G) hZO y]
      have : oc G (O \ Z) y = 0 := oc_eq_zero (fun x hx => by
        obtain ⟨hxO, hxZ⟩ := Finset.mem_sdiff.mp hx
        have hxm : G x m = true := by
          by_contra h
          exact hxZ (Finset.mem_filter.mpr ⟨hxO, h⟩)
        cases hyx : G y x
        · rfl
        · rw [R.H.tri (R.ltM hm) (R.ltO hyO) (R.ltO hxO) hmy hyx] at hxm
          exact absurd hxm Bool.false_ne_true)
      omega
    omega
  have hYc : oc G O m = Y.card := rfl
  have hZsub : Z ⊆ Finset.range 19 := hZO.trans R.subO
  by_contra hcon
  push Not at hcon
  obtain ⟨hpos, hlt⟩ := hcon
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  by_cases h3 : Y.card ≤ 3
  · exact small_two R.H.loopless R.H.noShort hZsub hYZ (by omega) h3 hYne hY2
  · obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (show 3 ≤ Y.card by omega)
    have hYZc := Finset.card_le_card hYZ
    exact small_two R.H.loopless R.H.noShort hZsub (hS.trans hYZ) (by omega) (by omega)
      (Finset.card_pos.mp (by omega)) (fun y hy => hY2 y (hS hy))

/-- (L5) A full row heads nothing in `O` and only vertices of `I₀` in `I`. -/
theorem full_heads {m : Nat} (hm : m ∈ M) (hfull : ic G O m = 6) : 6 ≤ oc G M m + oc G (I0 G I O) m := by
  have hall : ∀ x ∈ O, G x m = true := all_of_ic (by rw [R.cO]; omega)
  have h1 := R.out6 (R.ltM hm)
  rw [R.outM hm] at h1
  have h2 : oc G O m = 0 := oc_eq_zero (fun x hx => R.H.back (R.ltO hx) (R.ltM hm) (hall x hx))
  have h3 : oc G (I \ I0 G I O) m = 0 := by
    apply oc_eq_zero
    intro w hw
    obtain ⟨hwI, hwn⟩ := Finset.mem_sdiff.mp hw
    cases h : G m w
    · rfl
    · exfalso
      apply hwn
      refine Finset.mem_filter.mpr ⟨hwI, oc_eq_zero (fun x hx => ?_)⟩
      cases h' : G w x
      · rfl
      · have := R.L3 hm hwI hx h h'
        rw [hall x hx] at this
        exact Bool.noConfusion this
  have h4 := oc_sdiff (G := G) R.I0_sub m
  omega

theorem I0_card : (I0 G I O).card ≤ 7 := R.cI ▸ Finset.card_le_card R.I0_sub

/-- **Lemma 2.1.** Full rows force `I₀`. -/
theorem k0_bound {F : Finset Nat} (hF : F ⊆ M) (hfull : ∀ m ∈ F, ic G O m = 6) :
    (1 ≤ F.card → 2 ≤ (I0 G I O).card) ∧ (2 ≤ F.card → 3 ≤ (I0 G I O).card) ∧
      (3 ≤ F.card → 4 ≤ (I0 G I O).card) := by
  classical
  have heads : ∀ m ∈ F, 6 ≤ oc G M m + oc G (I0 G I O) m := fun m hm => R.full_heads (hF hm) (hfull m hm)
  have hMm : ∀ m ∈ F, oc G M m ≤ 4 := by
    intro m hm
    rw [← oc_erase_eq (G := G) (A := M) (R.H.loopless m (R.ltM (hF hm)))]
    have := oc_le (G := G) (M.erase m) m
    rw [Finset.card_erase_of_mem (hF hm), R.cM] at this
    exact this
  have hle : ∀ m, oc G (I0 G I O) m ≤ (I0 G I O).card := fun m => oc_le _ m
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · obtain ⟨m, hm⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    have := heads m hm; have := hMm m hm; have := hle m; omega
  · by_contra hk
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
    have row : ∀ x ∈ F, ∀ y ∈ M, x ≠ y → G x y = true := by
      intro x hx y hy hxy
      have h1 := heads x hx
      have h2 := hle x
      have h3 := oc_erase_eq (G := G) (A := M) (R.H.loopless x (R.ltM (hF hx)))
      have h5 : (M.erase x).card = 4 := by rw [Finset.card_erase_of_mem (hF hx), R.cM]
      have hall := all_of_oc (G := G) (A := M.erase x) (w := x) (by omega)
      exact hall y (Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩)
    exact R.H.n2 (R.ltM (hF ha)) (R.ltM (hF hb)) (row a ha b (hF hb) hab) (row b hb a (hF ha) (Ne.symm hab))
  · by_contra hk
    obtain ⟨F', hF', hF'c⟩ := Finset.exists_subset_card_eq h3
    apply small_out R.H.loopless R.H.noShort ((hF'.trans hF).trans R.subM) (by omega)
      (Finset.card_pos.mp (by omega))
    intro m hm
    have h1 := heads m (hF' hm)
    have h2 := hle m
    have h3 := oc_sdiff (G := G) (hF'.trans hF) m
    have h4 : (M \ F').card = 2 := by rw [Finset.card_sdiff_of_subset (hF'.trans hF), R.cM, hF'c]
    have h5 := oc_le (G := G) (M \ F') m
    exact exists_of_oc (by omega)

/-! ### Lemma N1 (the I-trap) -/

/-- A vertex `w ∈ I` of in-degree 7 heads only rows `m` with `out_O(m) ≥ 3`. -/
theorem N1a {w m : Nat} (hw : w ∈ I) (h7 : ic G V w = 7) (hm : m ∈ M) (hwm : G w m = true) :
    3 ≤ oc G O m := by
  classical
  have hdis := R.dIM
  set A := I ∪ M with hA
  have hAc : A.card = 12 := by rw [hA, Finset.card_union_of_disjoint hdis, R.cI, R.cM]
  have hinA : ic G A w = 7 := by rw [hA, ic_union hdis, ← R.inI hw, h7]
  have hcomp := Finset.card_filter_add_card_filter_not (s := A) (fun v => G v w = true)
  have hmw : G m w = false := R.H.back (R.ltI hw) (R.ltM hm) hwm
  have hwA : w ∈ A.filter (fun v => ¬ G v w = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hw, by rw [R.H.loopless w (R.ltI hw)]; exact Bool.false_ne_true⟩
  have hmA : m ∈ (A.filter (fun v => ¬ G v w = true)).erase w :=
    Finset.mem_erase.mpr ⟨(R.neIM hw hm).symm,
      Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hm, by rw [hmw]; exact Bool.false_ne_true⟩⟩
  have hsub : oc G A m ≤ (((A.filter (fun v => ¬ G v w = true)).erase w).erase m).card := by
    apply oc_le_of_sub
    intro v hv hmv
    have hvn : v < 19 := Finset.mem_range.mp ((Finset.union_subset R.subI R.subM) hv)
    refine Finset.mem_erase.mpr ⟨R.H.ne_of_arc (R.ltM hm) hmv |>.symm, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
    · rintro rfl; rw [hmw] at hmv; exact Bool.false_ne_true hmv
    · refine Finset.mem_filter.mpr ⟨hv, ?_⟩
      rw [R.H.tri (R.ltI hw) (R.ltM hm) hvn hwm hmv]; exact Bool.false_ne_true
  rw [Finset.card_erase_of_mem hmA, Finset.card_erase_of_mem hwA] at hsub
  unfold ic at hinA
  have hocA : oc G A m = oc G I m + oc G M m := by rw [hA, oc_union hdis]
  have hout := R.out6 (R.ltM hm)
  rw [R.outM hm] at hout
  omega

/-- **Lemma N1.** A vertex `w ∈ I` of in-degree 7 heading only rows with `out_O ≤ 2` heads no row, and every
head of `w` in `O` has a head among the heads of `w` in `O`; hence `p_w ≥ 4`. -/
theorem N1 {w : Nat} (hw : w ∈ I) (h7 : ic G V w = 7) (hrow : ∀ m ∈ M, G w m = true → oc G O m ≤ 2) :
    (∀ m ∈ M, G w m = false) ∧ (∀ x ∈ O, G w x = true → ∃ y ∈ O, G w y = true ∧ G x y = true) ∧
      4 ≤ oc G O w := by
  classical
  have noM : ∀ m ∈ M, G w m = false := by
    intro m hm
    cases h : G w m
    · rfl
    · have := R.N1a hw h7 hm h; have := hrow m hm h; omega
  have hocM : oc G M w = 0 := oc_eq_zero noM
  have hout : oc G V w = 6 := R.cap7 (R.ltI hw) h7
  rw [R.outI hw, hocM] at hout
  have hin := h7
  rw [R.inI hw] at hin
  have hII := oc_ic_le_mem R.H.loopless R.H.noShort R.subI hw
  rw [R.cI] at hII
  have hicM := ic_le (G := G) M w
  rw [R.cM] at hicM
  have sink : ∀ x ∈ O, G w x = true → ∃ y ∈ O, G w y = true ∧ G x y = true := by
    intro x hx hwx
    by_contra hcon
    push Not at hcon
    have h1 : oc G O x ≤ (O.filter (fun v => ¬ G w v = true)).card := oc_le_of_sub (fun y hy hxy => by
      exact Finset.mem_filter.mpr ⟨hy, fun hwy => hcon y hy hwy hxy⟩)
    have h2 : oc G M x ≤ (M.filter (fun v => ¬ G v w = true)).card := oc_le_of_sub (fun v hv hxv => by
      refine Finset.mem_filter.mpr ⟨hv, ?_⟩
      rw [R.H.tri (R.ltI hw) (R.ltO hx) (R.ltM hv) hwx hxv]; exact Bool.false_ne_true)
    have h3 := Finset.card_filter_add_card_filter_not (s := O) (fun v => G w v = true)
    have h4 := Finset.card_filter_add_card_filter_not (s := M) (fun v => G v w = true)
    rw [R.cO] at h3
    rw [R.cM] at h4
    have h3' : (O.filter (fun v => ¬ G w v = true)).card + oc G O w = 6 := by unfold oc; omega
    have h4' : (M.filter (fun v => ¬ G v w = true)).card + ic G M w = 5 := by unfold ic; omega
    have h5 := R.O_out hx
    omega
  refine ⟨noM, sink, ?_⟩
  by_contra h4
  have hpos : 1 ≤ oc G O w := by omega
  apply small_out R.H.loopless R.H.noShort (A := O.filter (fun v => G w v = true))
    ((Finset.filter_subset _ O).trans R.subO) (by unfold oc at h4; omega)
    (Finset.card_pos.mp hpos)
  intro x hx
  obtain ⟨hxO, hwx⟩ := Finset.mem_filter.mp hx
  obtain ⟨y, hy, hwy, hxy⟩ := sink x hxO hwx
  exact ⟨y, Finset.mem_filter.mpr ⟨hy, hwy⟩, hxy⟩

/-! ### Lemma N2 (the global identity, split along `I = J ⊔ H`) -/

theorem noMHH {m w : Nat} (hm : m ∈ M) (hw : w ∈ HH G I O) : G m w = false :=
  R.noMH hm (R.HH_sub hw) (R.HH_all hw)

/-- **Lemma N2**, exact. -/
theorem N2 :
    7 + ∑ w ∈ JJ G I O, oc G O w + 6 * (HH G I O).card + ∑ m ∈ M, oc G O m + ∑ m ∈ M, ic G V m +
        ∑ w ∈ JJ G I O, ic G V w + ∑ w ∈ JJ G I O, oc G (HH G I O) w =
      ∑ m ∈ M, ic G O m + ∑ m ∈ M, oc G V m + ∑ w ∈ JJ G I O, oc G V w + 7 * (HH G I O).card +
        ∑ η ∈ HH G I O, oc G (JJ G I O) η + ∑ η ∈ HH G I O, oc G M η := by
  have hg := R.global
  set J := JJ G I O
  set H := HH G I O
  have hsplit : ∀ f : Nat → Nat, ∑ w ∈ I, f w = ∑ w ∈ J, f w + ∑ w ∈ H, f w := fun f => by
    rw [← Finset.sum_union R.JJ_HH_disj, R.JJ_union]
  rw [hsplit, hsplit (ic G V), hsplit (oc G V)] at hg
  have h6 : ∀ w ∈ H, oc G O w = 6 := fun w hw => (Finset.mem_filter.mp hw).2
  have e1 : ∑ w ∈ H, oc G O w = 6 * H.card := by
    rw [Finset.sum_congr rfl h6, Finset.sum_const, smul_eq_mul, mul_comm]
  have e2 : ∑ w ∈ H, ic G V w = ∑ w ∈ H, ic G I w := Finset.sum_congr rfl (fun w hw => by
    rw [R.inI (R.HH_sub hw), ic_eq_zero (fun m hm => R.noMHH hm hw)]; rfl)
  have e3 : ∑ w ∈ H, oc G V w = 7 * H.card + ∑ w ∈ H, oc G I w + ∑ w ∈ H, oc G M w := by
    rw [Finset.sum_congr rfl (fun w hw => by rw [R.outI (R.HH_sub hw), h6 w hw])]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul, Finset.sum_const, smul_eq_mul]
    omega
  have e4 : ∑ w ∈ H, ic G I w = ∑ w ∈ J, oc G H w + ∑ w ∈ H, oc G H w := by
    rw [← swap G I H, hsplit]
  have e5 : ∑ w ∈ H, oc G I w = ∑ w ∈ H, oc G J w + ∑ w ∈ H, oc G H w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => by rw [← R.JJ_union, oc_union R.JJ_HH_disj])
  have e6 : ∑ x ∈ O, oc G M x = ∑ m ∈ M, ic G O m := swap G O M
  omega

/-- Rows: `Σ_M in ≤ 35`. -/
theorem sumM_in : ∑ m ∈ M, ic G V m ≤ 35 := by
  have := sum_le_card_mul (s := M) (f := ic G V) (c := 7) (fun m hm => R.cap (R.ltM hm))
  rw [R.cM] at this; exact this

/-- Rows: `30 ≤ Σ_M out`. -/
theorem sumM_out : 30 ≤ ∑ m ∈ M, oc G V m := by
  have := card_mul_le_sum (s := M) (f := oc G V) (c := 6) (fun m hm => R.out6 (R.ltM hm))
  rw [R.cM] at this; exact this

theorem sumJH : ∑ w ∈ JJ G I O, oc G (HH G I O) w ≤ (JJ G I O).card * (HH G I O).card :=
  sum_le_card_mul (fun w _ => oc_le _ w)

/-- Per vertex: `in ≤ out` unless `in = 7`. -/
theorem in_le_out {v : Nat} (hv : v < 19) (h : ic G V v ≠ 7) : ic G V v ≤ oc G V v := by
  have := R.cap hv; have := R.out6 hv; omega

theorem in_le_out' {v : Nat} (hv : v < 19) : ic G V v ≤ oc G V v + 1 := by
  by_cases h : ic G V v = 7
  · have := R.cap7 hv h; omega
  · have := R.in_le_out hv h; omega

end Root

end LeanCH.BR.BR36
