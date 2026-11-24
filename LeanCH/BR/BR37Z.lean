import LeanCH.BR.BR36Disc
import LeanCH.BR.BR36Count

/-!
# BR(3,7), part 1: Theorem Z (Lean 4.35.0)

Paper source: `checkpoints/boundary_20261111/BR37_attempt_subagent.md`, section 5 (audited in
`BR37_audit_subagent.md`).

**Theorem Z (`SHyp.K_nonempty7`).** In a saturated boundary graph at `s = 7` with in-degrees at most 8, every root
`u` has `K(u) ≠ ∅`.

Proof. Suppose `K(u) = ∅` (`|I| = 8`, `|O| = 7`, `|M| = 6`).
* Step 1. Every `x ∈ O` misses a row, so `out_O(x) ≥ 2`; `BR(3,2)` on the 7-set `O` (`induced_regular_in`) makes
  `D[O]` 2-regular (out and in), so every `x ∈ O` misses exactly one row `r(x)`; `Z_m = r⁻¹(m)`, `Σ |Z_m| = 7`.
* Step 2. A vertex `w ∈ I` heading some `x ∈ O` is headed by at most one row (two rows heading `w` are both
  missed by `x`).
* Steps 3-5. Row balance and the out-degrees of `I₀` give `(M→O) ≥ 21 − k₀(8 − k₀) ≥ 5`. (We bound the rows into
  `I ∖ I₀` by `|I ∖ I₀|` directly, which absorbs the paper's `h`.)
* Step 6. A row `m` heads only vertices `y ∈ Z_m` whose two `O`-heads lie in `Z_m`; so `out_O(m) = 0` or
  `out_O(m) + 2 ≤ |Z_m| ≤ 6` (for `|Z_m| ≤ 4` by `small_two`, for `|Z_m| ∈ {5,6}` by counting the arcs into
  `O ∖ Z_m`, using in-degree 2). Summing, `(M→O) ≤ 4`.
-/

namespace LeanCH.BR.BR37

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of
open LeanCH.BR.BR36

/-- `BR(q,c)` on an induced subgraph of order `qc + 1` with internal minimum out-degree `c`: every member has exactly
`c` parents inside (the in-degree half of `StrictCap.induced_regular`). -/
theorem induced_regular_in {G : CH.Digraph} {n q c : Nat} {M : Finset Nat}
    (br : BoundaryRegular q c) (hsub : M ⊆ Finset.range n) (hcard : M.card = q * c + 1)
    (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n q)
    (keep : ∀ x ∈ M, c ≤ (M.filter (fun w => G x w = true)).card) :
    ∀ y ∈ M, (M.filter (fun u => G u y = true)).card = c := by
  classical
  obtain ⟨e, eB, eI, eM, eS⟩ := CH.Side.sc_finset_enumeration hsub
  set m := M.card with hm
  let H : CH.Digraph := fun a b => if a < m then (if b < m then G (e a) (e b) else false) else false
  have hloop : CH.Loopless H m := by
    intro v hv
    change (if v < m then (if v < m then G (e v) (e v) else false) else false) = false
    simp only [hv, ite_true]; exact loopless (e v) (eB v hv)
  have hmin : CH.MinOutdegreeAtLeast H m c := by
    intro a ha
    let T : Finset Nat := (Finset.range m).filter (fun i => G (e a) (e i) = true)
    have himage : T.image e = M.filter (fun w => G (e a) w = true) := by
      ext w
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨i, ⟨hi, hG⟩, rfl⟩; exact ⟨eM i hi, hG⟩
      · rintro ⟨hwM, hG⟩; obtain ⟨i, hi, rfl⟩ := eS w hwM; exact ⟨i, ⟨hi, hG⟩, rfl⟩
    have hinj : Set.InjOn e T := by
      intro i hi j hj hij
      have hi' : i ∈ T := hi
      have hj' : j ∈ T := hj
      exact eI i j (Finset.mem_range.mp (Finset.mem_filter.mp hi').1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj').1) hij
    have hTcard : c ≤ T.card := by
      have := Finset.card_image_of_injOn hinj
      rw [himage] at this; rw [← this]; exact keep (e a) (eM a ha)
    refine ⟨(T.sort (· ≤ ·)).take c, ?_, ?_, ?_⟩
    · rw [List.length_take, Finset.length_sort]; omega
    · exact (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)
    · intro w hw
      have hwT : w ∈ T := (Finset.mem_sort _).mp ((List.take_sublist _ _).subset hw)
      simp only [T, Finset.mem_filter, Finset.mem_range] at hwT
      refine ⟨hwT.1, ?_⟩
      change (if a < m then (if w < m then G (e a) (e w) else false) else false) = true
      simp only [ha, hwT.1, ite_true]; exact hwT.2
  have hshort : ¬ CH.HasDirectedCycleAtMost H m q := fun h =>
    noShort (CH.Side.sc_induced_subgraph_transport eB eI h)
  rw [hcard] at hloop hmin hshort
  have hreg := br H hloop hmin hshort
  intro y hy
  obtain ⟨a, ha, rfl⟩ := eS y hy
  have h1 := hreg a (by omega)
  have himage : (par H (q * c + 1) a).image e = M.filter (fun u => G u (e a) = true) := by
    ext w
    simp only [par, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, ⟨hi, hG⟩, rfl⟩
      have hi' : i < m := by omega
      have hG' : (if i < m then (if a < m then G (e i) (e a) else false) else false) = true := hG
      simp only [hi', ha, ite_true] at hG'
      exact ⟨eM i hi', hG'⟩
    · rintro ⟨hwM, hG⟩
      obtain ⟨i, hi, rfl⟩ := eS w hwM
      refine ⟨i, ⟨by omega, ?_⟩, rfl⟩
      change (if i < m then (if a < m then G (e i) (e a) else false) else false) = true
      simp only [hi, ha, ite_true]; exact hG
  have hinj : Set.InjOn e (par H (q * c + 1) a) := by
    intro i hi j hj hij
    have hi' : i ∈ par H (q * c + 1) a := hi
    have hj' : j ∈ par H (q * c + 1) a := hj
    have hi'' := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
    have hj'' := Finset.mem_range.mp (Finset.mem_filter.mp hj').1
    exact eI i j (by omega) (by omega) hij
  rw [← himage, Finset.card_image_of_injOn hinj, h1]

namespace SHyp7

variable {G : CH.Digraph} (H : SHyp 7 G)
include H

theorem outM {u m : Nat} (hu : u < 22) (hm : m ∈ MM G 7 u) :
    oc G (VS 7) m = oc G (II G 7 u) m + oc G (OO G 7 u) m + oc G (MM G 7 u) m := by
  rw [H.split_out hu m, (mem_MM.mp hm).2.2.1]; simp

theorem inM {u m : Nat} (hu : u < 22) (hm : m ∈ MM G 7 u) :
    ic G (VS 7) m = ic G (II G 7 u) m + ic G (OO G 7 u) m + ic G (MM G 7 u) m := by
  rw [H.split_in hu m, (mem_MM.mp hm).2.2.2]; simp

theorem outI {u w : Nat} (hu : u < 22) (hw : w ∈ II G 7 u) :
    oc G (VS 7) w = 1 + oc G (II G 7 u) w + oc G (OO G 7 u) w + oc G (MM G 7 u) w := by
  rw [H.split_out hu w, (mem_II.mp hw).2]; simp

end SHyp7

/-- **Theorem Z.** -/
theorem SHyp.K_nonempty7 {G : CH.Digraph} (H : SHyp 7 G) {u : Nat} (hr : IsRoot G 7 u) :
    (KS G 7 u).Nonempty := by
  classical
  by_contra hK
  rw [Finset.not_nonempty_iff_eq_empty] at hK
  have hu := hr.1
  have hMc := H.root_M hr
  have cI : (II G 7 u).card = 8 := by rw [card_II]; exact hr.2.1
  have cO : (OO G 7 u).card = 7 := by rw [card_OO]; exact hr.2.2
  set I := II G 7 u with hI
  set O := OO G 7 u with hO
  set M := MM G 7 u with hM
  have cM : M.card = 6 := by omega
  have subO : O ⊆ Finset.range 22 := H.subO
  -- Step 1
  have miss : ∀ x ∈ O, ∃ m ∈ M, G x m = false := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have : x ∈ KS G 7 u := Finset.mem_filter.mpr ⟨hx, fun m hm => by simpa using hcon m hm⟩
    rw [hK] at this
    exact Finset.notMem_empty x this
  have ocM5 : ∀ x ∈ O, oc G M x ≤ 5 := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ := miss x hx
    rw [← oc_erase_eq (G := G) (A := M) hxm]
    have := oc_le (G := G) (M.erase m) x
    rw [Finset.card_erase_of_mem hm, cM] at this
    exact this
  have outO : ∀ x ∈ O, oc G (VS 7) x = oc G O x + oc G M x := fun x hx => H.outO hu hx
  have keep : ∀ x ∈ O, 2 ≤ oc G O x := by
    intro x hx
    have h1 := H.out (H.ltO hx)
    rw [outO x hx] at h1
    have := ocM5 x hx
    omega
  have regO : ∀ x ∈ O, oc G O x = 2 :=
    LeanCH.BR.StrictCap.induced_regular (q := 3) (c := 2) LeanCH.BR.SmallBR.br_two subO cO H.loopless
      H.noShort keep
  have regI : ∀ x ∈ O, ic G O x = 2 :=
    induced_regular_in (q := 3) (c := 2) LeanCH.BR.SmallBR.br_two subO cO H.loopless H.noShort keep
  have ocM : ∀ x ∈ O, oc G M x = 5 := by
    intro x hx
    have h1 := H.out (H.ltO hx)
    rw [outO x hx, regO x hx] at h1
    have := ocM5 x hx
    omega
  have one : ∀ x ∈ O, ∀ m ∈ M, ∀ m' ∈ M, G x m = false → G x m' = false → m = m' := by
    intro x hx m hm m' hm' g1 g2
    by_contra hne
    have h1 : oc G M x ≤ ((M.erase m).erase m').card := oc_le_of_sub (fun v hv hxv => by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hv⟩⟩
      · rintro rfl; rw [g2] at hxv; exact Bool.false_ne_true hxv
      · rintro rfl; rw [g1] at hxv; exact Bool.false_ne_true hxv)
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hne, hm'⟩), Finset.card_erase_of_mem hm,
      cM] at h1
    have := ocM x hx
    omega
  -- Step 2: a vertex of `I` heading `O` is headed by at most one row
  have rowR : ∀ w ∈ I, 1 ≤ oc G O w → ic G M w ≤ 1 := by
    intro w hw hp
    obtain ⟨x, hx, hwx⟩ := exists_of_oc hp
    apply Finset.card_le_one.mpr
    intro m hm m' hm'
    obtain ⟨hmM, hmw⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm'M, hm'w⟩ := Finset.mem_filter.mp hm'
    exact one x hx m hmM m' hm'M (H.tri (H.ltM hmM) (H.ltI hw) (H.ltO hx) hmw hwx)
      (H.tri (H.ltM hm'M) (H.ltI hw) (H.ltO hx) hm'w hwx)
  -- Steps 3-5: `(M→O) ≥ 5`
  have hMO5 : 5 ≤ ∑ m ∈ M, oc G O m := by
    have Sout : M.card * 7 ≤ ∑ m ∈ M, (oc G I m + oc G O m + oc G M m) :=
      card_mul_le_sum (fun m hm => by rw [← SHyp7.outM H hu hm]; exact H.out (H.ltM hm))
    have Sin : ∑ m ∈ M, (ic G I m + ic G O m + ic G M m) ≤ M.card * 8 :=
      sum_le_card_mul (fun m hm => by rw [← SHyp7.inM H hu hm]; exact H.cap m (H.ltM hm))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, cM] at Sout Sin
    have e1 : ∑ m ∈ M, ic G O m = 35 := by
      rw [← swap G O M, Finset.sum_congr rfl ocM, Finset.sum_const, cO, smul_eq_mul]
    have e2 : ∑ m ∈ M, oc G M m = ∑ m ∈ M, ic G M m := swap G M M
    have e3 : ∑ m ∈ M, oc G I m = ∑ w ∈ I, ic G M w := swap G M I
    have e4 : ∑ m ∈ M, ic G I m = ∑ w ∈ I, oc G M w := (swap G I M).symm
    set I0 := I.filter (fun w => oc G O w = 0) with hI0
    have hI0I : I0 ⊆ I := Finset.filter_subset _ _
    set R := I \ I0 with hR
    have cR : R.card + I0.card = 8 := by rw [hR, Finset.card_sdiff_of_subset hI0I, cI]; have := Finset.card_le_card hI0I; omega
    have sp : ∀ f : Nat → Nat, ∑ w ∈ I, f w = ∑ w ∈ R, f w + ∑ w ∈ I0, f w := fun f =>
      (Finset.sum_sdiff hI0I).symm
    have hRrow : ∑ w ∈ R, ic G M w ≤ R.card := by
      have := sum_le_card_mul (s := R) (f := ic G M) (c := 1) (fun w hw => by
        obtain ⟨hwI, hwn⟩ := Finset.mem_sdiff.mp hw
        exact rowR w hwI (by
          by_contra h0
          exact hwn (Finset.mem_filter.mpr ⟨hwI, by omega⟩)))
      rwa [mul_one] at this
    -- vertices of `I₀`: in ≤ out
    have hI0row : ∀ w ∈ I0, ic G M w + ic G I w ≤ 1 + oc G I w + oc G M w := by
      intro w hw
      have hwI := hI0I hw
      have hp : oc G O w = 0 := (Finset.mem_filter.mp hw).2
      have h1 := H.out (H.ltI hwI)
      have h1' : oc G (VS 7) w = 1 + oc G I w + oc G O w + oc G M w := SHyp7.outI H hu hwI
      have hin' : ic G (VS 7) w = ic G I w + ic G M w := H.inI hu hwI
      rw [h1', hp] at h1
      have h2 : oc G I w + ic G I w + 1 ≤ I.card := oc_ic_le_mem H.loopless H.noShort H.subI hwI
      have h3 : oc G M w + ic G M w ≤ M.card :=
        oc_ic_le H.loopless H.noShort H.subM (H.ltI hwI) (B := M) (fun v hv _ => hv)
      rw [cI] at h2
      rw [cM] at h3
      omega
    have S0 := Finset.sum_le_sum hI0row
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul, mul_one] at S0
    have hsplitI : ∀ w, oc G I w = oc G I0 w + oc G R w := fun w => oc_sdiff hI0I w
    have hsplitI' : ∀ w, ic G I0 w ≤ ic G I w := fun w => ic_mono hI0I w
    have a1 : ∑ w ∈ I0, oc G I w = ∑ w ∈ I0, oc G I0 w + ∑ w ∈ I0, oc G R w := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun w _ => hsplitI w)
    have a2 : ∑ w ∈ I0, ic G I0 w ≤ ∑ w ∈ I0, ic G I w := Finset.sum_le_sum (fun w _ => hsplitI' w)
    have a3 : ∑ w ∈ I0, oc G I0 w = ∑ w ∈ I0, ic G I0 w := swap G I0 I0
    have a4 : ∑ w ∈ I0, oc G R w ≤ I0.card * R.card := sum_le_card_mul (fun w _ => oc_le R w)
    rw [sp (ic G M)] at e3
    rw [sp (oc G M)] at e4
    clear_value I0 R
    have hk : I0.card ≤ 8 := by omega
    generalize I0.card = k0 at *
    generalize R.card = r at *
    interval_cases k0 <;> omega
  -- Step 6: `(M→O) ≤ 4`
  have rowY : ∀ m ∈ M, oc G O m + 2 * (if 1 ≤ oc G O m then 1 else 0) ≤ (O.filter (fun x => G x m = false)).card ∧
      oc G O m ≤ 4 * (if 1 ≤ oc G O m then 1 else 0) := by
    intro m hm
    have hZO : O.filter (fun x => G x m = false) ⊆ O := Finset.filter_subset _ _
    set Z := O.filter (fun x => G x m = false) with hZ
    set Y := O.filter (fun x => G m x = true) with hY
    have hYc : oc G O m = Y.card := rfl
    have hZ6 : Z.card ≤ 6 := by
      obtain ⟨a, ha, ham⟩ := H.am_pos hu hm
      have : Z ⊆ O.erase a := fun x hx => by
        obtain ⟨hxO, hxm⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_erase.mpr ⟨by rintro rfl; rw [ham] at hxm; exact Bool.noConfusion hxm, hxO⟩
      have := Finset.card_le_card this
      rw [Finset.card_erase_of_mem ha, cO] at this
      exact this
    by_cases hpos : 1 ≤ oc G O m
    · rw [if_pos hpos]
      have hYZ : Y ⊆ Z := fun y hy => by
        obtain ⟨hyO, hmy⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨hyO, H.back (H.ltM hm) (H.ltO hyO) hmy⟩
      -- every head in `O` of a vertex of `Y` lies in `Z`
      have hYZh : ∀ y ∈ Y, ∀ z ∈ O, G y z = true → z ∈ Z := by
        intro y hy z hz hyz
        obtain ⟨hyO, hmy⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨hz, H.tri (H.ltM hm) (H.ltO hyO) (H.ltO hz) hmy hyz⟩
      have hY2 : ∀ y ∈ Y, oc G Z y = 2 := by
        intro y hy
        have hyO := hZO (hYZ hy)
        rw [← regO y hyO, oc_sdiff (G := G) hZO y]
        have : oc G (O \ Z) y = 0 := oc_eq_zero (fun z hz => by
          cases h : G y z
          · rfl
          · exact absurd (hYZh y hy z (Finset.mem_sdiff.mp hz).1 h) (Finset.mem_sdiff.mp hz).2)
        omega
      have hZsub : Z ⊆ Finset.range 22 := hZO.trans subO
      have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
      by_contra hcon
      have hlt : Z.card ≤ Y.card + 1 := by
        have := Finset.card_le_card hYZ
        omega
      by_cases hZ4 : Z.card ≤ 4
      · by_cases h3 : Y.card ≤ 3
        · exact small_two H.loopless H.noShort hZsub hYZ hlt h3 hYne (fun y hy => le_of_eq (hY2 y hy).symm)
        · obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (show 3 ≤ Y.card by omega)
          have := Finset.card_le_card hYZ
          exact small_two H.loopless H.noShort hZsub (hS.trans hYZ) (by omega) (by omega)
            (Finset.card_pos.mp (by omega)) (fun y hy => le_of_eq (hY2 y (hS hy)).symm)
      · -- `|Z| ∈ {5, 6}`: count the arcs from `Z` into `Q = O ∖ Z`
        set Q := O \ Z with hQ
        have cQ : Q.card + Z.card = 7 := by
          rw [hQ, Finset.card_sdiff_of_subset hZO, cO]; have := Finset.card_le_card hZO; omega
        have hQsub : Q ⊆ Finset.range 22 := Finset.sdiff_subset.trans subO
        have inQ : ∀ q ∈ Q, ic G Z q + ic G Q q = 2 := by
          intro q hq
          rw [← regI q (Finset.mem_sdiff.mp hq).1, ic_sdiff (G := G) hZO q]
        have s1 := Finset.sum_congr rfl inQ
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at s1
        have pvQ : ∀ q ∈ Q, oc G Q q + ic G Q q + 1 ≤ Q.card := fun q hq =>
          oc_ic_le_mem H.loopless H.noShort hQsub hq
        have s2 := Finset.sum_le_sum pvQ
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← swap G Q Q, Finset.sum_const, Finset.sum_const,
          smul_eq_mul, smul_eq_mul, mul_one] at s2
        have s3 : ∑ q ∈ Q, ic G Z q = ∑ z ∈ Z, oc G Q z := (swap G Z Q).symm
        have hZY : Y ⊆ Z := hYZ
        have s4 : ∑ z ∈ Z, oc G Q z = ∑ z ∈ Z \ Y, oc G Q z := by
          rw [← Finset.sum_sdiff hZY]
          have : ∑ z ∈ Y, oc G Q z = 0 := Finset.sum_eq_zero (fun y hy => oc_eq_zero (fun q hq => by
            cases h : G y q
            · rfl
            · exact absurd (hYZh y hy q (Finset.mem_sdiff.mp hq).1 h) (Finset.mem_sdiff.mp hq).2))
          omega
        have s5 : ∑ z ∈ Z \ Y, oc G Q z ≤ (Z \ Y).card * 2 :=
          sum_le_card_mul (fun z hz => by
            rw [← regO z (hZO (Finset.mem_sdiff.mp hz).1)]
            exact oc_mono Finset.sdiff_subset z)
        have s6 : ∑ z ∈ Z \ Y, oc G Q z ≤ (Z \ Y).card * Q.card := sum_le_card_mul (fun z _ => oc_le Q z)
        have cZY : (Z \ Y).card + Y.card = Z.card := by
          rw [Finset.card_sdiff_of_subset hZY]; have := Finset.card_le_card hZY; omega
        have hQ12 : Q.card = 1 ∨ Q.card = 2 := by omega
        have hZY1 : (Z \ Y).card = 0 ∨ (Z \ Y).card = 1 := by omega
        have s6' : ∑ z ∈ Z \ Y, oc G Q z ≤ Q.card := le_trans s6 (by
          calc (Z \ Y).card * Q.card ≤ 1 * Q.card := Nat.mul_le_mul_right _ (by omega)
            _ = Q.card := one_mul _)
        have s7 : ∑ q ∈ Q, ic G Q q = ∑ q ∈ Q, oc G Q q := (swap G Q Q).symm
        rcases hQ12 with h | h <;> rw [h] at s1 s2 s6' <;> omega
    · rw [if_neg hpos]
      omega
  have hsumZ : ∑ m ∈ M, (O.filter (fun x => G x m = false)).card = 7 := by
    have : ∀ m ∈ M, (O.filter (fun x => G x m = false)).card + ic G O m = 7 := by
      intro m _
      have := Finset.card_filter_add_card_filter_not (s := O) (fun x => G x m = true)
      rw [cO] at this
      have e : (O.filter (fun x => ¬ G x m = true)) = O.filter (fun x => G x m = false) := by
        congr 1; ext x; simp
      rw [e] at this
      unfold ic
      omega
    have h1 := Finset.sum_congr rfl this
    rw [Finset.sum_add_distrib, Finset.sum_const, cM, smul_eq_mul, ← swap G O M,
      Finset.sum_congr rfl ocM, Finset.sum_const, cO, smul_eq_mul] at h1
    omega
  have T1 := Finset.sum_le_sum (fun m hm => (rowY m hm).1)
  have T2 := Finset.sum_le_sum (fun m hm => (rowY m hm).2)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumZ] at T1
  rw [← Finset.mul_sum] at T2
  omega

end LeanCH.BR.BR37
