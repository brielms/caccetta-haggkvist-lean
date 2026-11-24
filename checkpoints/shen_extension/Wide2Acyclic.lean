import checkpoints.shen_extension.Wide2Ring

/-!
# Layers `r`, `r + 2`, `r - 1`, `≤ r - 1` with `Y` acyclic, and the full shape

Take `F = X ∪ Y`. Rows of `X` keep all heads in `F`, rows of `Y` keep one head in `F`
because `|Z| = r - 1`. So `F` carries a closed walk and has a shortest cycle `C`
(`Wide2Ring.exists_ring`). It has length at least `q + 1 = r + 2`, meets `X` (as `Y` is
acyclic), and is chordless, so a row of `X ∩ C` (a full `C` row) has `r - 1` heads in
`A = F \ C`; thus `|C| ∈ {r + 2, r + 3}`. Let `m = |X ∩ C|`.

The windows: a row of `F` headed by a row of `C` has at most two heads on `C`, and a row
of `F` with a head on `C` has at most two parents on `C`. An `A`-sink has a head on `C`.

* `|C| = r + 3`: full `C` rows head all of `A`. For `m ≥ 3` an `A`-sink has three
  parents on `C`. For `m ≤ 2` a sink of `X \ C` has at most `|A| - |X \ C|` heads in `A`
  and two on `C`.
* `|C| = r + 2`: full `C` rows omit at most one row of `A`. For `m ≤ 2` the same sink
  count works on the rows of `X \ C` headed by one full `C` row (`6 ≤ r`). For `m ≥ 3`
  each row of `A` with a head on `C` is omitted by `m - 2` full `C` rows, and omitters of
  distinct rows are distinct. For `m ≤ r - 2` the `r - m` rows of `X \ C` need
  `(r - m)(m - 2) ≤ m` (`7 ≤ r`). For `m ≥ r - 1` only one row `a*` of `A` has a head on
  `C`, it is the sink of `A`, and one of its `r - 3` omitters closes
  `c → b → a* → c* ⇝ c` within `q` (`7 ≤ r`).
-/

namespace LeanCH.BR.Wide2Acyclic
open Finset BRq2 BRq3 SinkReturnAncestors SinkDepthReturn WideLayerReturn TightWideBanks
  Wide2Cycle Wide2Ring

/-- **Case 2: `Y` acyclic.** -/
theorem acyclic_case_false {D : CH.Digraph} {V X Y Z W : Finset ℕ} {q r : ℕ}
    (w : Wide2 D V X Y Z W q r) (seven : 7 ≤ r) (acyc : QFree D Y (r + 2)) : False := by
  classical
  have hq := w.hq
  have cx := w.cx
  have cz := w.cz
  obtain ⟨F, hF⟩ : ∃ F, F = X ∪ Y := ⟨_, rfl⟩
  have fv : F ⊆ V := by rw [hF]; exact union_subset w.xv w.yv
  have xF : X ⊆ F := by rw [hF]; exact subset_union_left
  have cF : F.card ≤ 2 * r + 2 := by rw [hF]; have := card_union_le X Y; have := w.cy; omega
  have headsXF (x) (xm : x ∈ X) : outN D V x ⊆ F := by rw [hF]; exact w.headsX x xm
  have rowF (v) (vm : v ∈ F) : ∃ u ∈ F, D v u = true := by
    have vm' := vm
    rw [hF] at vm'
    rcases mem_union.mp vm' with vx | vy
    · obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (outN D V v).card by have := w.degX v vx; omega)
      exact ⟨u, headsXF v vx hu, (mem_outN.mp hu).2⟩
    · by_contra! none
      have sub : outN D V v ⊆ Z := by
        intro u hu
        have arc := (mem_outN.mp hu).2
        rcases mem_union.mp (w.headsY v vy hu) with uxy | uz
        · exact (none u (by rw [hF]; exact uxy) arc).elim
        · exact uz
      have := card_le_card sub
      have := w.degY v vy
      omega
  have Xne : X.Nonempty := card_pos.mp (by omega)
  -- `F` carries a closed walk, hence a shortest cycle `C`
  obtain ⟨a₀, ℓ, h1, -, cyc⟩ : ∃ a ℓ, 1 ≤ ℓ ∧ ℓ ≤ F.card ∧ Walk D F a a ℓ := by
    by_contra! none
    obtain ⟨σ, σm, stop⟩ := exists_sink (fun a ℓ h1 hl walk => none a ℓ h1 hl walk)
      (Xne.mono xF) le_rfl
    obtain ⟨u, um, arc⟩ := rowF σ σm
    exact stop u um arc
  obtain ⟨C, R⟩ := exists_ring h1 cyc
  obtain ⟨c₀, c₀m⟩ := card_pos.mp (show 0 < C.card by have := R.pos; omega)
  have long : r + 2 ≤ C.card := by
    obtain ⟨g, g0, ge, gL, -⟩ := R.rot c₀ c₀m
    have wk := Ring.walk (R := R) ge (Nat.zero_le C.card) le_rfl
    rw [g0, gL, Nat.sub_zero] at wk
    by_contra! sh
    exact w.free c₀ C.card R.pos (by omega) (wk.mono fv)
  have three : 3 ≤ C.card := by omega
  -- `C` meets `X`
  obtain ⟨c₁, c₁C, c₁X⟩ : ∃ c ∈ C, c ∈ X := by
    by_contra! none
    have cY : C ⊆ Y := fun c cm => by
      have := R.sub cm
      rw [hF] at this
      rcases mem_union.mp this with h | h
      · exact (none c cm h).elim
      · exact h
    obtain ⟨g, g0, ge, gL, -⟩ := R.rot c₀ c₀m
    have wk := walk_between ge (Nat.zero_le C.card) le_rfl
    rw [g0, gL, Nat.sub_zero] at wk
    have := card_le_card cY
    have := w.cy
    exact acyc c₀ C.card R.pos (by omega) (wk.mono cY)
  obtain ⟨A, hA⟩ : ∃ A, A = F \ C := ⟨_, rfl⟩
  have cA : A.card + C.card = F.card := by
    rw [hA, card_sdiff_of_subset R.sub]; have := card_le_card R.sub; omega
  have aF : A ⊆ F := by rw [hA]; exact sdiff_subset
  have av : A ⊆ V := aF.trans fv
  have FCA (u) (um : u ∈ F) : u ∈ C ∨ u ∈ A := by
    by_cases h : u ∈ C
    · exact Or.inl h
    · right; rw [hA]; exact mem_sdiff.mpr ⟨um, h⟩
  have XCA (a) (ha : a ∈ X \ C) : a ∈ A := by
    obtain ⟨ax, ac⟩ := mem_sdiff.mp ha
    rw [hA]; exact mem_sdiff.mpr ⟨xF ax, ac⟩
  -- a full `C` row has `r - 1` heads in `A`
  have fullC (c) (cm : c ∈ C) (cX : c ∈ X) : r ≤ 1 + (outN D A c).card := by
    have split : outN D V c ⊆ outN D C c ∪ outN D A c := by
      intro u hu
      have arc := (mem_outN.mp hu).2
      rcases FCA u (headsXF c cX hu) with uc | ua
      · exact mem_union_left _ (mem_outN.mpr ⟨uc, arc⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨ua, arc⟩)
    have := (card_le_card split).trans (card_union_le _ _)
    have := ring_heads R (by omega) cm
    have := w.degX c cX
    omega
  have shortL : C.card ≤ r + 3 := by
    have := fullC c₁ c₁C c₁X
    have := card_le_card (outN_subset (D := D) (W := A) (y := c₁))
    omega
  have Asize : A.card ≤ r := by omega
  have Abig : r - 1 ≤ A.card := by
    have := fullC c₁ c₁C c₁X
    have := card_le_card (outN_subset (D := D) (W := A) (y := c₁))
    omega
  have fA : QFree D A q := w.free.mono_set av
  have sA : A.card ≤ q := by omega
  have Ane : A.Nonempty := card_pos.mp (by omega)
  -- an `A`-sink has a head on `C`
  have sinkC (σ) (σm : σ ∈ A) (kσ : Sink D A σ) : ∃ c ∈ C, D σ c = true := by
    obtain ⟨u, um, arc⟩ := rowF σ (aF σm)
    rcases FCA u um with uc | ua
    · exact ⟨u, uc, arc⟩
    · exact (kσ u ua arc).elim
  -- a sink of rows of `X \ C` all headed by one `C` row
  have sinkB (S : Finset ℕ) (Ssub : S ⊆ X \ C) (Sne : S.Nonempty) (c) (cm : c ∈ C)
      (cS : ∀ a ∈ S, D c a = true) : r + S.card ≤ 2 + A.card := by
    have SX : S ⊆ X := Ssub.trans sdiff_subset
    have SA : S ⊆ A := fun s hs => XCA s (Ssub hs)
    obtain ⟨σ, σm, stop⟩ := exists_sink (w.free.mono_set (SX.trans w.xv)) Sne
      (by have := card_le_card SX; omega)
    have sub : outN D V σ ⊆ outN D C σ ∪ outN D (A \ S) σ := by
      intro u hu
      have arc := (mem_outN.mp hu).2
      rcases FCA u (headsXF σ (SX σm) hu) with uc | ua
      · exact mem_union_left _ (mem_outN.mpr ⟨uc, arc⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨ua, fun us => stop u us arc⟩, arc⟩)
    have h₁ := (card_le_card sub).trans (card_union_le _ _)
    have h₂ := ring_children R three cm (aF (SA σm)) (cS σ σm)
    have h₃ := card_le_card (outN_subset (D := D) (W := A \ S) (y := σ))
    rw [card_sdiff_of_subset SA] at h₃
    have := w.degX σ (SX σm)
    have := card_le_card SA
    omega
  have XC : (X \ C).card + (X ∩ C).card = r := by rw [card_sdiff_add_card_inter]; exact cx
  have m1 : 1 ≤ (X ∩ C).card := card_pos.mpr ⟨c₁, mem_inter.mpr ⟨c₁X, c₁C⟩⟩
  rcases (show C.card = r + 3 ∨ C.card = r + 2 by omega) with L3 | L2
  · -- `|C| = r + 3`: full `C` rows head all of `A`
    have allA (c) (cm : c ∈ C) (cX : c ∈ X) (a) (am : a ∈ A) : D c a = true := by
      have eq := eq_of_subset_of_card_le (outN_subset (D := D) (W := A) (y := c))
        (by have := fullC c cm cX; omega)
      have : a ∈ outN D A c := by rw [eq]; exact am
      exact (mem_outN.mp this).2
    by_cases m3 : 3 ≤ (X ∩ C).card
    · obtain ⟨σ, σm, stop⟩ := exists_sink fA Ane sA
      obtain ⟨c', c'm, arc⟩ := sinkC σ σm (fun z zm => stop z zm)
      have par := ring_parents R c'm (aF σm) arc
      have sub : X ∩ C ⊆ C.filter (fun c => D c σ = true) := fun c hc =>
        mem_filter.mpr ⟨(mem_inter.mp hc).2, allA c (mem_inter.mp hc).2 (mem_inter.mp hc).1 σ σm⟩
      have := card_le_card sub
      omega
    · have ne : (X \ C).Nonempty := card_pos.mp (by omega)
      have := sinkB (X \ C) subset_rfl ne c₁ c₁C (fun a ha => allA c₁ c₁C c₁X a (XCA a ha))
      omega
  -- `|C| = r + 2`: full `C` rows omit at most one row of `A`
  have omit1 (c) (cm : c ∈ C) (cX : c ∈ X) : (A \ outN D V c).card ≤ 1 := by
    have sub : A \ outN D V c ⊆ A \ outN D A c := by
      intro a ha
      obtain ⟨am, an⟩ := mem_sdiff.mp ha
      exact mem_sdiff.mpr ⟨am, fun h => an (mem_outN.mpr ⟨av am, (mem_outN.mp h).2⟩)⟩
    have := card_le_card sub
    rw [card_sdiff_of_subset outN_subset] at this
    have := fullC c cm cX
    omega
  by_cases m2 : (X ∩ C).card ≤ 2
  · -- few full `C` rows (`6 ≤ r`)
    let S := (X \ C).filter (fun a => D c₁ a = true)
    have Ssub : S ⊆ X \ C := filter_subset _ _
    have rest : (X \ C) \ S ⊆ A \ outN D V c₁ := by
      intro a ha
      obtain ⟨am, aS⟩ := mem_sdiff.mp ha
      refine mem_sdiff.mpr ⟨XCA a am, fun h => aS (mem_filter.mpr ⟨am, (mem_outN.mp h).2⟩)⟩
    have h₁ := card_le_card rest
    rw [card_sdiff_of_subset Ssub] at h₁
    have h₂ := omit1 c₁ c₁C c₁X
    have ne : S.Nonempty := card_pos.mp (by omega)
    have := sinkB S Ssub ne c₁ c₁C (fun a ha => (mem_filter.mp ha).2)
    omega
  -- omitters
  let O : ℕ → Finset ℕ := fun a => (X ∩ C).filter (fun c => D c a ≠ true)
  have Odisj (a) (am : a ∈ A) (a') (a'm : a' ∈ A) (ne : a ≠ a') : Disjoint (O a) (O a') := by
    rw [disjoint_left]
    intro c hc hc'
    obtain ⟨cm', ca⟩ := mem_filter.mp hc
    obtain ⟨_, ca'⟩ := mem_filter.mp hc'
    have cmX := mem_inter.mp cm'
    exact ne (card_le_one.mp (omit1 c cmX.2 cmX.1) a
      (mem_sdiff.mpr ⟨am, fun h => ca (mem_outN.mp h).2⟩) a'
      (mem_sdiff.mpr ⟨a'm, fun h => ca' (mem_outN.mp h).2⟩))
  have Obig (a) (aF' : a ∈ F) (c') (c'm : c' ∈ C) (ac : D a c' = true) :
      (X ∩ C).card ≤ 2 + (O a).card := by
    have par := ring_parents R c'm aF' ac
    have sub : X ∩ C ⊆ C.filter (fun c => D c a = true) ∪ O a := by
      intro c hc
      by_cases h : D c a = true
      · exact mem_union_left _ (mem_filter.mpr ⟨(mem_inter.mp hc).2, h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hc, h⟩)
    have := (card_le_card sub).trans (card_union_le _ _)
    omega
  let Hd := A.filter (fun a => ∃ c ∈ C, D a c = true)
  have count : Hd.card * ((X ∩ C).card - 2) ≤ (X ∩ C).card := by
    have bu : (Hd.biUnion O).card = ∑ a ∈ Hd, (O a).card :=
      card_biUnion (fun a ha a' ha' ne => Odisj a (mem_filter.mp ha).1 a' (mem_filter.mp ha').1 ne)
    have sub : Hd.biUnion O ⊆ X ∩ C := biUnion_subset.mpr (fun a _ => filter_subset _ _)
    have lower : Hd.card • ((X ∩ C).card - 2) ≤ ∑ a ∈ Hd, (O a).card :=
      card_nsmul_le_sum Hd (fun a => (O a).card) ((X ∩ C).card - 2) (fun a ha => by
        obtain ⟨am, c', c'm, ac⟩ := mem_filter.mp ha
        have := Obig a (aF am) c' c'm ac
        omega)
    rw [smul_eq_mul] at lower
    have := card_le_card sub
    omega
  -- rows of `X \ C` have a head on `C`
  have fullHd : X \ C ⊆ Hd := by
    intro a ha
    have am := XCA a ha
    refine mem_filter.mpr ⟨am, ?_⟩
    by_contra! none
    have sub : outN D V a ⊆ A.erase a := by
      intro u hu
      have arc := (mem_outN.mp hu).2
      rcases FCA u (headsXF a (mem_sdiff.mp ha).1 hu) with uc | ua
      · exact (none u uc arc).elim
      · exact mem_erase.mpr ⟨fun e => loopfree w.free (by omega) (av am) (e ▸ arc), ua⟩
    have := card_le_card sub
    rw [card_erase_of_mem am] at this
    have := w.degX a (mem_sdiff.mp ha).1
    omega
  have hd := card_le_card fullHd
  by_cases mid : (X ∩ C).card ≤ r - 2
  · -- `(r - m)(m - 2) ≤ m` (`7 ≤ r`)
    have prod := (Nat.mul_le_mul_right ((X ∩ C).card - 2) hd).trans count
    obtain ⟨u, hu⟩ : ∃ u, (X \ C).card = u + 2 := ⟨(X \ C).card - 2, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, (X ∩ C).card - 2 = v + 1 := ⟨(X ∩ C).card - 3, by omega⟩
    have mv : (X ∩ C).card = v + 3 := by omega
    rw [hu, hv, mv] at prod
    have e : (u + 2) * (v + 1) = u * v + u + 2 * v + 2 := by ring
    rw [e] at prod
    omega
  -- `m ≥ r - 1`: a single row of `A` heads `C` (`7 ≤ r`)
  have one : Hd.card ≤ 1 := by
    by_contra! two
    have := (Nat.mul_le_mul_right ((X ∩ C).card - 2) (show 2 ≤ Hd.card by omega)).trans count
    omega
  obtain ⟨as, asm, stop⟩ := exists_sink fA Ane sA
  have kas : Sink D A as := fun z zm => stop z zm
  obtain ⟨cs, csm, ascs⟩ := sinkC as asm kas
  have asHd : as ∈ Hd := mem_filter.mpr ⟨asm, cs, csm, ascs⟩
  obtain ⟨b₀, b₀m, b₀ne⟩ := exists_mem_ne (show 1 < A.card by omega) as
  obtain ⟨s, sm, stops, k, -, walk⟩ := reach_sink_of_card fA sA b₀m
  have se : s = as := by
    obtain ⟨c, cm, sc⟩ := sinkC s sm (fun z zm => stops z zm)
    exact card_le_one.mp one s (mem_filter.mpr ⟨sm, c, cm, sc⟩) as asHd
  subst se
  obtain ⟨b, bm, bs⟩ := last_parent b₀m walk b₀ne
  have bne : b ≠ s := fun e => loopfree w.free (by omega) (av bm) (e ▸ bs)
  have big := Obig s (aF sm) cs csm ascs
  have far : ∀ c ∈ O s, ∀ t, Walk D F cs c t → r - 1 ≤ t := by
    intro c hc t wk
    obtain ⟨cm', cs'⟩ := mem_filter.mp hc
    have cmX := mem_inter.mp cm'
    have cb : D c b = true := by
      by_contra no
      exact bne (card_le_one.mp (omit1 c cmX.2 cmX.1) b
        (mem_sdiff.mpr ⟨bm, fun h => no (mem_outN.mp h).2⟩) s
        (mem_sdiff.mpr ⟨sm, fun h => cs' (mem_outN.mp h).2⟩))
    by_contra! short
    exact w.free c (t + 1 + 1 + 1) (by omega) (by omega) (.step (av bm) cb (.step (av sm) bs
      (.step (fv (R.sub csm)) ascs (wk.mono fv))))
  have := ring_far R csm (S := O s) (filter_subset _ _ |>.trans inter_subset_right) far
  omega

/-- **The shape `r`, `r + 2`, `r - 1`, `≤ r - 1`.** Four consecutive layers of widths `r`,
`r + 2`, `r - 1` and at most `r - 1` are impossible at cutoff `q = r + 1` when `7 ≤ r`. -/
theorem wide2_false {D : CH.Digraph} {V X Y Z W : Finset ℕ} {q r : ℕ}
    (w : Wide2 D V X Y Z W q r) (seven : 7 ≤ r) : False := by
  by_cases acyc : QFree D Y (r + 2)
  · exact acyclic_case_false w seven acyc
  · exact cycle_case_false w (by omega) acyc

/-- **The shape `r`, `r + 2`, `r - 1`, `≤ r - 1`, unbundled.** -/
theorem wide2_layers_false {D : CH.Digraph} {V X Y Z W : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (xv : X ⊆ V) (yv : Y ⊆ V) (zv : Z ⊆ V)
    (cx : X.card = r) (cy : Y.card = r + 2) (cz : Z.card + 1 = r) (cw : W.card + 1 ≤ r)
    (seven : 7 ≤ r) (hq : q = r + 1)
    (degX : ∀ x ∈ X, r ≤ (outN D V x).card) (degY : ∀ y ∈ Y, r ≤ (outN D V y).card)
    (degZ : ∀ z ∈ Z, r ≤ (outN D V z).card)
    (headsX : ∀ x ∈ X, outN D V x ⊆ X ∪ Y) (headsY : ∀ y ∈ Y, outN D V y ⊆ X ∪ Y ∪ Z)
    (headsZ : ∀ z ∈ Z, outN D V z ⊆ X ∪ Y ∪ Z ∪ W) : False :=
  wide2_false ⟨free, xv, yv, zv, cx, cy, cz, cw, hq, degX, degY, degZ, headsX, headsY, headsZ⟩
    seven

#print axioms acyclic_case_false
#print axioms wide2_false
#print axioms wide2_layers_false

end LeanCH.BR.Wide2Acyclic
