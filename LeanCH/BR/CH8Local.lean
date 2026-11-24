import LeanCH.BR.BR37

/-!
# CH(8) on at most 24 vertices, part 1: saturated boundary graphs without an in-degree cap (Lean 4.35.0)

Paper sources: `checkpoints/boundary_20261111/BR38_attempt_subagent.md` (Lemmas 1, 2, 5, 6, 7, 12) with
`BR38_audit_subagent.md`, and `Z8_attempt_subagent.md` (Corollary 7) with `Z8_audit_subagent.md`.

`SatHyp s G`: `3s+1` labels, loopless, minimum out-degree `s`, no cycle of length `≤ 3`, saturated in the two-path
form. Unlike `BR36.SHyp` there is **no** in-degree cap: at `s = 8` the strict cap allows in-degree `s + 2`.

* The cap-free part of `BR36Root` (Lemmas 1, 2 of the `s = 7` note), restated for `SatHyp`: the partition at a
  vertex, `O_noI`, `outO`, `lemma51`, `am_pos`, `noMH`, `K_par`, `K_in`, `K_out`.
* `H_out`: an `H`-vertex of `u` has out-degree at least `out(u) + 1` (out-degree half of Lemma 5 of the `s = 8`
  note).
* `K_priv`: `K`-sets of two distinct vertices of equal out-degree are disjoint (Lemma 6 of the `s = 8` note with the
  out-degree half of Lemma 5; this is Prop 10(c) there).
* `H_recv`: if `η ∈ H(v)` for every `v` of a nonempty set `U` and `in(v) ≤ out(v) + d` on `U`, then
  `in(η) + |U| + 1 ≤ out(η) + d`. With `d = 2` this is the multiplicity bound `E(η) ≥ |U| - 1` of Lemma 7 (family
  bound) for a family of depth-2 roots, proved as in `BR36Root.lemma5` (one member with `out_U ≤ in_U`).
* `low_K`: at a vertex with `out(u) = s ≤ 9` and `|M(u)| = s - 2`, some `x ∈ K(u)` has out-degree exactly `s`
  (Lemma 12 of the `s = 8` note, in the weak form "one `L`-vertex"; only `BR(3,3)` is used).
-/

set_option linter.unusedSectionVars false

namespace LeanCH.BR.CH8

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of
open LeanCH.BR.BR36

/-- A saturated boundary graph at `s`, with no in-degree cap. -/
structure SatHyp (s : Nat) (G : CH.Digraph) : Prop where
  loopless : CH.Loopless G (3 * s + 1)
  deg : CH.MinOutdegreeAtLeast G (3 * s + 1) s
  noShort : ¬ CH.HasDirectedCycleAtMost G (3 * s + 1) 3
  sat : ∀ a b, a < 3 * s + 1 → b < 3 * s + 1 → a ≠ b → G a b = false → G b a = false →
    ∃ z, z < 3 * s + 1 ∧ G a z = true ∧ G z b = true

namespace SatHyp

variable {s : Nat} {G : CH.Digraph} (H : SatHyp s G)
include H

theorem n2 {a b : Nat} (ha : a < 3 * s + 1) (hb : b < 3 * s + 1) (h1 : G a b = true) (h2 : G b a = true) :
    False :=
  no2 H.loopless H.noShort ha hb h1 h2

theorem n3 {a b c : Nat} (ha : a < 3 * s + 1) (hb : b < 3 * s + 1) (hc : c < 3 * s + 1)
    (h1 : G a b = true) (h2 : G b c = true) (h3 : G c a = true) : False :=
  no3 H.loopless H.noShort ha hb hc h1 h2 h3

theorem out {w : Nat} (hw : w < 3 * s + 1) : s ≤ oc G (VS s) w := out_card H.deg hw

theorem tri {a b c : Nat} (ha : a < 3 * s + 1) (hb : b < 3 * s + 1) (hc : c < 3 * s + 1) (h1 : G a b = true)
    (h2 : G b c = true) : G c a = false := by
  cases h' : G c a
  · rfl
  · exact (H.n3 ha hb hc h1 h2 h').elim

theorem back {a b : Nat} (ha : a < 3 * s + 1) (hb : b < 3 * s + 1) (h : G a b = true) : G b a = false := by
  cases h' : G b a
  · rfl
  · exact (H.n2 ha hb h h').elim

variable {u : Nat}

theorem ltI {w : Nat} (h : w ∈ II G s u) : w < 3 * s + 1 := (mem_II.mp h).1
theorem ltO {w : Nat} (h : w ∈ OO G s u) : w < 3 * s + 1 := (mem_OO.mp h).1
theorem ltM {w : Nat} (h : w ∈ MM G s u) : w < 3 * s + 1 := (mem_MM.mp h).1
theorem subO : OO G s u ⊆ Finset.range (3 * s + 1) := fun _ h => Finset.mem_range.mpr (H.ltO h)

theorem uI (hu : u < 3 * s + 1) : u ∉ II G s u := fun h => by
  have := (mem_II.mp h).2; rw [H.loopless u hu] at this; exact Bool.false_ne_true this

theorem uO (hu : u < 3 * s + 1) : u ∉ OO G s u := fun h => by
  have := (mem_OO.mp h).2; rw [H.loopless u hu] at this; exact Bool.false_ne_true this

theorem uM : u ∉ MM G s u := fun h => (mem_MM.mp h).2.1 rfl

theorem dIO (hu : u < 3 * s + 1) : Disjoint (II G s u) (OO G s u) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact H.n2 (H.ltI h1) hu (mem_II.mp h1).2 (mem_OO.mp h2).2

theorem dIM : Disjoint (II G s u) (MM G s u) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := (mem_II.mp h1).2; rw [(mem_MM.mp h2).2.2.1] at this; exact Bool.false_ne_true this

theorem dOM : Disjoint (OO G s u) (MM G s u) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := (mem_OO.mp h1).2; rw [(mem_MM.mp h2).2.2.2] at this; exact Bool.false_ne_true this

theorem V_eq (hu : u < 3 * s + 1) : VS s = insert u (II G s u ∪ OO G s u ∪ MM G s u) := by
  ext v
  simp only [mem_VS, Finset.mem_insert, Finset.mem_union, mem_II, mem_OO, mem_MM]
  constructor
  · intro hv
    by_cases h1 : v = u
    · exact Or.inl h1
    right
    cases h2 : G v u
    · cases h3 : G u v
      · exact Or.inr ⟨hv, h1, rfl, rfl⟩
      · exact Or.inl (Or.inr ⟨hv, rfl⟩)
    · exact Or.inl (Or.inl ⟨hv, rfl⟩)
  · rintro (rfl | (h | h) | h)
    · exact hu
    · exact h.1
    · exact h.1
    · exact h.1

theorem sumV (hu : u < 3 * s + 1) (f : Nat → Nat) :
    ∑ v ∈ VS s, f v = f u + ∑ v ∈ II G s u, f v + ∑ v ∈ OO G s u, f v + ∑ v ∈ MM G s u, f v := by
  have hun : u ∉ II G s u ∪ OO G s u ∪ MM G s u := by
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨H.uI hu, H.uO hu⟩, H.uM⟩
  rw [H.V_eq hu, Finset.sum_insert hun,
    Finset.sum_union (Finset.disjoint_union_left.mpr ⟨H.dIM, H.dOM⟩), Finset.sum_union (H.dIO hu)]
  omega

theorem part (hu : u < 3 * s + 1) (p : Nat → Prop) [DecidablePred p] :
    ((VS s).filter p).card =
      (if p u then 1 else 0) + ((II G s u).filter p).card + ((OO G s u).filter p).card +
        ((MM G s u).filter p).card := by
  rw [Finset.card_filter, H.sumV hu, Finset.card_filter, Finset.card_filter, Finset.card_filter]

theorem cM (hu : u < 3 * s + 1) :
    (MM G s u).card + ic G (VS s) u + oc G (VS s) u + 1 = 3 * s + 1 := by
  have h := H.part hu (fun _ => True)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial), ite_true] at h
  rw [card_II, card_OO] at h
  have : (VS s).card = 3 * s + 1 := by simp [VS]
  omega

theorem split_out (hu : u < 3 * s + 1) (w : Nat) :
    oc G (VS s) w = (if G w u = true then 1 else 0) + oc G (II G s u) w + oc G (OO G s u) w +
      oc G (MM G s u) w :=
  H.part hu (fun v => G w v = true)

theorem split_in (hu : u < 3 * s + 1) (w : Nat) :
    ic G (VS s) w = (if G u w = true then 1 else 0) + ic G (II G s u) w + ic G (OO G s u) w +
      ic G (MM G s u) w :=
  H.part hu (fun v => G v w = true)

/-- Lemma 1: an out-neighbour of `u` heads no in-neighbour of `u`. -/
theorem O_noI (hu : u < 3 * s + 1) {x w : Nat} (hx : x ∈ OO G s u) (hw : w ∈ II G s u) : G x w = false := by
  cases h : G x w
  · rfl
  · exact (H.n3 hu (H.ltO hx) (H.ltI hw) (mem_OO.mp hx).2 h (mem_II.mp hw).2).elim

theorem O_nou (hu : u < 3 * s + 1) {x : Nat} (hx : x ∈ OO G s u) : G x u = false :=
  H.back hu (H.ltO hx) (mem_OO.mp hx).2

theorem outO (hu : u < 3 * s + 1) {x : Nat} (hx : x ∈ OO G s u) :
    oc G (VS s) x = oc G (OO G s u) x + oc G (MM G s u) x := by
  rw [H.split_out hu x, H.O_nou hu hx, oc_eq_zero (fun w hw => H.O_noI hu hx hw)]
  simp

/-- If `w ∈ I(u)` misses `x ∈ O(u)`, some row `m` has `x → m → w` (saturation). -/
theorem lemma51 (hu : u < 3 * s + 1) {w x : Nat} (hw : w ∈ II G s u) (hx : x ∈ OO G s u)
    (hwx : G w x = false) : ∃ m ∈ MM G s u, G x m = true ∧ G m w = true := by
  have hne : x ≠ w := by
    rintro rfl; exact Finset.disjoint_left.mp (H.dIO hu) hw hx
  obtain ⟨z, hz, h1, h2⟩ := H.sat x w (H.ltO hx) (H.ltI hw) hne (H.O_noI hu hx hw) hwx
  refine ⟨z, ?_, h1, h2⟩
  have hzV : z ∈ insert u (II G s u ∪ OO G s u ∪ MM G s u) := H.V_eq hu ▸ mem_VS.mpr hz
  rcases Finset.mem_insert.mp hzV with h | h
  · rw [h, H.O_nou hu hx] at h1; exact absurd h1 Bool.false_ne_true
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rw [H.O_noI hu hx h] at h1; exact absurd h1 Bool.false_ne_true
    · rw [H.O_noI hu h hw] at h2; exact absurd h2 Bool.false_ne_true
  · exact h

/-- Lemma 2(a): every row is headed by a vertex of `O(u)`. -/
theorem am_pos (hu : u < 3 * s + 1) {m : Nat} (hm : m ∈ MM G s u) : ∃ a ∈ OO G s u, G a m = true := by
  obtain ⟨hmn, hmu, h1, h2⟩ := mem_MM.mp hm
  obtain ⟨z, hz, g1, g2⟩ := H.sat u m hu hmn (Ne.symm hmu) h2 h1
  exact ⟨z, mem_OO.mpr ⟨hz, g1⟩, g2⟩

/-- Lemma 2(b): rows do not head `H(u)`. -/
theorem noMH (hu : u < 3 * s + 1) {m η : Nat} (hm : m ∈ MM G s u) (hη : η ∈ HS G s u) : G m η = false := by
  cases hmη : G m η
  · rfl
  · exfalso
    obtain ⟨a, ha, ham⟩ := H.am_pos hu hm
    rw [H.tri (H.ltM hm) (H.ltI (HS_sub hη)) (H.ltO ha) hmη (HS_all hη a ha)] at ham
    exact Bool.false_ne_true ham

/-- Lemma 2(c): a vertex of `K(u)` is headed only by `u`, vertices of `O(u)` and vertices of `H(u)`. -/
theorem K_par (hu : u < 3 * s + 1) {x w : Nat} (hx : x ∈ KS G s u) (hw : w < 3 * s + 1) (hwx : G w x = true) :
    w = u ∨ w ∈ OO G s u ∨ w ∈ HS G s u := by
  have hxO := KS_sub hx
  have hwV : w ∈ insert u (II G s u ∪ OO G s u ∪ MM G s u) := H.V_eq hu ▸ mem_VS.mpr hw
  rcases Finset.mem_insert.mp hwV with h | h
  · exact Or.inl h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · right; right
      refine Finset.mem_filter.mpr ⟨h, fun y hy => ?_⟩
      by_contra hwy
      obtain ⟨m, hm, _, hmw⟩ := H.lemma51 hu h hy (by simpa using hwy)
      exact H.n3 (H.ltM hm) (H.ltI h) (H.ltO hxO) hmw hwx (KS_all hx m hm)
    · exact Or.inr (Or.inl h)
  · exact (H.n2 (H.ltO hxO) hw (KS_all hx w h) hwx).elim

/-- Lemma 2(c): `in(x) = 1 + in_O(x) + h(u)` for `x ∈ K(u)`. -/
theorem K_in (hu : u < 3 * s + 1) {x : Nat} (hx : x ∈ KS G s u) :
    ic G (VS s) x = 1 + ic G (OO G s u) x + (HS G s u).card := by
  have hxO := KS_sub hx
  rw [H.split_in hu x, (mem_OO.mp hxO).2]
  have h1 : ic G (MM G s u) x = 0 := ic_eq_zero (fun m hm => H.back (H.ltO hxO) (H.ltM hm) (KS_all hx m hm))
  have h2 : ic G (II G s u) x = (HS G s u).card := by
    unfold ic
    congr 1
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hwI, hwx⟩
      rcases H.K_par hu hx (H.ltI hwI) hwx with h | h | h
      · exact absurd (h ▸ hwI) (H.uI hu)
      · exact absurd h (Finset.disjoint_left.mp (H.dIO hu) hwI)
      · exact h
    · intro hw
      exact ⟨HS_sub hw, HS_all hw x hxO⟩
  rw [h1, h2]
  simp
  omega

theorem K_out (hu : u < 3 * s + 1) {x : Nat} (hx : x ∈ KS G s u) :
    oc G (VS s) x = oc G (OO G s u) x + (MM G s u).card := by
  rw [H.outO hu (KS_sub hx), oc_full (KS_all hx)]

/-! ### New lemmas for `s = 8` (no in-degree cap) -/

/-- An `H`-vertex of `u` heads `u` and all of `O(u)`: `out(w) ≥ out(u) + 1`. -/
theorem H_out (hu : u < 3 * s + 1) {w : Nat} (hw : w ∈ HS G s u) :
    oc G (VS s) u + 1 ≤ oc G (VS s) w := by
  have hsub : insert u (OO G s u) ⊆ (VS s).filter (fun y => G w y = true) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_filter.mpr ⟨mem_VS.mpr hu, (mem_II.mp (HS_sub hw)).2⟩
    · exact Finset.mem_filter.mpr ⟨mem_VS.mpr (H.ltO hy), HS_all hw y hy⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (H.uO hu), card_OO] at h1
  exact h1

/-- **`K`-privacy.** Two distinct vertices of equal out-degree share no `K`-vertex. -/
theorem K_priv {u' x : Nat} (hu : u < 3 * s + 1) (hu' : u' < 3 * s + 1) (hne : u ≠ u')
    (hout : oc G (VS s) u = oc G (VS s) u') (hx : x ∈ KS G s u) (hx' : x ∈ KS G s u') : False := by
  have hux : G u x = true := (mem_OO.mp (KS_sub hx)).2
  have hu'x : G u' x = true := (mem_OO.mp (KS_sub hx')).2
  have a1 : G u' u = true := by
    rcases H.K_par hu' hx' hu hux with h | h | h
    · exact absurd h hne
    · exact (mem_OO.mp h).2
    · have := H.H_out hu' h; omega
  have a2 : G u u' = true := by
    rcases H.K_par hu hx hu' hu'x with h | h | h
    · exact absurd h.symm hne
    · exact (mem_OO.mp h).2
    · have := H.H_out hu h; omega
  exact H.n2 hu hu' a2 a1

/-- **`H`-multiplicity.** If `η ∈ H(v)` for every `v` of a nonempty set `U` with `in(v) ≤ out(v) + d`, then
`in(η) + |U| + 1 ≤ out(η) + d`. -/
theorem H_recv {η d : Nat} {U : Finset Nat} (hη : η < 3 * s + 1) (hne : U.Nonempty)
    (hU : ∀ v ∈ U, v < 3 * s + 1 ∧ η ∈ HS G s v ∧ ic G (VS s) v ≤ oc G (VS s) v + d) :
    ic G (VS s) η + U.card + 1 ≤ oc G (VS s) η + d := by
  classical
  have hηv : ∀ v ∈ U, G η v = true := fun v hv => (mem_II.mp (HS_sub (hU v hv).2.1)).2
  -- out-bound at each member: `O(v) ∪ U ⊆ O(η)`
  have outb : ∀ v ∈ U, oc G (VS s) v + U.card ≤ oc G (VS s) η + oc G U v := by
    intro v hv
    have hsub : OO G s v ∪ U ⊆ (VS s).filter (fun y => G η y = true) := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_filter.mpr ⟨mem_VS.mpr (H.ltO hy), HS_all (hU v hv).2.1 y hy⟩
      · exact Finset.mem_filter.mpr ⟨mem_VS.mpr (hU y hy).1, hηv y hy⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_add_card_inter (OO G s v) U
    have h3 : (OO G s v ∩ U).card ≤ oc G U v := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_inter.mp hy
      exact Finset.mem_filter.mpr ⟨hy2, (mem_OO.mp hy1).2⟩
    rw [card_OO] at h2
    change Finset.card _ ≤ oc G (VS s) η at h1
    omega
  -- in-bound at each member: `I(η) ⊆ (I(v) ∖ U) ∖ {η}`
  have inb : ∀ v ∈ U, ic G (VS s) η + ic G U v + 1 ≤ ic G (VS s) v := by
    intro v hv
    have hv' := (hU v hv).1
    have hηH := (hU v hv).2.1
    have hηI := HS_sub hηH
    have hηU : η ∉ U := fun h => by
      have := hηv η h; rw [H.loopless η hη] at this; exact Bool.false_ne_true this
    have hsub : (VS s).filter (fun y => G y η = true) ⊆ (II G s v \ U).erase η := by
      intro y hy
      obtain ⟨hyV, hyη⟩ := Finset.mem_filter.mp hy
      have hy' := mem_VS.mp hyV
      refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_sdiff.mpr ⟨?_, fun hyU => ?_⟩⟩
      · rw [h, H.loopless η hη] at hyη; exact Bool.false_ne_true hyη
      · have hyV' : y ∈ insert v (II G s v ∪ OO G s v ∪ MM G s v) := H.V_eq hv' ▸ hyV
        rcases Finset.mem_insert.mp hyV' with h | h
        · rw [h] at hyη; exact (H.n2 hη hv' (hηv v hv) hyη).elim
        rcases Finset.mem_union.mp h with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact h
          · rw [H.O_noI hv' h hηI] at hyη; exact absurd hyη Bool.false_ne_true
        · rw [H.noMH hv' h hηH] at hyη; exact absurd hyη Bool.false_ne_true
      · exact H.n2 hη hy' (hηv y hyU) hyη
    have h1 := Finset.card_le_card hsub
    have hmem : η ∈ II G s v \ U := Finset.mem_sdiff.mpr ⟨hηI, hηU⟩
    rw [Finset.card_erase_of_mem hmem] at h1
    have h2 : ic G U v ≤ (II G s v ∩ U).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨hyU, hyv⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_inter.mpr ⟨mem_II.mpr ⟨(hU y hyU).1, hyv⟩, hyU⟩
    have h3 := Finset.card_sdiff_add_card_inter (II G s v) U
    have h4 : (II G s v).card = ic G (VS s) v := card_II
    have h5 : ((VS s).filter (fun y => G y η = true)).card = ic G (VS s) η := rfl
    have h6 : 1 ≤ (II G s v \ U).card := Finset.card_pos.mpr ⟨η, hmem⟩
    omega
  -- a member with `out_U ≤ in_U`
  have hsw : ∑ v ∈ U, oc G U v ≤ ∑ v ∈ U, ic G U v := le_of_eq (swap G U U)
  obtain ⟨v0, hv0, hle⟩ := Finset.exists_le_of_sum_le hne hsw
  have o0 := outb v0 hv0
  have i0 := inb v0 hv0
  have d0 := (hU v0 hv0).2.2
  omega

/-- **One low `K`-vertex.** If `out(u) = s ≤ 9` and `|M(u)| = s - 2`, some `x ∈ K(u)` has out-degree `s`:
`D[O(u)]` has minimum out-degree `2`, and `BR(3,3)` forbids minimum out-degree `3` on `s ≤ 9` vertices. -/
theorem low_K (hu : u < 3 * s + 1) (hM : (MM G s u).card + 2 = s) (hO : oc G (VS s) u = s)
    (hs9 : s ≤ 9) : ∃ x ∈ KS G s u, oc G (VS s) x = s := by
  by_contra hcon
  push Not at hcon
  apply ch_subset (q := 3) (c := 3) (S := OO G s u) (by norm_num) LeanCH.BR.SmallBR.br_three H.subO
    (Finset.card_pos.mp (by rw [card_OO, hO]; omega)) (by rw [card_OO, hO]; omega) H.loopless H.noShort
  intro x hx
  have h1 := H.out (H.ltO hx)
  rw [H.outO hu hx] at h1
  have h2 := oc_le (G := G) (MM G s u) x
  by_contra hlt
  have hall : ∀ m ∈ MM G s u, G x m = true := all_of_oc (by omega)
  have hK : x ∈ KS G s u := Finset.mem_filter.mpr ⟨hx, hall⟩
  apply hcon x hK
  rw [H.outO hu hx, oc_full hall]
  omega

end SatHyp

end LeanCH.BR.CH8
