import LeanCH.BR.BR35Shape

/-!
# BR(3,6), part 1: the local setup at a vertex of in-degree 7 (Lean 4.35.0)

Paper sources: `checkpoints/boundary_20261111/BR36_attempt_subagent.md` (sections 1, 2, 5) and
`BR36_residual_subagent.md` (section 2), with the corrections of the two audits.

* `Hyp G`: a boundary graph at `s = 6` (19 labels, minimum out-degree 6, no cycle of length `≤ 3`), with the strict
  cap (`in ≤ 7`, and `in = 7 ⇒ out = 6`), and **saturated** in the two-path form: every non-adjacent pair `a, b` has
  a path `a → z → b`. (`BR36Reduce` shows this is no loss of generality.)
* `Root G u I O M`: `u` has in-degree 7 and out-degree 6; `I = I(u)`, `O = O(u)`, `M` = the 5 other labels.
* The degree splits of each class, the local facts (L1)-(L5), the saturation facts (`a_m ≥ 1`, Lemma 5.1 in the
  form `lemma51`, `M ↛ H`), and the **global identity** `global` (residual note, Lemma N2, exact form).

The counting tools `oc`, `ic` and their lemmas are the generic ones of `LeanCH.BR.BR35`.
-/

namespace LeanCH.BR.BR36

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of

/-- The 19 labels. -/
abbrev V : Finset Nat := Finset.range 19

/-- A saturated boundary graph at `s = 6` with the strict cap. -/
structure Hyp (G : CH.Digraph) : Prop where
  loopless : CH.Loopless G 19
  deg : CH.MinOutdegreeAtLeast G 19 6
  noShort : ¬ CH.HasDirectedCycleAtMost G 19 3
  cap : ∀ v, v < 19 → ic G V v ≤ 7
  cap7 : ∀ v, v < 19 → ic G V v = 7 → oc G V v = 6
  sat : ∀ a b, a < 19 → b < 19 → a ≠ b → G a b = false → G b a = false →
    ∃ z, z < 19 ∧ G a z = true ∧ G z b = true

namespace Hyp

variable {G : CH.Digraph} (H : Hyp G)
include H

theorem n2 {a b : Nat} (ha : a < 19) (hb : b < 19) (h1 : G a b = true) (h2 : G b a = true) : False :=
  no2 H.loopless H.noShort ha hb h1 h2

theorem n3 {a b c : Nat} (ha : a < 19) (hb : b < 19) (hc : c < 19)
    (h1 : G a b = true) (h2 : G b c = true) (h3 : G c a = true) : False :=
  no3 H.loopless H.noShort ha hb hc h1 h2 h3

theorem out {w : Nat} (hw : w < 19) : 6 ≤ oc G V w := out_card H.deg hw

theorem ne_of_arc {a b : Nat} (ha : a < 19) (h : G a b = true) : a ≠ b := by
  rintro rfl; rw [H.loopless a ha] at h; exact Bool.false_ne_true h

/-- `G c a = false` from `a → b → c` (no triangle). -/
theorem tri {a b c : Nat} (ha : a < 19) (hb : b < 19) (hc : c < 19) (h1 : G a b = true)
    (h2 : G b c = true) : G c a = false := by
  cases h' : G c a
  · rfl
  · exact (H.n3 ha hb hc h1 h2 h').elim

/-- `G b a = false` from `G a b = true` (no digon). -/
theorem back {a b : Nat} (ha : a < 19) (hb : b < 19) (h : G a b = true) : G b a = false := by
  cases h' : G b a
  · rfl
  · exact (H.n2 ha hb h h').elim

end Hyp

/-- The local picture at a vertex `u` of in-degree 7 and out-degree 6. -/
structure Root (G : CH.Digraph) (u : Nat) (I O M : Finset Nat) : Prop where
  H : Hyp G
  hu : u < 19
  mI : ∀ v, v ∈ I ↔ v < 19 ∧ G v u = true
  mO : ∀ v, v ∈ O ↔ v < 19 ∧ G u v = true
  mM : ∀ v, v ∈ M ↔ v < 19 ∧ v ≠ u ∧ G v u = false ∧ G u v = false
  cI : I.card = 7
  cO : O.card = 6

/-- The root structure at `u`, from in-degree 7. -/
theorem root_of {G : CH.Digraph} (H : Hyp G) {u : Nat} (hu : u < 19) (hin : ic G V u = 7) :
    Root G u (V.filter (fun v => G v u = true)) (V.filter (fun v => G u v = true))
      (V.filter (fun v => v ≠ u ∧ G v u = false ∧ G u v = false)) where
  H := H
  hu := hu
  mI := fun v => by simp [V]
  mO := fun v => by simp [V]
  mM := fun v => by simp [V]
  cI := hin
  cO := H.cap7 u hu hin

namespace Root

variable {G : CH.Digraph} {u : Nat} {I O M : Finset Nat} (R : Root G u I O M)
include R

theorem ltI {w : Nat} (h : w ∈ I) : w < 19 := ((R.mI w).mp h).1
theorem ltO {w : Nat} (h : w ∈ O) : w < 19 := ((R.mO w).mp h).1
theorem ltM {w : Nat} (h : w ∈ M) : w < 19 := ((R.mM w).mp h).1
theorem subI : I ⊆ Finset.range 19 := fun _ h => Finset.mem_range.mpr (R.ltI h)
theorem subO : O ⊆ Finset.range 19 := fun _ h => Finset.mem_range.mpr (R.ltO h)
theorem subM : M ⊆ Finset.range 19 := fun _ h => Finset.mem_range.mpr (R.ltM h)
theorem arcI {w : Nat} (h : w ∈ I) : G w u = true := ((R.mI w).mp h).2
theorem arcO {w : Nat} (h : w ∈ O) : G u w = true := ((R.mO w).mp h).2
theorem Mnu {m : Nat} (h : m ∈ M) : G m u = false := ((R.mM m).mp h).2.2.1
theorem Mun {m : Nat} (h : m ∈ M) : G u m = false := ((R.mM m).mp h).2.2.2

theorem uI : u ∉ I := fun h => by
  have := R.arcI h; rw [R.H.loopless u R.hu] at this; exact Bool.false_ne_true this

theorem uO : u ∉ O := fun h => by
  have := R.arcO h; rw [R.H.loopless u R.hu] at this; exact Bool.false_ne_true this

theorem uM : u ∉ M := fun h => ((R.mM u).mp h).2.1 rfl

theorem dIO : Disjoint I O := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact R.H.n2 (R.ltI h1) R.hu (R.arcI h1) (R.arcO h2)

theorem dIM : Disjoint I M := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := R.arcI h1; rw [R.Mnu h2] at this; exact Bool.false_ne_true this

theorem dOM : Disjoint O M := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := R.arcO h1; rw [R.Mun h2] at this; exact Bool.false_ne_true this

theorem neIO {w x : Nat} (hw : w ∈ I) (hx : x ∈ O) : w ≠ x := by
  rintro rfl; exact Finset.disjoint_left.mp R.dIO hw hx

theorem neIM {w x : Nat} (hw : w ∈ I) (hx : x ∈ M) : w ≠ x := by
  rintro rfl; exact Finset.disjoint_left.mp R.dIM hw hx

theorem neOM {w x : Nat} (hw : w ∈ O) (hx : x ∈ M) : w ≠ x := by
  rintro rfl; exact Finset.disjoint_left.mp R.dOM hw hx

theorem V_eq : V = insert u (I ∪ O ∪ M) := by
  ext v
  simp only [V, Finset.mem_range, Finset.mem_insert, Finset.mem_union]
  constructor
  · intro hv
    by_cases h1 : v = u
    · exact Or.inl h1
    right
    cases h2 : G v u
    · cases h3 : G u v
      · exact Or.inr ((R.mM v).mpr ⟨hv, h1, h2, h3⟩)
      · exact Or.inl (Or.inr ((R.mO v).mpr ⟨hv, h3⟩))
    · exact Or.inl (Or.inl ((R.mI v).mpr ⟨hv, h2⟩))
  · rintro (rfl | (h | h) | h)
    · exact R.hu
    · exact R.ltI h
    · exact R.ltO h
    · exact R.ltM h

theorem u_notin : u ∉ I ∪ O ∪ M := by
  simp only [Finset.mem_union, not_or]
  exact ⟨⟨R.uI, R.uO⟩, R.uM⟩

/-- Sums over the 19 labels split along the partition. -/
theorem sumV (f : Nat → Nat) : ∑ v ∈ V, f v = f u + ∑ v ∈ I, f v + ∑ v ∈ O, f v + ∑ v ∈ M, f v := by
  rw [R.V_eq, Finset.sum_insert R.u_notin,
    Finset.sum_union (Finset.disjoint_union_left.mpr ⟨R.dIM, R.dOM⟩), Finset.sum_union R.dIO]
  omega

/-- The partition `V = {u} ⊔ I ⊔ O ⊔ M`. -/
theorem part (p : Nat → Prop) [DecidablePred p] :
    (V.filter p).card =
      (if p u then 1 else 0) + (I.filter p).card + (O.filter p).card + (M.filter p).card := by
  rw [Finset.card_filter, R.sumV, Finset.card_filter, Finset.card_filter, Finset.card_filter]

theorem cM : M.card = 5 := by
  have h := R.part (fun _ => True)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial), ite_true, Finset.card_range] at h
  rw [R.cI, R.cO] at h
  omega

theorem split_out (w : Nat) :
    oc G V w = (if G w u = true then 1 else 0) + oc G I w + oc G O w + oc G M w :=
  R.part (fun v => G w v = true)

theorem split_in (w : Nat) :
    ic G V w = (if G u w = true then 1 else 0) + ic G I w + ic G O w + ic G M w :=
  R.part (fun v => G v w = true)

theorem in_u : ic G V u = 7 := by
  rw [← R.cI]
  unfold ic
  congr 1
  ext v
  simp [R.mI v, V]

theorem out_u : oc G V u = 6 := by
  rw [← R.cO]
  unfold oc
  congr 1
  ext v
  simp [R.mO v, V]

/-- (L1) An out-neighbour of `u` heads no in-neighbour of `u`. -/
theorem O_noI {x w : Nat} (hx : x ∈ O) (hw : w ∈ I) : G x w = false := by
  cases h : G x w
  · rfl
  · exact (R.H.n3 R.hu (R.ltO hx) (R.ltI hw) (R.arcO hx) h (R.arcI hw)).elim

theorem O_nou {x : Nat} (hx : x ∈ O) : G x u = false := R.H.back R.hu (R.ltO hx) (R.arcO hx)

theorem I_nu {w : Nat} (hw : w ∈ I) : G u w = false := R.H.back (R.ltI hw) R.hu (R.arcI hw)

/-! ### Degrees by class -/

theorem outO {x : Nat} (hx : x ∈ O) : oc G V x = oc G O x + oc G M x := by
  rw [R.split_out x, R.O_nou hx, oc_eq_zero (fun w hw => R.O_noI hx hw)]
  simp

theorem inO {x : Nat} (hx : x ∈ O) : ic G V x = 1 + ic G I x + ic G O x + ic G M x := by
  rw [R.split_in x, R.arcO hx]
  simp

theorem outI {w : Nat} (hw : w ∈ I) : oc G V w = 1 + oc G I w + oc G O w + oc G M w := by
  rw [R.split_out w, R.arcI hw]
  simp

theorem inI {w : Nat} (hw : w ∈ I) : ic G V w = ic G I w + ic G M w := by
  rw [R.split_in w, R.I_nu hw, ic_eq_zero (fun x hx => R.O_noI hx hw)]
  simp

theorem outM {m : Nat} (hm : m ∈ M) : oc G V m = oc G I m + oc G O m + oc G M m := by
  rw [R.split_out m, R.Mnu hm]
  simp

theorem inM {m : Nat} (hm : m ∈ M) : ic G V m = ic G I m + ic G O m + ic G M m := by
  rw [R.split_in m, R.Mun hm]
  simp

/-- (L1) Rows of `O` live in `O ∪ M`. -/
theorem O_out {x : Nat} (hx : x ∈ O) : 6 ≤ oc G O x + oc G M x := by
  rw [← R.outO hx]; exact R.H.out (R.ltO hx)

theorem O_inner {x : Nat} (hx : x ∈ O) : 1 ≤ oc G O x := by
  have h1 := R.O_out hx
  have h2 := oc_le (G := G) M x
  rw [R.cM] at h2
  omega

theorem cap {v : Nat} (hv : v < 19) : ic G V v ≤ 7 := R.H.cap v hv

theorem cap7 {v : Nat} (hv : v < 19) (h : ic G V v = 7) : oc G V v = 6 := R.H.cap7 v hv h

theorem out6 {v : Nat} (hv : v < 19) : 6 ≤ oc G V v := R.H.out hv

/-- (L2) A vertex of `I` heading nothing in `O` has in-degree at most 6. -/
theorem I0_in {w : Nat} (hw : w ∈ I) (hp : oc G O w = 0) : ic G V w ≤ 6 := by
  have h1 := R.out6 (R.ltI hw)
  rw [R.outI hw, hp] at h1
  rw [R.inI hw]
  have h2 := oc_ic_le_mem R.H.loopless R.H.noShort R.subI hw
  have h3 := oc_ic_le R.H.loopless R.H.noShort R.subM (R.ltI hw) (B := M) (fun v hv _ => hv)
  rw [R.cI] at h2
  rw [R.cM] at h3
  omega

/-! ### Saturation facts -/

/-- Lemma 5.2: every row of `M` is headed by some vertex of `O`. -/
theorem am_pos {m : Nat} (hm : m ∈ M) : 1 ≤ ic G O m := by
  have hne : u ≠ m := fun h => R.uM (h ▸ hm)
  obtain ⟨z, hz, h1, h2⟩ := R.H.sat u m R.hu (R.ltM hm) hne (R.Mun hm) (R.Mnu hm)
  exact ic_pos ((R.mO z).mpr ⟨hz, h1⟩) h2

/-- Lemma 5.1, local form: if `w ∈ I` misses `x ∈ O`, some row `m` has `x → m → w`. -/
theorem lemma51 {w x : Nat} (hw : w ∈ I) (hx : x ∈ O) (hwx : G w x = false) :
    ∃ m ∈ M, G x m = true ∧ G m w = true := by
  obtain ⟨z, hz, h1, h2⟩ := R.H.sat x w (R.ltO hx) (R.ltI hw) (Ne.symm (R.neIO hw hx))
    (R.O_noI hx hw) hwx
  refine ⟨z, ?_, h1, h2⟩
  have hzu : z ≠ u := by rintro rfl; rw [R.O_nou hx] at h1; exact Bool.false_ne_true h1
  rcases Finset.mem_insert.mp (R.V_eq ▸ Finset.mem_range.mpr hz : z ∈ insert u (I ∪ O ∪ M)) with h | h
  · exact absurd h hzu
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rw [R.O_noI hx h] at h1; exact absurd h1 Bool.false_ne_true
    · rw [R.O_noI h hw] at h2; exact absurd h2 Bool.false_ne_true
  · exact h

/-- (L3) A row heading `w ∈ I` is not headed by any head of `w` in `O`. -/
theorem L3 {m w x : Nat} (hm : m ∈ M) (hw : w ∈ I) (hx : x ∈ O) (hmw : G m w = true)
    (hwx : G w x = true) : G x m = false :=
  R.H.tri (R.ltM hm) (R.ltI hw) (R.ltO hx) hmw hwx

/-- `M ↛ H`: no row heads a vertex of `I` heading all of `O` (uses `a_m ≥ 1`). -/
theorem noMH {m w : Nat} (hm : m ∈ M) (hw : w ∈ I) (hall : ∀ x ∈ O, G w x = true) : G m w = false := by
  cases hmw : G m w
  · rfl
  · exfalso
    obtain ⟨x, hx, hxm⟩ := exists_of_ic (R.am_pos hm)
    rw [R.L3 hm hw hx hmw (hall x hx)] at hxm
    exact Bool.false_ne_true hxm

/-- A vertex `w ∈ I` heading some `x ∈ O` that heads all of `M` is headed by no row. -/
theorem noMK {m w x : Nat} (hm : m ∈ M) (hw : w ∈ I) (hx : x ∈ O) (hK : ∀ m' ∈ M, G x m' = true)
    (hwx : G w x = true) : G m w = false := by
  cases hmw : G m w
  · rfl
  · have := R.L3 hm hw hx hmw hwx
    rw [hK m hm] at this
    exact Bool.noConfusion this

/-! ### The global identity (residual note, Lemma N2, exact form) -/

/-- `Σ in = Σ out`, split by classes: `7 + (I→O) + (M→O) + Σ_M in + Σ_I in = (O→M) + Σ_M out + Σ_I out`. -/
theorem global :
    7 + ∑ w ∈ I, oc G O w + ∑ m ∈ M, oc G O m + ∑ m ∈ M, ic G V m + ∑ w ∈ I, ic G V w =
      ∑ x ∈ O, oc G M x + ∑ m ∈ M, oc G V m + ∑ w ∈ I, oc G V w := by
  have hs := Compose.ThinRigid.sum_out_eq_sum_in G V
  change ∑ x ∈ V, oc G V x = ∑ v ∈ V, ic G V v at hs
  rw [R.sumV, R.sumV (ic G V), R.in_u, R.out_u] at hs
  have hO1 : ∑ x ∈ O, oc G V x = ∑ x ∈ O, oc G O x + ∑ x ∈ O, oc G M x := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun x hx => R.outO hx)
  have hO2 : ∑ x ∈ O, ic G V x = 6 + ∑ x ∈ O, ic G I x + ∑ x ∈ O, ic G O x + ∑ x ∈ O, ic G M x := by
    rw [Finset.sum_congr rfl (fun x hx => R.inO hx), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, R.cO, smul_eq_mul]
  have s1 : ∑ x ∈ O, ic G I x = ∑ w ∈ I, oc G O w := (swap G I O).symm
  have s2 : ∑ x ∈ O, ic G O x = ∑ x ∈ O, oc G O x := (swap G O O).symm
  have s3 : ∑ x ∈ O, ic G M x = ∑ m ∈ M, oc G O m := (swap G M O).symm
  omega

end Root

end LeanCH.BR.BR36
