import LeanCH.BR.BR36Reduce
import Mathlib.Tactic.Ring

/-!
# Discharging route, part 1: root lemmas for every `s` (Lean 4.35.0)

Paper source: `checkpoints/boundary_20261111/BR37_attempt_subagent.md`, sections 1-3 (Lemmas 1-6).

Setting (`SHyp s G`): `3s+1` labels, loopless, minimum out-degree `s`, no cycle of length `≤ 3`, every in-degree at
most `s + 1` (the strict cap for `s ≤ 7`), and saturated in the two-path form. For a label `u`:
`II u = I(u)`, `OO u = O(u)`, `MM u` = the non-neighbours, `HS u` = vertices of `I(u)` heading all of `O(u)`,
`KS u` = vertices of `O(u)` heading all of `M(u)`. A *root* has `(in, out) = (s + 1, s)`.

* `ch_subset`: `BoundaryRegular q c` excludes a vertex set of size `≤ qc` in which every vertex has `c` heads.
* Lemma 1 (`O_noI`, `outO`, `inI`), Lemma 2: `am_pos` (a), `noMH`, `H_in` (b), `K_par`, `K_in` (c).
* Lemmas 3-4 as the two inequalities `K1`, `K2` at a root.
* Lemma 5 (`lemma5`): `r` roots served by `η ∈ H(·)` give `in(η) + r ≤ out(η)` and `r + 2s + 1 ≤ 2 out(η)`.
  (The paper's averaging step is replaced by one root `v` with `out_U(v) ≤ in_U(v)`.)
* Lemma 6 (`lemma6`): `K`-witnesses of roots with `h = 0` are private.
-/

namespace LeanCH.BR.BR36

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of

/-- **CH from BR on a vertex subset.** -/
theorem ch_subset {G : CH.Digraph} {n q c : Nat} {S : Finset Nat} (hc : 0 < c)
    (br : BoundaryRegular q c) (hsub : S ⊆ Finset.range n) (hne : S.Nonempty) (hcard : S.card ≤ q * c)
    (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n q)
    (keep : ∀ x ∈ S, c ≤ oc G S x) : False := by
  classical
  obtain ⟨e, eB, eI, eM, eS⟩ := CH.Side.sc_finset_enumeration hsub
  set m := S.card with hm
  let H : CH.Digraph := fun a b => if a < m then (if b < m then G (e a) (e b) else false) else false
  have hloop : CH.Loopless H m := by
    intro v hv
    change (if v < m then (if v < m then G (e v) (e v) else false) else false) = false
    simp only [hv, ite_true]; exact loopless (e v) (eB v hv)
  have hmin : CH.MinOutdegreeAtLeast H m c := by
    intro a ha
    let T : Finset Nat := (Finset.range m).filter (fun i => G (e a) (e i) = true)
    have himage : T.image e = S.filter (fun w => G (e a) w = true) := by
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
  exact hshort (ch_of_boundaryRegular hc br (Finset.card_pos.mpr hne) hcard hloop hmin)

/-- The `3s+1` labels. -/
def VS (s : Nat) : Finset Nat := Finset.range (3 * s + 1)

def II (G : CH.Digraph) (s u : Nat) : Finset Nat := (VS s).filter (fun v => G v u = true)
def OO (G : CH.Digraph) (s u : Nat) : Finset Nat := (VS s).filter (fun v => G u v = true)
def MM (G : CH.Digraph) (s u : Nat) : Finset Nat :=
  (VS s).filter (fun v => v ≠ u ∧ G v u = false ∧ G u v = false)

/-- `H(u)`: in-neighbours of `u` heading all of `O(u)`. -/
def HS (G : CH.Digraph) (s u : Nat) : Finset Nat := (II G s u).filter (fun w => ∀ x ∈ OO G s u, G w x = true)

/-- `K(u)`: out-neighbours of `u` heading all of `M(u)`. -/
def KS (G : CH.Digraph) (s u : Nat) : Finset Nat := (OO G s u).filter (fun x => ∀ m ∈ MM G s u, G x m = true)

/-- A root: in-degree `s + 1`, out-degree `s`. -/
def IsRoot (G : CH.Digraph) (s u : Nat) : Prop :=
  u < 3 * s + 1 ∧ ic G (VS s) u = s + 1 ∧ oc G (VS s) u = s

/-- Saturated boundary graph at `s` with every in-degree at most `s + 1`. -/
structure SHyp (s : Nat) (G : CH.Digraph) : Prop where
  loopless : CH.Loopless G (3 * s + 1)
  deg : CH.MinOutdegreeAtLeast G (3 * s + 1) s
  noShort : ¬ CH.HasDirectedCycleAtMost G (3 * s + 1) 3
  cap : ∀ v, v < 3 * s + 1 → ic G (VS s) v ≤ s + 1
  sat : ∀ a b, a < 3 * s + 1 → b < 3 * s + 1 → a ≠ b → G a b = false → G b a = false →
    ∃ z, z < 3 * s + 1 ∧ G a z = true ∧ G z b = true

theorem mem_VS {s v : Nat} : v ∈ VS s ↔ v < 3 * s + 1 := by simp [VS]

theorem mem_II {G : CH.Digraph} {s u v : Nat} : v ∈ II G s u ↔ v < 3 * s + 1 ∧ G v u = true := by
  simp [II, VS]

theorem mem_OO {G : CH.Digraph} {s u v : Nat} : v ∈ OO G s u ↔ v < 3 * s + 1 ∧ G u v = true := by
  simp [OO, VS]

theorem mem_MM {G : CH.Digraph} {s u v : Nat} :
    v ∈ MM G s u ↔ v < 3 * s + 1 ∧ v ≠ u ∧ G v u = false ∧ G u v = false := by
  simp [MM, VS]

theorem card_II {G : CH.Digraph} {s u : Nat} : (II G s u).card = ic G (VS s) u := rfl
theorem card_OO {G : CH.Digraph} {s u : Nat} : (OO G s u).card = oc G (VS s) u := rfl

theorem HS_sub {G : CH.Digraph} {s u : Nat} : HS G s u ⊆ II G s u := Finset.filter_subset _ _
theorem KS_sub {G : CH.Digraph} {s u : Nat} : KS G s u ⊆ OO G s u := Finset.filter_subset _ _

theorem HS_all {G : CH.Digraph} {s u w : Nat} (h : w ∈ HS G s u) : ∀ x ∈ OO G s u, G w x = true :=
  (Finset.mem_filter.mp h).2

theorem KS_all {G : CH.Digraph} {s u x : Nat} (h : x ∈ KS G s u) : ∀ m ∈ MM G s u, G x m = true :=
  (Finset.mem_filter.mp h).2

namespace SHyp

variable {s : Nat} {G : CH.Digraph} (H : SHyp s G)
include H

theorem n2 {a b : Nat} (ha : a < 3 * s + 1) (hb : b < 3 * s + 1) (h1 : G a b = true) (h2 : G b a = true) :
    False :=
  no2 H.loopless H.noShort ha hb h1 h2

theorem n3 {a b c : Nat} (ha : a < 3 * s + 1) (hb : b < 3 * s + 1) (hc : c < 3 * s + 1)
    (h1 : G a b = true) (h2 : G b c = true) (h3 : G c a = true) : False :=
  no3 H.loopless H.noShort ha hb hc h1 h2 h3

theorem out {w : Nat} (hw : w < 3 * s + 1) : s ≤ oc G (VS s) w := out_card H.deg hw

theorem ne_of_arc {a b : Nat} (ha : a < 3 * s + 1) (h : G a b = true) : a ≠ b := by
  rintro rfl; rw [H.loopless a ha] at h; exact Bool.false_ne_true h

theorem tri {a b c : Nat} (ha : a < 3 * s + 1) (hb : b < 3 * s + 1) (hc : c < 3 * s + 1) (h1 : G a b = true)
    (h2 : G b c = true) : G c a = false := by
  cases h' : G c a
  · rfl
  · exact (H.n3 ha hb hc h1 h2 h').elim

theorem back {a b : Nat} (ha : a < 3 * s + 1) (hb : b < 3 * s + 1) (h : G a b = true) : G b a = false := by
  cases h' : G b a
  · rfl
  · exact (H.n2 ha hb h h').elim

theorem subV : VS s ⊆ Finset.range (3 * s + 1) := fun _ h => h

variable {u : Nat}

theorem ltI {w : Nat} (h : w ∈ II G s u) : w < 3 * s + 1 := (mem_II.mp h).1
theorem ltO {w : Nat} (h : w ∈ OO G s u) : w < 3 * s + 1 := (mem_OO.mp h).1
theorem ltM {w : Nat} (h : w ∈ MM G s u) : w < 3 * s + 1 := (mem_MM.mp h).1
theorem subI : II G s u ⊆ Finset.range (3 * s + 1) := fun _ h => Finset.mem_range.mpr (H.ltI h)
theorem subO : OO G s u ⊆ Finset.range (3 * s + 1) := fun _ h => Finset.mem_range.mpr (H.ltO h)
theorem subM : MM G s u ⊆ Finset.range (3 * s + 1) := fun _ h => Finset.mem_range.mpr (H.ltM h)

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

theorem I_nu (hu : u < 3 * s + 1) {w : Nat} (hw : w ∈ II G s u) : G u w = false :=
  H.back (H.ltI hw) hu (mem_II.mp hw).2

theorem outO (hu : u < 3 * s + 1) {x : Nat} (hx : x ∈ OO G s u) :
    oc G (VS s) x = oc G (OO G s u) x + oc G (MM G s u) x := by
  rw [H.split_out hu x, H.O_nou hu hx, oc_eq_zero (fun w hw => H.O_noI hu hx hw)]
  simp

theorem inI (hu : u < 3 * s + 1) {w : Nat} (hw : w ∈ II G s u) :
    ic G (VS s) w = ic G (II G s u) w + ic G (MM G s u) w := by
  rw [H.split_in hu w, H.I_nu hu hw, ic_eq_zero (fun x hx => H.O_noI hu hx hw)]
  simp

/-- Lemma 5.1: if `w ∈ I(u)` misses `x ∈ O(u)`, some row `m` has `x → m → w`. -/
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

/-- Lemma 2(b): a vertex of `H(u)` has in-degree at most `in(u) − 1`. -/
theorem H_in (hu : u < 3 * s + 1) {η : Nat} (hη : η ∈ HS G s u) : ic G (VS s) η + 1 ≤ ic G (VS s) u := by
  have hηI := HS_sub hη
  rw [H.inI hu hηI, ic_eq_zero (fun m hm => H.noMH hu hm hη), ← card_II]
  have := oc_ic_le_mem H.loopless H.noShort H.subI hηI
  omega

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

/-! ### Lemmas at a root -/

theorem root_M {u : Nat} (hr : IsRoot G s u) : (MM G s u).card + 1 = s := by
  have := H.cM hr.1
  rw [hr.2.1, hr.2.2] at this
  omega

/-- Lemma 3 (with `ν` dropped): `in(x) + out(x) + 1 ≤ 2s + h(u)` for `x ∈ K(u)`. -/
theorem K1 {u x : Nat} (hr : IsRoot G s u) (hx : x ∈ KS G s u) :
    ic G (VS s) x + oc G (VS s) x + 1 ≤ 2 * s + (HS G s u).card := by
  have hxO := KS_sub hx
  have h1 := H.K_in hr.1 hx
  have h2 := H.K_out hr.1 hx
  have h3 := oc_ic_le_mem H.loopless H.noShort H.subO hxO
  rw [card_OO, hr.2.2] at h3
  have h4 := H.root_M hr
  omega

/-- Lemma 4 (no near-sink), with Lemma 3: `in(x) + 2 ≤ out(x) + h(u)` for `x ∈ K(u)`. -/
theorem K2 {u x : Nat} (hr : IsRoot G s u) (hx : x ∈ KS G s u) :
    ic G (VS s) x + 2 ≤ oc G (VS s) x + (HS G s u).card := by
  have hu := hr.1
  have hxO := KS_sub hx
  have h1 := H.K_in hu hx
  have h2 := H.K_out hu hx
  have h3 := oc_ic_le_mem H.loopless H.noShort H.subO hxO
  rw [card_OO, hr.2.2] at h3
  have h4 := H.root_M hr
  have h5 := H.out (H.ltO hxO)
  by_cases hbig : 2 ≤ oc G (OO G s u) x
  · omega
  -- `x` has exactly one head `x⁺` in `O(u)`; it must have a non-neighbour there
  have hone : oc G (OO G s u) x = 1 := by omega
  by_contra hcon
  have hfull : oc G (OO G s u) x + ic G (OO G s u) x + 1 = s := by omega
  obtain ⟨xp, hxpO, hxxp⟩ := exists_of_oc (le_of_eq hone.symm)
  -- every other vertex of `O(u)` heads `x`
  have adj : ∀ y ∈ OO G s u, y ≠ x → y ≠ xp → G y x = true := by
    intro y hy hyx hyxp
    by_contra hyx'
    have hxy : G x y = false := by
      cases h : G x y
      · rfl
      · exfalso
        have hsub : (OO G s u).filter (fun v => G x v = true) ⊆ {xp} := by
          intro v hv
          by_contra hne
          have : 2 ≤ oc G (OO G s u) x := by
            unfold oc
            rw [← Finset.card_pair (Ne.symm (by simpa using hne) : xp ≠ v)]
            apply Finset.card_le_card
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact Finset.mem_filter.mpr ⟨hxpO, hxxp⟩
            · rw [Finset.mem_singleton.mp hz]; exact hv
          omega
        exact hyxp (Finset.mem_singleton.mp (hsub (Finset.mem_filter.mpr ⟨hy, h⟩)))
    have := oc_ic_le H.loopless H.noShort H.subO (H.ltO hxO) (B := ((OO G s u).erase x).erase y)
      (fun v hv hG => by
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hv⟩⟩
        · rintro rfl
          rcases hG with h | h
          · rw [hxy] at h; exact Bool.false_ne_true h
          · exact hyx' h
        · rintro rfl
          rcases hG with h | h <;> (rw [H.loopless v (H.ltO hxO)] at h; exact Bool.false_ne_true h))
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyx, hy⟩), Finset.card_erase_of_mem hxO, card_OO,
      hr.2.2] at this
    omega
  -- `x⁺` heads nothing in `O(u)`
  have hxp0 : oc G (OO G s u) xp = 0 := by
    apply oc_eq_zero
    intro y hy
    cases h : G xp y
    · rfl
    · exfalso
      have hxpx : xp ≠ x := (H.ne_of_arc (H.ltO hxO) hxxp).symm
      by_cases hyx : y = x
      · rw [hyx] at h; exact H.n2 (H.ltO hxO) (H.ltO hxpO) hxxp h
      by_cases hyxp : y = xp
      · rw [hyxp, H.loopless xp (H.ltO hxpO)] at h; exact Bool.false_ne_true h
      exact H.n3 (H.ltO hy) (H.ltO hxO) (H.ltO hxpO) (adj y hy hyx hyxp) hxxp h
  have h6 := H.out (H.ltO hxpO)
  rw [H.outO hu hxpO, hxp0] at h6
  have h7 := oc_le (G := G) (MM G s u) xp
  omega

/-- **Lemma 5.** If `η` lies in `H(v)` for every root `v` of a nonempty set `U` of roots, then
`in(η) + |U| ≤ out(η)` and `|U| + 2s + 1 ≤ 2 out(η)`. -/
theorem lemma5 {η : Nat} {U : Finset Nat} (hη : η < 3 * s + 1) (hne : U.Nonempty)
    (hU : ∀ v ∈ U, IsRoot G s v ∧ η ∈ HS G s v) :
    ic G (VS s) η + U.card ≤ oc G (VS s) η ∧ U.card + 2 * s + 1 ≤ 2 * oc G (VS s) η := by
  classical
  have hUV : U ⊆ Finset.range (3 * s + 1) := fun v hv => Finset.mem_range.mpr (hU v hv).1.1
  have hηv : ∀ v ∈ U, G η v = true := fun v hv => (mem_II.mp (HS_sub (hU v hv).2)).2
  -- out-bound at each root of `U`
  have outb : ∀ v ∈ U, s + U.card ≤ oc G (VS s) η + oc G U v := by
    intro v hv
    have hr := (hU v hv).1
    have hsub : OO G s v ∪ U ⊆ (VS s).filter (fun y => G η y = true) := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_filter.mpr ⟨mem_VS.mpr (H.ltO hy), HS_all (hU v hv).2 y hy⟩
      · exact Finset.mem_filter.mpr ⟨mem_VS.mpr (hU y hy).1.1, hηv y hy⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_add_card_inter (OO G s v) U
    have h3 : (OO G s v ∩ U).card ≤ oc G U v := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_inter.mp hy
      exact Finset.mem_filter.mpr ⟨hy2, (mem_OO.mp hy1).2⟩
    rw [card_OO, hr.2.2] at h2
    change Finset.card _ ≤ oc G (VS s) η at h1
    omega
  -- in-bound at each root of `U`
  have inb : ∀ v ∈ U, ic G (VS s) η + ic G U v ≤ s := by
    intro v hv
    have hr := (hU v hv).1
    have hηI := HS_sub (hU v hv).2
    have hηU : η ∉ U := fun h => by
      have := hηv η h; rw [H.loopless η hη] at this; exact Bool.false_ne_true this
    have hsub : (VS s).filter (fun y => G y η = true) ⊆ (II G s v \ U).erase η := by
      intro y hy
      obtain ⟨hyV, hyη⟩ := Finset.mem_filter.mp hy
      have hy' := mem_VS.mp hyV
      refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_sdiff.mpr ⟨?_, fun hyU => ?_⟩⟩
      · rw [h, H.loopless η hη] at hyη; exact Bool.false_ne_true hyη
      · have hyV' : y ∈ insert v (II G s v ∪ OO G s v ∪ MM G s v) := H.V_eq hr.1 ▸ hyV
        rcases Finset.mem_insert.mp hyV' with h | h
        · rw [h] at hyη; exact (H.n2 hη hr.1 (hηv v hv) hyη).elim
        rcases Finset.mem_union.mp h with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact h
          · rw [H.O_noI hr.1 h hηI] at hyη; exact absurd hyη Bool.false_ne_true
        · rw [H.noMH hr.1 h (hU v hv).2] at hyη; exact absurd hyη Bool.false_ne_true
      · exact H.n2 hη hy' (hηv y hyU) hyη
    have h1 := Finset.card_le_card hsub
    have hmem : η ∈ II G s v \ U := Finset.mem_sdiff.mpr ⟨hηI, hηU⟩
    rw [Finset.card_erase_of_mem hmem] at h1
    have h2 : ic G U v ≤ (II G s v ∩ U).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨hyU, hyv⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_inter.mpr ⟨mem_II.mpr ⟨(hU y hyU).1.1, hyv⟩, hyU⟩
    have h3 := Finset.card_sdiff_add_card_inter (II G s v) U
    have h4 : (II G s v).card = s + 1 := by rw [card_II]; exact hr.2.1
    have h5 : ((VS s).filter (fun y => G y η = true)).card = ic G (VS s) η := rfl
    have h6 : 1 ≤ (II G s v \ U).card := Finset.card_pos.mpr ⟨η, hmem⟩
    omega
  -- a root of `U` with `out_U ≤ in_U`
  have hsw : ∑ v ∈ U, oc G U v ≤ ∑ v ∈ U, ic G U v := le_of_eq (swap G U U)
  obtain ⟨v0, hv0, hle⟩ := Finset.exists_le_of_sum_le hne hsw
  have o0 := outb v0 hv0
  have i0 := inb v0 hv0
  refine ⟨by omega, ?_⟩
  -- the second bound: average `outb` over `U`
  have S1 := Finset.sum_le_sum outb
  rw [Finset.sum_const, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, smul_eq_mul] at S1
  have pv : ∀ v ∈ U, oc G U v + ic G U v + 1 ≤ U.card := fun v hv =>
    oc_ic_le_mem H.loopless H.noShort hUV hv
  have S2 := Finset.sum_le_sum pv
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← swap G U U, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, mul_one] at S2
  set r := U.card with hr
  set o := oc G (VS s) η
  set e := ∑ v ∈ U, oc G U v
  have hr0 : 0 < r := Finset.card_pos.mpr hne
  have key : r * (s + r + 1 + s) ≤ r * (2 * o) := by
    have : r * (s + r + 1 + s) = 2 * (r * (s + r)) + r - r * r := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have : r * r ≤ 2 * (r * s + r * r) + r := by omega
      omega
    rw [this]
    have : r * (2 * o) = 2 * (r * o) := by ring
    rw [this]
    omega
  have := Nat.le_of_mul_le_mul_left key hr0
  omega

/-- **Lemma 6.** Two distinct roots `u, u'` with `h(u') = 0` share no `K`-vertex. -/
theorem lemma6 {u u' x : Nat} (hr : IsRoot G s u) (hr' : IsRoot G s u') (hne : u ≠ u')
    (hH : (HS G s u').card = 0) (hx : x ∈ KS G s u) (hx' : x ∈ KS G s u') : False := by
  have hux : G u x = true := (mem_OO.mp (KS_sub hx)).2
  have hu'x : G u' x = true := (mem_OO.mp (KS_sub hx')).2
  have a1 : G u' u = true := by
    rcases H.K_par hr'.1 hx' hr.1 hux with h | h | h
    · exact absurd h hne
    · exact (mem_OO.mp h).2
    · rw [Finset.card_eq_zero.mp hH] at h; exact absurd h (Finset.notMem_empty u)
  have a2 : G u u' = true := by
    rcases H.K_par hr.1 hx hr'.1 hu'x with h | h | h
    · exact absurd h.symm hne
    · exact (mem_OO.mp h).2
    · have := H.H_in hr.1 h
      rw [hr.2.1, hr'.2.1] at this
      omega
  exact H.n2 hr.1 hr'.1 a2 a1

end SHyp

end LeanCH.BR.BR36
