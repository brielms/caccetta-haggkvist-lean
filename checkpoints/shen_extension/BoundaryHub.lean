import Mathlib.Tactic
import checkpoints.shen_extension.TopOvershootProfiles
import checkpoints.shen_extension.DisjointRootFourCycles

/-!
# The boundary hub law and what it gives

Lean 4.35.0. "Tight" means exactly `d` heads. `inN` is `LeanCH.BR.BR45.inN`.

F1, tight rows from regularity one vertex lower.
* `tight_rows_of_lower_regular`: (any cutoff `q ≥ 2`) if every row of `U` has at least `d` heads, every
  sub-family of `U` with one vertex fewer and all rows at least `d` is out-regular, and the tight rows `S`
  satisfy `|S|(d+1) < |U|`, then `d+1 ≤ |S|`.
* `qThreeTight_of_lowerRegular`: (`q ≥ 3`, `d ≥ 2`) out-regularity on `q*d+1` vertices gives `QThreeTight q d`.
* `threeTight_of_boundaryRegular`: (`d ≥ 1`) `BoundaryRegular d` gives `ThreeTight d` (`d = 1` by `threeTight_one`).
* `qTwoTight_of_lowerRegular`: (`q ≥ 2`, `d ≥ 1`) out-regularity on `q*d+1` vertices gives `QTwoTight q d`.
* `twoTight_of_boundaryRegular`: (`d ≥ 1`) `BoundaryRegular d` gives `TwoTight d`.

F2, in-regularity.
* `QBoundaryInRegular q d`: every `q`-free digraph on `q*d+1` vertices with all rows at least `d` has every
  vertex with exactly `d` parents.
* `boundaryNoPrivate_of_inRegular`: (`d ≠ 1`, any cutoff) in-regularity excludes a vertex with exactly one parent.

F3, the hub law.
* `BoundaryHub d`: on `3d+1` vertices, 3-free, all rows at least `d`, every vertex is the hub of `d` directed
  4-cycles with pairwise disjoint interiors.
* `hub_spanning`: (any cutoff `q ≥ 3`) a packing at `h` with `|V| = 3|P|+1` gives `h` exactly `|P|` heads and
  exactly `|P|` parents.
* `boundaryRegular_of_boundaryHub`, `inRegular_of_boundaryHub`: the hub law gives out- and in-regularity.
* `middle_false_of_boundaryHub`: the exact-cost disjunct of `Alternatives` is impossible under the hub law.
* `top_overshoot_one_false_of_boundaryHub`: for `d ≥ 2`, overshoot one is impossible under the hub law.
* `overshoot_ge_two_of_boundaryHub`, `third_disjunct_two_of_boundaryHub`: the same consequences under the hub law.

`BoundaryHub d` and the regularity laws are SUPPLIED HYPOTHESES. Nothing here closes CH.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.Closure.BoundaryHub

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 Finset LeanCH.BR.Closure.DeficitLevels
  LeanCH.BR.Closure.PackingFrontier LeanCH.BR.Closure.PrivateCompletion
  LeanCH.BR.Closure.UnitState LeanCH.BR.Closure.PrivateCompletionOrder
  LeanCH.BR.TightProfile LeanCH.BR.Closure.TopOvershoot
  LeanCH.BR.Closure.DisjointRootFourCycles

/-! ## F1 -/

/-- (F1) Tight rows from out-regularity one vertex lower (only for `E` on subsets of `U`). -/
theorem tight_rows_of_lower_regular {q d : ℕ} {E : CH.Digraph} {U : Finset ℕ}
    (hq : 2 ≤ q) (free : QFree E U q)
    (law : ∀ W ⊆ U, W.card + 1 = U.card → (∀ x ∈ W, d ≤ (outN E W x).card) →
      ∀ x ∈ W, (outN E W x).card = d)
    (deg : ∀ x ∈ U, d ≤ (outN E U x).card)
    (few : (U.filter (fun x => (outN E U x).card = d)).card * (d+1) < U.card) :
    d + 1 ≤ (U.filter (fun x => (outN E U x).card = d)).card := by
  classical
  set S := U.filter (fun x => (outN E U x).card = d) with hS
  have hT : (S ∪ S.biUnion (fun x => outN E U x)).card ≤ S.card * (d+1) := by
    have h1 := card_union_le S (S.biUnion (fun x => outN E U x))
    have h2 : (S.biUnion (fun x => outN E U x)).card ≤ S.card * d := by
      calc (S.biUnion (fun x => outN E U x)).card ≤ ∑ x ∈ S, (outN E U x).card := card_biUnion_le
        _ = ∑ x ∈ S, d := sum_congr rfl (fun x hx => (mem_filter.mp hx).2)
        _ = S.card * d := by rw [sum_const, smul_eq_mul]
    have h3 : S.card * (d+1) = S.card * d + S.card := by ring
    omega
  obtain ⟨w, wU, wT⟩ : ∃ w ∈ U, w ∉ S ∪ S.biUnion (fun x => outN E U x) := by
    by_contra! all
    have := card_le_card (show U ⊆ S ∪ S.biUnion (fun x => outN E U x) from all)
    omega
  have wS : w ∉ S := fun m => wT (mem_union.mpr (Or.inl m))
  have noHit : ∀ x ∈ S, E x w ≠ true := fun x hx e =>
    wT (mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨x, hx, mem_outN.mpr ⟨wU, e⟩⟩)))
  have rows : ∀ x ∈ U.erase w, d ≤ (outN E (U.erase w) x).card := by
    intro x hx
    obtain ⟨_, xU⟩ := mem_erase.mp hx
    rw [outN_erase]
    by_cases xs : x ∈ S
    · rw [erase_eq_of_notMem (fun m => noHit x xs (mem_outN.mp m).2)]
      exact deg x xU
    · have ne : (outN E U x).card ≠ d := fun e => xs (mem_filter.mpr ⟨xU, e⟩)
      have := deg x xU
      have := pred_card_le_card_erase (s := outN E U x) (a := w)
      omega
  have reg := law (U.erase w) (erase_subset w U) (card_erase_add_one wU) rows
  have heads : outN E U w ⊆ S := by
    intro y hy
    obtain ⟨yU, ewy⟩ := mem_outN.mp hy
    have yw : y ≠ w := fun e => loopfree free (by omega) wU (e ▸ ewy)
    by_contra ys
    have ne : (outN E U y).card ≠ d := fun e => ys (mem_filter.mpr ⟨yU, e⟩)
    have big := deg y yU
    have r := reg y (mem_erase.mpr ⟨yw, yU⟩)
    rw [outN_erase] at r
    by_cases eyw : E y w = true
    · exact digonfree free hq wU yU ewy eyw
    · rw [erase_eq_of_notMem (fun m => eyw (mem_outN.mp m).2)] at r
      omega
  have wne : (outN E U w).card ≠ d := fun e => wS (mem_filter.mpr ⟨wU, e⟩)
  have := deg w wU
  have := card_le_card heads
  omega

/-- (F1) Out-regularity on `q*d+1` vertices gives three tight rows on `q*d+2` vertices (`q ≥ 3`, `d ≥ 2`). -/
theorem qThreeTight_of_lowerRegular {q d : ℕ} (hq : 3 ≤ q) (hd : 2 ≤ d)
    (reg : ∀ (E : CH.Digraph) (W : Finset ℕ), QFree E W q → W.card = q*d+1 →
      (∀ x ∈ W, d ≤ (outN E W x).card) → ∀ x ∈ W, (outN E W x).card = d) :
    QThreeTight q d := by
  intro E U free size deg
  by_contra! few
  have m1 : (U.filter (fun x => (outN E U x).card = d)).card * (d+1) ≤ 2 * (d+1) :=
    Nat.mul_le_mul_right _ (by omega)
  have m2 : 3 * d ≤ q * d := Nat.mul_le_mul_right _ hq
  have key := tight_rows_of_lower_regular (by omega) free
    (fun W sub c rows => reg E W (free.mono_set sub) (by omega) rows) deg (by omega)
  omega

/-- (F1) `BoundaryRegular d` gives `ThreeTight d` for `d ≥ 1` (`d = 1` is `threeTight_one`). -/
theorem threeTight_of_boundaryRegular {d : ℕ} (hd : 1 ≤ d) (reg : BoundaryRegular d) : ThreeTight d := by
  rcases (show d = 1 ∨ 2 ≤ d by omega) with rfl | hd2
  · exact threeTight_one
  · exact qThreeTight_of_lowerRegular le_rfl hd2 reg

/-- (F1) Out-regularity on `q*d+1` vertices gives two tight rows on `q*d+2` vertices (`q ≥ 2`, `d ≥ 1`). -/
theorem qTwoTight_of_lowerRegular {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d)
    (reg : ∀ (E : CH.Digraph) (W : Finset ℕ), QFree E W q → W.card = q*d+1 →
      (∀ x ∈ W, d ≤ (outN E W x).card) → ∀ x ∈ W, (outN E W x).card = d) :
    QTwoTight q d := by
  intro E U free size deg
  by_contra! few
  have m1 : (U.filter (fun x => (outN E U x).card = d)).card * (d+1) ≤ 1 * (d+1) :=
    Nat.mul_le_mul_right _ (by omega)
  have m2 : 2 * d ≤ q * d := Nat.mul_le_mul_right _ hq
  have key := tight_rows_of_lower_regular hq free
    (fun W sub c rows => reg E W (free.mono_set sub) (by omega) rows) deg (by omega)
  omega

/-- (F1) `BoundaryRegular d` gives `TwoTight d` for `d ≥ 1`. -/
theorem twoTight_of_boundaryRegular {d : ℕ} (hd : 1 ≤ d) (reg : BoundaryRegular d) : TwoTight d :=
  qTwoTight_of_lowerRegular (by decide) hd reg

/-! ## F2 -/

/-- In-regularity on `q*d+1` vertices. -/
def QBoundaryInRegular (q d : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (W : Finset ℕ), QFree E W q → W.card = q*d+1 →
    (∀ x ∈ W, d ≤ (outN E W x).card) → ∀ v ∈ W, (BR45.inN E W v).card = d

/-- (F2) In-regularity excludes a vertex with exactly one parent (`d ≠ 1`, any cutoff). -/
theorem boundaryNoPrivate_of_inRegular {q d : ℕ} (hd : d ≠ 1) (law : QBoundaryInRegular q d) :
    QBoundaryNoPrivate q d := by
  rintro E W free size deg v hv ⟨p, hp, iff⟩
  have c := law E W free size deg v hv
  have eq : BR45.inN E W v = {p} := by
    ext x
    rw [BR45.mem_inN, mem_singleton]
    constructor
    · rintro ⟨xW, e⟩
      exact (iff x xW).mp e
    · rintro rfl
      exact ⟨hp, (iff x hp).mpr rfl⟩
  rw [eq, card_singleton] at c
  omega

/-! ## F3 -/

set_option linter.dupNamespace false in
/-- At the boundary order every vertex is the hub of `d` directed 4-cycles sharing only the hub. -/
def BoundaryHub (d : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), QFree E U 3 → U.card = 3*d+1 →
    (∀ x ∈ U, d ≤ (outN E U x).card) → ∀ h ∈ U, ∃ P, Packing E U h P ∧ P.card = d

/-- Indicator sums over one cycle interior: exactly one head and exactly one parent of the hub. -/
private theorem interior_counts {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {h : ℕ} {C : Finset ℕ}
    (hq : 3 ≤ q) (safe : QFree D V q) (hv : h ∈ V) (cyc : CycleInterior D V h C) :
    (∑ x ∈ C, if D h x = true then 1 else 0) = 1 ∧ (∑ x ∈ C, if D x h = true then 1 else 0) = 1 := by
  obtain ⟨_, sub, a, z, b, rfl, ha, az, zb, bh⟩ := cyc
  have av : a ∈ V := (mem_erase.mp (sub (by simp))).2
  have zv : z ∈ V := (mem_erase.mp (sub (by simp))).2
  have bv : b ∈ V := (mem_erase.mp (sub (by simp))).2
  have anz : a ≠ z := fun e => loopfree safe (by omega) zv (e ▸ az)
  have anb : a ≠ b := fun e => digonfree safe (by omega) hv bv (e ▸ ha) bh
  have znb : z ≠ b := fun e => loopfree safe (by omega) bv (e ▸ zb)
  have hz : D h z ≠ true := fun e =>
    safe h 3 (by decide) hq (.step zv e (.step bv zb (.step hv bh (.refl h))))
  have hb : D h b ≠ true := fun e => digonfree safe (by omega) hv bv e bh
  have ah : D a h ≠ true := fun e => digonfree safe (by omega) hv av ha e
  have zh : D z h ≠ true := fun e =>
    safe h 3 (by decide) hq (.step av ha (.step zv az (.step hv e (.refl h))))
  rw [sum_insert (by simp [anz, anb]), sum_insert (by simp [znb]), sum_singleton,
    sum_insert (by simp [anz, anb]), sum_insert (by simp [znb]), sum_singleton]
  simp [ha, hz, hb, ah, zh, bh]

/-- (F3) A packing at `h` with `|V| = 3|P|+1` spans `V`: `h` has exactly `|P|` heads and `|P|` parents. -/
theorem hub_spanning {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {h : ℕ} {P : Finset (Finset ℕ)}
    (hq : 3 ≤ q) (safe : QFree D V q) (hv : h ∈ V) (pack : Packing D V h P)
    (size : V.card = 3 * P.card + 1) :
    (outN D V h).card = P.card ∧ (BR45.inN D V h).card = P.card := by
  classical
  obtain ⟨rows, disj⟩ := pack
  have mcard : (P.biUnion id).card = 3 * P.card := by
    rw [card_biUnion disj]
    change ∑ C ∈ P, C.card = 3 * P.card
    rw [sum_const_nat (fun C hc => (rows C hc).1), Nat.mul_comm]
  have span : P.biUnion id = V.erase h := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨C, hC, xC⟩ := mem_biUnion.mp hx
      exact (rows C hC).2.1 xC
    · rw [card_erase_of_mem hv, mcard]; omega
  have outEq : outN D V h = (P.biUnion id).filter (fun x => D h x = true) := by
    rw [span]
    ext x
    simp only [mem_outN, mem_filter, mem_erase]
    constructor
    · rintro ⟨xv, e⟩
      exact ⟨⟨fun hx => by rw [hx] at e; exact loopfree safe (by omega) hv e, xv⟩, e⟩
    · rintro ⟨⟨_, xv⟩, e⟩
      exact ⟨xv, e⟩
  have inEq : BR45.inN D V h = (P.biUnion id).filter (fun x => D x h = true) := by
    rw [span]
    ext x
    simp only [BR45.mem_inN, mem_filter, mem_erase]
    constructor
    · rintro ⟨xv, e⟩
      exact ⟨⟨fun hx => by rw [hx] at e; exact loopfree safe (by omega) hv e, xv⟩, e⟩
    · rintro ⟨⟨_, xv⟩, e⟩
      exact ⟨xv, e⟩
  constructor
  · rw [outEq, card_filter, sum_biUnion disj]
    calc _ = ∑ C ∈ P, 1 := sum_congr rfl (fun C hC => (interior_counts hq safe hv (rows C hC)).1)
      _ = P.card := by simp
  · rw [inEq, card_filter, sum_biUnion disj]
    calc _ = ∑ C ∈ P, 1 := sum_congr rfl (fun C hC => (interior_counts hq safe hv (rows C hC)).2)
      _ = P.card := by simp

/-- (F3) The hub law gives out-regularity at the boundary order. -/
theorem boundaryRegular_of_boundaryHub {d : ℕ} (hub : BoundaryHub d) : BoundaryRegular d := by
  intro E W free size deg z hz
  obtain ⟨P, pack, pc⟩ := hub E W free size deg z hz
  have := (hub_spanning le_rfl free hz pack (by omega)).1
  omega

/-- (F3) The hub law gives in-regularity at the boundary order. -/
theorem inRegular_of_boundaryHub {d : ℕ} (hub : BoundaryHub d) : QBoundaryInRegular 3 d := by
  intro E W free size deg v hv
  obtain ⟨P, pack, pc⟩ := hub E W free size deg v hv
  have := (hub_spanning le_rfl free hv pack (by omega)).2
  omega

/-- (F3) The hub law excludes a vertex with exactly one parent (`d ≠ 1`). -/
theorem boundaryNoPrivate_of_boundaryHub {d : ℕ} (hd : d ≠ 1) (hub : BoundaryHub d) :
    BoundaryNoPrivate d :=
  boundaryNoPrivate_of_inRegular hd (inRegular_of_boundaryHub hub)

/-- (F3) Under the hub law the exact-cost disjunct of `Alternatives` is impossible. -/
theorem middle_false_of_boundaryHub {d : ℕ} {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (hub : BoundaryHub d) :
    ¬ ∃ (P : Origin 3 (d+1)) (v : ℕ) (t : State), P.V.card=O.V.card ∧
      MaximalReturns 3 P.G P.V ∧ v∈P.V ∧ t.U=P.V.erase v ∧
      Reach (RStep 3 (d+1)) P.init t ∧ total (d+1) t.H t.U=1 :=
  middle_false_of_boundaryRegular fr (boundaryRegular_of_boundaryHub hub)

/-- (F3) For `d ≥ 2`, the hub law excludes overshoot one. -/
theorem top_overshoot_one_false_of_boundaryHub {d : ℕ} (hd : 2 ≤ d) (hub : BoundaryHub d)
    {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (small : total (d+1) st.H st.U < d+1)
    (excess : O.V.card + 1 = st.U.card + total (d+1) st.H st.U) : False :=
  top_overshoot_one_false hd (threeTight_of_boundaryRegular (by omega) (boundaryRegular_of_boundaryHub hub))
    (boundaryNoPrivate_of_boundaryHub (by omega) hub) fr small excess

/-- (F3) For `d ≥ 2`, under the hub law every positive overshoot is at least two. -/
theorem overshoot_ge_two_of_boundaryHub {d : ℕ} (hd : 2 ≤ d) (hub : BoundaryHub d)
    {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (small : total (d+1) st.H st.U < d+1) {g : ℕ} (positive : 0 < g)
    (gap : O.V.card + g = st.U.card + total (d+1) st.H st.U) : 2 ≤ g :=
  overshoot_ge_two hd (threeTight_of_boundaryRegular (by omega) (boundaryRegular_of_boundaryHub hub))
    (boundaryNoPrivate_of_boundaryHub (by omega) hub) fr small positive gap

/-- (F3) For `d ≥ 2`, under the hub law the third disjunct of `Alternatives` holds with `2 ≤ g`. -/
theorem third_disjunct_two_of_boundaryHub {d : ℕ} (hd : 2 ≤ d) (hub : BoundaryHub d)
    {O : Origin 3 (d+1)} {st : State} (fr : Frontier O st)
    (third : total (d+1) st.H st.U<d+1 ∧ ∃ g e, 0<g ∧
      O.V.card+e=3*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
      let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
      total (d+1) st.H st.U+t*t+t*e≤t*(3+2*g)) :
    total (d+1) st.H st.U<d+1 ∧ ∃ g e, 2≤g ∧
      O.V.card+e=3*(d+1) ∧ O.V.card+g=st.U.card+total (d+1) st.H st.U ∧
      let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
      total (d+1) st.H st.U+t*t+t*e≤t*(3+2*g) :=
  third_disjunct_two hd (threeTight_of_boundaryRegular (by omega) (boundaryRegular_of_boundaryHub hub))
    (boundaryNoPrivate_of_boundaryHub (by omega) hub) fr third

#print axioms tight_rows_of_lower_regular
#print axioms qThreeTight_of_lowerRegular
#print axioms threeTight_of_boundaryRegular
#print axioms qTwoTight_of_lowerRegular
#print axioms twoTight_of_boundaryRegular
#print axioms boundaryNoPrivate_of_inRegular
#print axioms hub_spanning
#print axioms boundaryRegular_of_boundaryHub
#print axioms inRegular_of_boundaryHub
#print axioms boundaryNoPrivate_of_boundaryHub
#print axioms middle_false_of_boundaryHub
#print axioms top_overshoot_one_false_of_boundaryHub
#print axioms overshoot_ge_two_of_boundaryHub
#print axioms third_disjunct_two_of_boundaryHub

end LeanCH.BR.Closure.BoundaryHub
