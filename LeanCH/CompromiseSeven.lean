module

public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Card

set_option linter.style.header false

/-!
The unit-weight compromise inequality at exact out-degree seven.
The final theorem explicitly assumes the small induced-subgraph CH bounds and
existence of a Seymour vertex, as allowed in CH_ThinkingPrompt_20261110.md.
It does not assume minimality, a bound on the order, or the weighted compromise
conjecture. This is not a proof of CH in all degrees.
-/

open Finset

public section

namespace CH.CompromiseSeven

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

def outN (v : V) : Finset V := univ.filter (adj v ·)
def inN (v : V) : Finset V := univ.filter (adj · v)
def second (v : V) : Finset V :=
  univ.filter (fun w => w ≠ v ∧ ¬ adj v w ∧ ∃ a, adj v a ∧ adj a w)

omit [DecidableEq V] in
@[simp] lemma mem_outN (v w : V) : w ∈ outN adj v ↔ adj v w := by
  simp [outN]
omit [DecidableEq V] in
@[simp] lemma mem_inN (v w : V) : w ∈ inN adj v ↔ adj w v := by
  simp [inN]
@[simp] lemma mem_second (v w : V) :
    w ∈ second adj v ↔ w ≠ v ∧ ¬ adj v w ∧ ∃ a, adj v a ∧ adj a w := by
  simp [second]

/-- Only induced sets of at most seven vertices are used. -/
@[expose] def LocalSmall : Prop := ∀ S : Finset V, S.Nonempty → S.card ≤ 7 →
  ∃ a ∈ S, (outN adj a ∩ S).card ≤ (S.card - 1) / 3

lemma localSmall_of_induction
    (ih : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 7 →
      (∀ a ∈ S, r ≤ (outN adj a ∩ S).card) → 3 * r < S.card) :
    LocalSmall adj := by
  intro S hn hs
  have hp := card_pos.mpr hn
  by_contra h
  have hm : ∀ a ∈ S, (S.card - 1) / 3 + 1 ≤ (outN adj a ∩ S).card := by
    intro a ha
    have hh : ¬ (outN adj a ∩ S).card ≤ (S.card - 1) / 3 := fun hc => h ⟨a, ha, hc⟩
    omega
  have := ih S ((S.card - 1) / 3 + 1) hn (by omega) (by omega) hm
  omega

lemma double_count (A C : Finset V) :
    ∑ v ∈ A, (outN adj v ∩ C).card = ∑ v ∈ C, (inN adj v ∩ A).card := by
  have ho (v : V) : outN adj v ∩ C = C.filter (adj v ·) := by ext; simp; tauto
  have hi (v : V) : inN adj v ∩ A = A.filter (adj · v) := by ext; simp; tauto
  simp_rw [ho, hi, card_eq_sum_ones, sum_filter]
  exact sum_comm

omit [DecidableEq V] in
lemma total_indegree (R : ℕ) (regular : ∀ v, (outN adj v).card = R) :
    ∑ v, (inN adj v).card = Fintype.card V * R := by
  classical
  have h := double_count adj univ univ
  simpa [regular] using h.symm

omit [DecidableEq V] in
/-- If in-degree is at most R+1, routing every surplus vertex entirely into
strictly deficient vertices is impossible, unless all vertices are balanced. -/
theorem degree_transport (R : ℕ) (hR : 1 ≤ R)
    (regular : ∀ v, (outN adj v).card = R)
    (cap : ∀ v, (inN adj v).card ≤ R + 1)
    (heads : ∀ v, (inN adj v).card = R + 1 →
      ∀ a ∈ outN adj v, (inN adj a).card < R) :
    ∀ v, (inN adj v).card = R := by
  classical
  let H := univ.filter (fun v => (inN adj v).card = R + 1)
  let L := univ.filter (fun v => (inN adj v).card < R)
  have hp (v : V) : (inN adj v).card + (if v ∈ L then 1 else 0) ≤
      R + (if v ∈ H then 1 else 0) := by
    have hc := cap v
    simp only [H, L, mem_filter, mem_univ, true_and]
    split_ifs <;> omega
  have hs := sum_le_sum (s := (univ : Finset V)) (fun v _ => hp v)
  simp only [sum_add_distrib, total_indegree adj R regular, sum_const,
    card_univ, smul_eq_mul] at hs
  have hLsum : ∑ v, (if v ∈ L then 1 else 0 : ℕ) = L.card := by simp
  have hHsum : ∑ v, (if v ∈ H then 1 else 0 : ℕ) = H.card := by simp
  rw [hLsum, hHsum] at hs
  have hLH : L.card ≤ H.card := by omega
  have hsub (v : V) (hv : v ∈ H) : outN adj v ⊆ L := by
    intro a ha
    exact mem_filter.mpr ⟨mem_univ _, heads v (by simpa [H] using hv) a ha⟩
  have hc := double_count adj H L
  have hout : ∑ v ∈ H, (outN adj v ∩ L).card = H.card * R := by
    calc
      _ = ∑ v ∈ H, R := sum_congr rfl (fun v hv => by
        rw [inter_eq_left.mpr (hsub v hv), regular])
      _ = _ := by simp
  have hin : ∑ v ∈ L, (inN adj v ∩ H).card ≤ L.card * (R - 1) := by
    calc
      _ ≤ ∑ v ∈ L, (R - 1) := sum_le_sum (fun v hv => by
        have hh : (inN adj v).card < R := by simpa [L] using hv
        have := card_le_card (inter_subset_left : inN adj v ∩ H ⊆ inN adj v)
        omega)
      _ = _ := by simp
  have he : H.card * R ≤ L.card * (R - 1) := by omega
  have hmul := Nat.mul_le_mul_right (R - 1) hLH
  have hzero : H.card = 0 := by nlinarith [Nat.sub_add_cancel hR]
  have hcapR (v : V) : (inN adj v).card ≤ R := by
    have hc := cap v
    have hn : v ∉ H := by rw [card_eq_zero.mp hzero]; simp
    simp only [H, mem_filter, mem_univ, true_and] at hn
    omega
  intro v
  have hsum : ∑ a, (inN adj a).card = ∑ _a : V, R := by
    simp [total_indegree adj R regular]
  exact (sum_eq_sum_iff_of_le (fun a _ => hcapR a)).mp hsum v (mem_univ _)

omit [Fintype V] in
lemma degree_bound (D A C : Finset V) (h : D ⊆ A ∪ C) :
    D.card ≤ (D ∩ A).card + C.card := by
  have hs : D ⊆ (D ∩ A) ∪ C := by
    intro x hx
    have := h hx
    simp only [mem_union, mem_inter] at *
    tauto
  exact (card_le_card hs).trans (card_union_le _ _)

/-- A quantitative version: each surplus vertex sends at least q edges into
vertices of in-degree at most d. Their deficit budget forbids q*(R-d)>d. -/
theorem degree_transport_quota (R d q : ℕ) (hd : d < R)
    (hq : d < q * (R - d))
    (regular : ∀ v, (outN adj v).card = R)
    (cap : ∀ v, (inN adj v).card ≤ R + 1)
    (heads : ∀ v, (inN adj v).card = R + 1 →
      q ≤ (outN adj v ∩ univ.filter (fun a => (inN adj a).card ≤ d)).card) :
    ∀ v, (inN adj v).card = R := by
  let H := univ.filter (fun v => (inN adj v).card = R + 1)
  let L := univ.filter (fun v => (inN adj v).card ≤ d)
  have hp (v : V) : (inN adj v).card + (if v ∈ L then R - d else 0) ≤
      R + (if v ∈ H then 1 else 0) := by
    have hc := cap v
    simp only [H, L, mem_filter, mem_univ, true_and]
    split_ifs <;> omega
  have hs := sum_le_sum (s := (univ : Finset V)) (fun v _ => hp v)
  simp only [sum_add_distrib, total_indegree adj R regular, sum_const,
    card_univ, smul_eq_mul] at hs
  have hLsum : ∑ v, (if v ∈ L then R - d else 0 : ℕ) = L.card * (R - d) := by simp
  have hHsum : ∑ v, (if v ∈ H then 1 else 0 : ℕ) = H.card := by simp
  rw [hLsum, hHsum] at hs
  have hbudget : L.card * (R - d) ≤ H.card := by omega
  have hc := double_count adj H L
  have hout : H.card * q ≤ ∑ v ∈ H, (outN adj v ∩ L).card := by
    calc
      _ = ∑ _v ∈ H, q := by simp
      _ ≤ _ := sum_le_sum (fun v hv => heads v (by simpa [H] using hv))
  have hin : ∑ v ∈ L, (inN adj v ∩ H).card ≤ L.card * d := by
    calc
      _ ≤ ∑ v ∈ L, d := sum_le_sum (fun v hv => by
        have hh : (inN adj v).card ≤ d := by simpa [L] using hv
        exact (card_le_card inter_subset_left).trans hh)
      _ = _ := by simp
  have hedge : H.card * q ≤ L.card * d := by omega
  have hzero : H.card = 0 := by
    have h1 := Nat.mul_le_mul_right (R - d) hedge
    have h2 := Nat.mul_le_mul_right d hbudget
    nlinarith
  have hcapR (v : V) : (inN adj v).card ≤ R := by
    have hc := cap v
    have hn : v ∉ H := by rw [card_eq_zero.mp hzero]; simp
    simp only [H, mem_filter, mem_univ, true_and] at hn
    omega
  intro v
  have hsum : ∑ a, (inN adj a).card = ∑ _a : V, R := by
    simp [total_indegree adj R regular]
  exact (sum_eq_sum_iff_of_le (fun a _ => hcapR a)).mp hsum v (mem_univ _)

lemma heads_two_steps (noDigon : ∀ u v, adj u v → ¬ adj v u)
    {v a : V} (ha : a ∈ outN adj v) :
    outN adj a ⊆ outN adj v ∪ second adj v := by
  intro w hw
  by_cases hvw : adj v w
  · exact mem_union_left _ (by simpa using hvw)
  · apply mem_union_right
    apply (mem_second adj v w).mpr
    refine ⟨?_, hvw, a, by simpa using ha, by simpa using hw⟩
    intro heq
    subst w
    exact noDigon v a (by simpa using ha) (by simpa using hw)

lemma second_ge_five (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (small : LocalSmall adj) (regular : ∀ v, (outN adj v).card = 7) (v : V) :
    5 ≤ (second adj v).card := by
  obtain ⟨a, ha, hsmall⟩ := small (outN adj v)
    (card_pos.mp (by rw [regular]; omega)) (by rw [regular])
  have hb := degree_bound (outN adj a) (outN adj v) (second adj v)
    (heads_two_steps adj noDigon ha)
  rw [regular] at hb
  rw [regular] at hsmall
  omega

lemma local_degree_bound (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : LocalSmall adj) (S : Finset V) (hsize : S.card ≤ 8)
    (hmin : ∀ a ∈ S, 2 ≤ (outN adj a ∩ S).card)
    (v : V) (hv : v ∈ S) :
    (inN adj v ∩ S).card + (outN adj v ∩ S).card + 3 ≤
      S.card + ((outN adj v ∩ S).card - 1) / 3 := by
  let W := outN adj v ∩ S
  have hW : W ⊆ S := inter_subset_right
  have hpos : 0 < W.card := by
    change 0 < (outN adj v ∩ S).card
    have := hmin v hv
    omega
  have hvnotW : v ∉ W := by simp [W, loopless]
  have hWsize : W.card ≤ 7 := by
    have hc := card_le_card (insert_subset hv hW)
    rw [card_insert_of_notMem hvnotW] at hc
    omega
  obtain ⟨a, ha, hsmall⟩ := small W (card_pos.mp hpos)
    hWsize
  have hva : adj v a := (mem_outN adj v a).mp (mem_inter.mp ha).1
  have haS : a ∈ S := (mem_inter.mp ha).2
  let I := inN adj v ∩ S
  let D := (outN adj a ∩ S) \ W
  have hI : I ⊆ S := inter_subset_right
  have hD : D ⊆ S := fun x hx => (mem_inter.mp (mem_sdiff.mp hx).1).2
  have hvI : v ∉ I := by simp [I, loopless]
  have hvW : v ∉ W := by simp [W, loopless]
  have hvD : v ∉ D := by
    simp only [D, mem_sdiff, mem_inter, mem_outN]
    exact fun h => noDigon v a hva h.1.1
  have hIW : Disjoint I W := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact noDigon v x ((mem_outN adj v x).mp (mem_inter.mp hx').1)
      ((mem_inN adj v x).mp (mem_inter.mp hx).1)
  have hID : Disjoint I D := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact noTri v a x hva
      ((mem_outN adj a x).mp (mem_inter.mp (mem_sdiff.mp hx').1).1)
      ((mem_inN adj v x).mp (mem_inter.mp hx).1)
  have hWD : Disjoint W D := disjoint_left.mpr (fun _ hx hx' => (mem_sdiff.mp hx').2 hx)
  have hsub : insert v (I ∪ W ∪ D) ⊆ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hv
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hx | hx
      · exact hI hx
      · exact hW hx
    · exact hD hx
  have hc := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hvI, hvW, hvD]),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨hID, hWD⟩),
    card_union_of_disjoint hIW] at hc
  have hsplit := card_sdiff_add_card_inter (outN adj a ∩ S) W
  have heq : (outN adj a ∩ S) ∩ W = outN adj a ∩ W := by
    ext x
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hW h.2⟩, h.2⟩⟩
  rw [heq] at hsplit
  have hamin := hmin a haS
  change D.card + (outN adj a ∩ W).card = _ at hsplit
  change I.card + W.card + 3 ≤ S.card + (W.card - 1) / 3
  omega

lemma rigid_seven (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : LocalSmall adj) (A : Finset V) (hA : A.card = 7)
    (hmin : ∀ a ∈ A, 2 ≤ (outN adj a ∩ A).card) :
    ∀ a ∈ A, (outN adj a ∩ A).card = 2 := by
  have hcap (a : V) (ha : a ∈ A) : (inN adj a ∩ A).card ≤ 2 := by
    have hb := local_degree_bound adj loopless noDigon noTri small A (by omega) hmin a ha
    have hm := hmin a ha
    have hs : (outN adj a ∩ A).card ≤ 7 := hA ▸ card_le_card inter_subset_right
    omega
  have hsum := double_count adj A A
  have hupper : ∑ a ∈ A, (inN adj a ∩ A).card ≤ ∑ _a ∈ A, 2 :=
    sum_le_sum hcap
  have hlower : ∑ _a ∈ A, 2 ≤ ∑ a ∈ A, (outN adj a ∩ A).card :=
    sum_le_sum hmin
  have heq : ∑ a ∈ A, 2 = ∑ a ∈ A, (outN adj a ∩ A).card := by omega
  intro a ha
  exact ((sum_eq_sum_iff_of_le hmin).mp heq a ha).symm

lemma second_inside_two_of_min (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (small : LocalSmall adj) (A : Finset V)
    (hmin : ∀ a ∈ A, 2 ≤ (outN adj a ∩ A).card)
    (a : V) (hrow : (outN adj a ∩ A).card = 2) :
    2 ≤ (second adj a ∩ A).card := by
  let W := outN adj a ∩ A
  have hW : W.card = 2 := hrow
  obtain ⟨b, hb, hsmall⟩ := small W (card_pos.mp (by omega)) (by omega)
  have hab : adj a b := (mem_outN adj a b).mp (mem_inter.mp hb).1
  have hbA : b ∈ A := (mem_inter.mp hb).2
  have hzero : outN adj b ∩ W = ∅ := card_eq_zero.mp (by omega)
  have hsub : outN adj b ∩ A ⊆ second adj a ∩ A := by
    intro x hx
    have hbx : adj b x := (mem_outN adj b x).mp (mem_inter.mp hx).1
    have hxA := (mem_inter.mp hx).2
    refine mem_inter.mpr ⟨(mem_second adj a x).mpr ⟨?_, ?_, b, hab, hbx⟩, hxA⟩
    · intro heq
      subst x
      exact noDigon a b hab hbx
    · intro hax
      have hmem : x ∈ outN adj b ∩ W :=
        mem_inter.mpr ⟨by simpa using hbx, mem_inter.mpr ⟨by simpa using hax, hxA⟩⟩
      rw [hzero] at hmem
      exact notMem_empty x hmem
  have hc := card_le_card hsub
  exact (hmin b hbA).trans hc

lemma high_heads_low (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : LocalSmall adj) (regular : ∀ v, (outN adj v).card = 7)
    (bad : ∀ v, (second adj v).card + (inN adj v).card < 14)
    (v : V) (high : (inN adj v).card = 8) :
    ∀ a ∈ outN adj v, (inN adj a).card ≤ 5 := by
  let A := outN adj v
  let Z := second adj v
  have hA : A.card = 7 := regular v
  have hZ : Z.card = 5 := by
    have := second_ge_five adj noDigon small regular v
    have := bad v
    dsimp [Z]
    omega
  have hheads (a : V) (ha : a ∈ A) : outN adj a ⊆ A ∪ Z :=
    heads_two_steps adj noDigon ha
  have hmin (a : V) (ha : a ∈ A) : 2 ≤ (outN adj a ∩ A).card := by
    have := degree_bound (outN adj a) A Z (hheads a ha)
    rw [regular, hZ] at this
    omega
  have rigid := rigid_seven adj loopless noDigon noTri small A hA hmin
  have complete (a : V) (ha : a ∈ A) : Z ⊆ outN adj a := by
    have hsub : outN adj a \ A ⊆ Z := by
      intro z hz
      have hh := hheads a ha (mem_sdiff.mp hz).1
      rcases mem_union.mp hh with hh | hh
      · exact False.elim ((mem_sdiff.mp hz).2 hh)
      · exact hh
    have hc := card_sdiff_add_card_inter (outN adj a) A
    rw [regular, rigid a ha] at hc
    have heq : outN adj a \ A = Z := eq_of_subset_of_card_le hsub (by omega)
    rw [← heq]
    exact sdiff_subset
  let T := (Z.biUnion (outN adj)) \ Z
  have headsZ (z : V) (hz : z ∈ Z) : outN adj z ⊆ Z ∪ T := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · exact mem_union_left _ hxZ
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨z, hz, hx⟩, hxZ⟩)
  obtain ⟨z, hz, hsmall⟩ := small Z (card_pos.mp (by omega)) (by omega)
  have hT : 6 ≤ T.card := by
    have hb := degree_bound (outN adj z) Z T (headsZ z hz)
    rw [regular] at hb
    rw [hZ] at hsmall
    omega
  have hTA : Disjoint T A := by
    apply disjoint_left.mpr
    intro x hx hxA
    obtain ⟨z, hz, hzx⟩ := mem_biUnion.mp (mem_sdiff.mp hx).1
    exact noDigon x z (by simpa using complete x hxA hz) (by simpa using hzx)
  intro a ha
  have hTsecond : T ⊆ second adj a := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := mem_biUnion.mp (mem_sdiff.mp hx).1
    have hxA : x ∉ A := fun hh => disjoint_left.mp hTA hx hh
    have hxZ : x ∉ Z := (mem_sdiff.mp hx).2
    apply (mem_second adj a x).mpr
    refine ⟨?_, ?_, z, by simpa using complete a ha hz, by simpa using hzx⟩
    · intro heq
      subst x
      exact hxA ha
    · intro hax
      have hh := hheads a ha (by simpa using hax)
      rcases mem_union.mp hh with hh | hh
      · exact hxA hh
      · exact hxZ hh
  have hins := second_inside_two_of_min adj noDigon small A hmin a (rigid a ha)
  have hdisj : Disjoint T (second adj a ∩ A) := hTA.mono_right inter_subset_right
  have hc := card_le_card (union_subset hTsecond
    (inter_subset_left : second adj a ∩ A ⊆ second adj a))
  rw [card_union_of_disjoint hdisj] at hc
  have hb := bad a
  omega

/-- The compromise inequality for exact out-degree seven, from precisely the
small-set induction and Seymour hypotheses supplied by the thinking prompt. -/
theorem compromise_seven (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : LocalSmall adj) (regular : ∀ v, (outN adj v).card = 7)
    (seymour : ∃ v, 7 ≤ (second adj v).card) :
    ∃ v, 14 ≤ (second adj v).card + (inN adj v).card := by
  by_contra hn
  have bad (v : V) : (second adj v).card + (inN adj v).card < 14 := by
    have : ¬ 14 ≤ (second adj v).card + (inN adj v).card := fun h => hn ⟨v, h⟩
    omega
  have cap (v : V) : (inN adj v).card ≤ 8 := by
    have := second_ge_five adj noDigon small regular v
    have := bad v
    omega
  have balanced := degree_transport adj 7 (by omega) regular cap (by
    intro v hv a ha
    have := high_heads_low adj loopless noDigon noTri small regular bad v hv a ha
    omega)
  obtain ⟨v, hv⟩ := seymour
  have := bad v
  have := balanced v
  omega

end CH.CompromiseSeven

#print axioms CH.CompromiseSeven.degree_transport
#print axioms CH.CompromiseSeven.high_heads_low
#print axioms CH.CompromiseSeven.compromise_seven
