import LeanCH.BR.BRWeightedStrictPrime

/-! Serial chains in saturated graphs. All lengths and cutoffs are variable.
A single serial arc need not force a module. A chain of q-1 such arcs does.
-/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

structure SerialChain (D : CH.Digraph) (V : Finset ℕ) (l : ℕ) where
  vertex : ℕ → ℕ
  mem : ∀ i, i ≤ l → vertex i ∈ V
  outgoing : ∀ i, i < l → ∀ z ∈ V,
    D (vertex i) z = true ↔ z = vertex (i + 1)
  incoming : ∀ i, i < l → ∀ z ∈ V,
    D z (vertex (i + 1)) = true ↔ z = vertex i

namespace SerialChain
variable {D : CH.Digraph} {V : Finset ℕ} {l : ℕ} (P : SerialChain D V l)

def support : Finset ℕ := (Finset.range (l + 1)).image P.vertex

theorem mem_support {i : ℕ} (hi : i ≤ l) : P.vertex i ∈ P.support :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

theorem support_subset : P.support ⊆ V := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  exact P.mem i (by have := Finset.mem_range.mp hi; omega)

theorem forced_end {i k z : ℕ} (hik : i + k ≤ l)
    (h : Walk D V (P.vertex i) z k) : z = P.vertex (i + k) := by
  induction k generalizing i with
  | zero => cases h; simp
  | succ k ih =>
    cases h with
    | @step _ b _ _ hb hab tail =>
      have he := (P.outgoing i (by omega) b hb).mp hab
      subst b
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (i := i + 1) (by omega) tail

theorem drop_prefix {i d k z : ℕ} (hid : i + d ≤ l)
    (h : Walk D V (P.vertex i) z (d + k)) :
    Walk D V (P.vertex (i + d)) z k := by
  induction d generalizing i with
  | zero => simpa using h
  | succ d ih =>
    have hh : Walk D V (P.vertex i) z ((d + k) + 1) := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    cases hh with
    | @step _ b _ _ hb hab tail =>
      have he := (P.outgoing i (by omega) b hb).mp hab
      subst b
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (i := i + 1) (by omega) tail

def reverse : SerialChain (fun x y => D y x) V l where
  vertex i := P.vertex (l - i)
  mem i hi := P.mem _ (Nat.sub_le _ _)
  outgoing i hi z hz := by
    have he : l - (i + 1) + 1 = l - i := by omega
    simpa only [he] using P.incoming (l - (i + 1)) (by omega) z hz
  incoming i hi z hz := by
    have he : l - (i + 1) + 1 = l - i := by omega
    simpa only [he] using P.outgoing (l - (i + 1)) (by omega) z hz

theorem reverse_support : P.reverse.support = P.support := by
  ext z
  constructor <;> intro hz
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact P.mem_support (Nat.sub_le _ _)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hi' : i ≤ l := by have := Finset.mem_range.mp hi; omega
    have hh := P.reverse.mem_support (i := l - i) (Nat.sub_le _ _)
    simpa only [reverse, Nat.sub_sub_self hi'] using hh

theorem terminal_heads_outside (hl : 1 ≤ l) (hsat : Sat (l + 1) D V)
    {z : ℕ} (hz : z ∈ V) (hn : z ∉ P.support) : D (P.vertex l) z = true := by
  have hnot : ¬ D z (P.vertex 1) = true := by
    intro he
    have hh := (P.incoming 0 (by omega) z hz).mp he
    exact hn (hh ▸ P.mem_support (i := 0) (by omega))
  obtain ⟨_, k, hk, hwalk⟩ := mem_ball.mp (hsat (P.vertex 1) (P.mem 1 hl) z hz hnot)
  have hklo : l - 1 ≤ k := by
    by_contra hlt
    have he := P.forced_end (i := 1) (by omega : 1 + k ≤ l) hwalk
    exact hn (he ▸ P.mem_support (by omega))
  have htail : Walk D V (P.vertex l) z (k - (l - 1)) := by
    have hh : Walk D V (P.vertex 1) z ((l - 1) + (k - (l - 1))) := by
      simpa only [Nat.add_sub_of_le hklo] using hwalk
    have ht := P.drop_prefix (i := 1) (d := l - 1) (by omega) hh
    simpa only [show 1 + (l - 1) = l by omega] using ht
  have hlen : k - (l - 1) = 1 := by
    have hnzero : k - (l - 1) ≠ 0 := by
      intro he
      rw [he] at htail
      have hzlast := walk_zero htail
      exact hn (hzlast ▸ P.mem_support le_rfl)
    omega
  rw [hlen] at htail
  exact (walk_one htail).2

theorem sat_reverse {q : ℕ} (hsat : Sat q D V) : Sat q (fun x y => D y x) V := by
  intro v hv z hz hnot
  obtain ⟨_, k, hk, hw⟩ := mem_ball.mp (hsat z hz v hv hnot)
  exact mem_ball.mpr ⟨hz, k, hk, hw.reverse_of_mem hz⟩

theorem outside_heads_initial (hl : 1 ≤ l) (hsat : Sat (l + 1) D V)
    {z : ℕ} (hz : z ∈ V) (hn : z ∉ P.support) : D z (P.vertex 0) = true := by
  have hh := P.reverse.terminal_heads_outside hl (sat_reverse hsat) hz
    (by rwa [P.reverse_support])
  simpa only [reverse, Nat.sub_self] using hh

theorem outside_module (hl : 1 ≤ l) (hsat : Sat (l + 1) D V) :
    OutUniform D V (V \ P.support) := by
  intro x hx y hy z hz hn
  have hxs := (Finset.mem_sdiff.mp hx).2
  have hys := (Finset.mem_sdiff.mp hy).2
  have hzS : z ∈ P.support := by
    by_contra h
    exact hn (Finset.mem_sdiff.mpr ⟨hz, h⟩)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hzS
  have hil : i ≤ l := by have := Finset.mem_range.mp hi; omega
  by_cases hi0 : i = 0
  · subst i
    rw [P.outside_heads_initial hl hsat (Finset.mem_sdiff.mp hx).1 hxs,
      P.outside_heads_initial hl hsat (Finset.mem_sdiff.mp hy).1 hys]
  · have hxnot : ¬ D x (P.vertex i) = true := by
      intro he
      have hh := (P.incoming (i - 1) (by omega) x (Finset.mem_sdiff.mp hx).1).mp
        (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using he)
      exact hxs (hh ▸ P.mem_support (by omega))
    have hynot : ¬ D y (P.vertex i) = true := by
      intro he
      have hh := (P.incoming (i - 1) (by omega) y (Finset.mem_sdiff.mp hy).1).mp
        (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using he)
      exact hys (hh ▸ P.mem_support (by omega))
    exact (Bool.eq_false_iff.mpr hxnot).trans (Bool.eq_false_iff.mpr hynot).symm

end SerialChain

theorem minOut_one_of_strict {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v) :
    ∀ v ∈ V, 1 ≤ (outN D V v).card := by
  intro v hv
  by_contra hnone
  have hout : outW D V w v = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have hnot : ¬ D v u = true := by
      intro he
      have hh := Finset.card_pos.mpr ⟨u, mem_outN.mpr ⟨hu, he⟩⟩
      omega
    simp [hnot]
  have hle : w v ≤ mass V w := Finset.single_le_sum hw hv
  have hh := hr v hv
  rw [row, hout, mul_zero, add_zero] at hh
  exact (not_lt_of_ge hle) hh

/-- The degree-one boundary theorem supplies a weighted base case for
every cutoff, even when the weights have zero coordinates. -/
theorem smallRow_of_card_le_succ {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hcard : V.card ≤ q + 1) : SmallRow q D V := by
  intro w hw hV
  by_contra hn
  have hr : ∀ v ∈ V, mass V w < row q D V w v := by
    intro v hv
    exact lt_of_not_ge (fun hh => hn ⟨v, hv, hh⟩)
  have hmin := minOut_one_of_strict w hw hr
  have hlo := dt_size hq (ball_q_one q hq) hf hmin hV
  have heq : V.card = q + 1 := by omega
  have hin := (dt_reg hq (ball_q_one q hq) hf hmin (by omega)).2
  have hsum : (∑ v ∈ V, outW D V w v) = mass V w := by
    unfold outW mass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    have he : (∑ v ∈ V, if D v u = true then w u else 0) =
        w u * inW D V (fun _ => 1) u := by
      simp only [inW, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      split_ifs <;> simp
    rw [he, inW_unit, hin u hu]
    simp
  have hsrow : (∑ v ∈ V, row q D V w v) = ((q : ℚ) + 1) * mass V w := by
    simp only [row, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    change mass V w + (q : ℚ) * mass V w = _
    ring
  have hstrict : (∑ _v ∈ V, mass V w) < ∑ v ∈ V, row q D V w v := by
    apply Finset.sum_lt_sum (fun v hv => (hr v hv).le)
    obtain ⟨v, hv⟩ := hV
    exact ⟨v, hv, hr v hv⟩
  rw [hsrow] at hstrict
  simp only [Finset.sum_const, nsmul_eq_mul, heq, Nat.cast_add, Nat.cast_one] at hstrict
  exact (lt_irrefl _) hstrict

/-- A long serial chain either has a genuine outside module, or the host
has at most q+1 vertices. Both branches are paid by checked induction. -/
theorem smallRow_of_serial_chain {l : ℕ} (hl : 1 ≤ l)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V (l + 1))
    (hsat : Sat (l + 1) D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow (l + 1) D U)
    (P : SerialChain D V l) : SmallRow (l + 1) D V := by
  let M := V \ P.support
  by_cases hM : 2 ≤ M.card
  · apply smallRow_of_proper_module (by omega) hf hsat hproper
      (Finset.sdiff_subset) hM
    · intro he
      have hh : P.vertex 0 ∈ M := by
        change P.vertex 0 ∈ V \ P.support
        rw [he]
        exact P.mem 0 (by omega)
      exact (Finset.mem_sdiff.mp hh).2 (P.mem_support (by omega))
    · exact P.outside_module hl hsat
  · apply smallRow_of_card_le_succ (by omega) hf
    have hs : P.support.card ≤ l + 1 :=
      (Finset.card_image_le).trans (by rw [Finset.card_range])
    have hc : M.card + P.support.card = V.card :=
      Finset.card_sdiff_add_card_eq_card P.support_subset
    omega

theorem no_long_serial_chain {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (hs : StrictPositiveRows q D V) : ¬ Nonempty (SerialChain D V (q - 1)) := by
  rintro ⟨P⟩
  have he : q - 1 + 1 = q := by omega
  have hsmall := smallRow_of_serial_chain (l := q - 1) (by omega)
    (by rwa [he]) (by rwa [he]) (by simpa only [he] using hproper) P
  rw [he] at hsmall
  obtain ⟨w, hw, hm, hr⟩ := hs
  exact hsmall.no_strict ⟨P.vertex 0, P.mem 0 (by omega)⟩ w
    (fun v hv => (hw v hv).le) (fun v hv => by rw [hm]; exact hr v hv)

theorem single_successor_unique_parent {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v)
    (hc : ∀ v ∈ V, mass V p < col q D V p v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V)
    (hout : ∀ z ∈ V, D x z = true ↔ z = y) :
    ∀ z ∈ V, D z y = true ↔ z = x := by
  intro z hz
  constructor
  · intro he
    by_contra hne
    apply strict_no_outgoing_domination hsmall hf p hp hc hx hz (Ne.symm hne)
    intro u hu hxu
    rw [(hout u (Finset.mem_erase.mp hu).2).mp hxu]
    exact he
  · intro he
    subst z
    exact (hout y hy).mpr rfl

theorem serialChain_of_strict_successors {q l : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hsrev : StrictPositiveRows q (fun x y => D y x) V)
    (a : ℕ → ℕ) (ha : ∀ i, i ≤ l → a i ∈ V)
    (hout : ∀ i, i < l → ∀ z ∈ V, D (a i) z = true ↔ z = a (i + 1)) :
    Nonempty (SerialChain D V l) := by
  obtain ⟨p, hp, hm, hc⟩ := hsrev
  have hcp : ∀ v ∈ V, mass V p < col q D V p v := by
    intro v hv
    rw [hm]
    exact hc v hv
  refine ⟨⟨a, ha, hout, ?_⟩⟩
  intro i hi
  exact single_successor_unique_parent hsmall hf p (fun v hv => (hp v hv).le) hcp
    (ha i (by omega)) (ha (i + 1) (by omega)) (hout i hi)

/-- Every vertex of a strict minimal host reaches a branching row before
q-1 steps. This is an all-cutoff structural restriction, not a claim that
single serial arcs are impossible. -/
theorem branching_within_cutoff {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hsmall : SmallerSmallRow q V.card) (hs : StrictPositiveRows q D V)
    (hsrev : StrictPositiveRows q (fun x y => D y x) V)
    {x : ℕ} (hx : x ∈ V) :
    ∃ y ∈ ball D V x (q - 2), 2 ≤ (outN D V y).card := by
  classical
  have hs' := hs
  obtain ⟨w, hw, hm, hr⟩ := hs'
  have hmin := minOut_one_of_strict w (fun v hv => (hw v hv).le)
    (fun v hv => by rw [hm]; exact hr v hv)
  have hex : ∀ v, ∃ z, v ∈ V → z ∈ V ∧ D v z = true := by
    intro v
    by_cases hv : v ∈ V
    · obtain ⟨z, hz⟩ := Finset.card_pos.mp (hmin v hv)
      exact ⟨z, fun _ => mem_outN.mp hz⟩
    · exact ⟨0, fun h => (hv h).elim⟩
  choose next hnext using hex
  let a : ℕ → ℕ := fun i => next^[i] x
  have ha : ∀ i, a i ∈ V := by
    intro i
    induction i with
    | zero => exact hx
    | succ i ih =>
      change next^[i + 1] x ∈ V
      rw [Function.iterate_succ_apply']
      exact (hnext _ ih).1
  have hedge : ∀ i, D (a i) (a (i + 1)) = true := by
    intro i
    change D (a i) (next^[i + 1] x) = true
    rw [Function.iterate_succ_apply']
    exact (hnext _ (ha i)).2
  have hwalk : ∀ i, Walk D V x (a i) i := by
    intro i
    exact walk_of_edges (f := a) (fun j _ => ⟨ha (j + 1), hedge j⟩)
  by_contra hn
  have hdeg : ∀ i, i < q - 1 → (outN D V (a i)).card ≤ 1 := by
    intro i hi
    have hb : a i ∈ ball D V x (q - 2) :=
      mem_ball.mpr ⟨ha i, i, by omega, hwalk i⟩
    have hh : ¬ 2 ≤ (outN D V (a i)).card := fun h => hn ⟨a i, hb, h⟩
    omega
  have hout : ∀ i, i < q - 1 → ∀ z ∈ V,
      D (a i) z = true ↔ z = a (i + 1) := by
    intro i hi z hz
    constructor
    · intro he
      exact Finset.card_le_one.mp (hdeg i hi) z (mem_outN.mpr ⟨hz, he⟩)
        (a (i + 1)) (mem_outN.mpr ⟨ha (i + 1), hedge i⟩)
    · intro he
      rw [he]
      exact hedge i
  exact no_long_serial_chain hq hf hsat (hsmall.induced hf) hs
    (serialChain_of_strict_successors hsmall hf hsrev a (fun i _ => ha i) hout)

end LeanCH.BR.WeightedSD
