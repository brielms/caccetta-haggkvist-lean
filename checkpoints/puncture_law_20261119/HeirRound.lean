import LeanCH.BR.BRWeightedSD
import LeanCH.BR.BROutModule
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.LinearCombination

/-! Heir round. If every vertex `a` of a `q`-free host `V` has an heir `v` (an out-neighbour of `a`
whose other in-neighbours all point to `a`), and no proper subset of size `≥ 2` is in-uniform, then
the heir map is one cycle through all of `V` and every out-neighbourhood is an interval after the
vertex on that cycle (`outRound_of_heirs`). For such an out-round digraph, positive unit row weights
of total mass one force constant interval length `r`, `|V| = q r + 1`, and saturation
(`sat_of_outRound`). Together: `sat_of_heirs`. -/

set_option linter.style.longLine false

namespace LeanCH.BR.Closure.HeirRound
open Finset BRq2 WeightedSD

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem bool_true_of_not_false {b : Bool} (h : ¬ b = false) : b = true := by
  cases b <;> simp_all

theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

theorem loop_false {q : ℕ} (hq : 1 ≤ q) {E : CH.Digraph} {V : Finset ℕ} (free : QFree E V q)
    {v : ℕ} (hv : v ∈ V) : ¬ E v v = true := fun h =>
  free v 1 le_rfl hq (.step hv h (.refl v))

theorem per_mul {α : Type*} {f : ℕ → α} {n : ℕ} (per : ∀ k, f (k + n) = f k) (k c : ℕ) :
    f (k + n * c) = f k := by
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, per, ih]

theorem per_mod {α : Type*} {f : ℕ → α} {n : ℕ} (per : ∀ k, f (k + n) = f k) (k : ℕ) :
    f k = f (k % n) := by
  have := per_mul per (k % n) (k / n)
  rwa [Nat.mod_add_div] at this

/-! ## Stage 1: the heir map is one cycle through `V` -/

theorem heir_cycle {q : ℕ} (hq : 1 ≤ q) {E : CH.Digraph} {V : Finset ℕ} (free : QFree E V q)
    (noIn : ∀ U ⊆ V, 2 ≤ U.card → U ≠ V → ¬ BRsub.InUniform E V U)
    {h : ℕ → ℕ} (hV : ∀ a ∈ V, h a ∈ V) (hout : ∀ a ∈ V, E a (h a) = true)
    (hheir : ∀ a ∈ V, ∀ i ∈ V, i ≠ a → E i (h a) = true → E i a = true)
    {z : ℕ} (hz : z ∈ V) :
    ∃ n, ∃ e : ℕ → ℕ, 2 ≤ n ∧ (∀ k, e k ∈ V) ∧ (∀ k, e (k + n) = e k) ∧
      (∀ a < n, ∀ b < n, e a = e b → a = b) ∧ (∀ v ∈ V, ∃ k < n, e k = v) ∧
      (∀ k, h (e k) = e (k + 1)) := by
  classical
  have hit : ∀ x ∈ V, ∀ k, h^[k] x ∈ V := by
    intro x hx k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [Function.iterate_succ_apply']; exact hV _ ih
  obtain ⟨a, -, b, -, hab, heq⟩ : ∃ a ∈ range (V.card + 1), ∃ b ∈ range (V.card + 1),
      a ≠ b ∧ h^[a] z = h^[b] z :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := V) (by simp) (by intro k _; exact hit z hz k)
  obtain ⟨z₀, hz₀, m, hm, hmz⟩ : ∃ z₀ ∈ V, ∃ m, 0 < m ∧ h^[m] z₀ = z₀ := by
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨h^[a] z, hit z hz a, b - a, by omega, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, heq]
    · refine ⟨h^[b] z, hit z hz b, a - b, by omega, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, heq]
  have hex : ∃ p, 0 < p ∧ h^[p] z₀ = z₀ := ⟨m, hm, hmz⟩
  obtain ⟨p, hp0, hpz, hmin⟩ : ∃ p, 0 < p ∧ h^[p] z₀ = z₀ ∧ ∀ c, 0 < c → c < p → h^[c] z₀ ≠ z₀ :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun c hc hcp hcz => Nat.find_min hex hcp ⟨hc, hcz⟩⟩
  have eper : ∀ k, h^[k + p] z₀ = h^[k] z₀ := by
    intro k; rw [Function.iterate_add_apply, hpz]
  have eperm : ∀ k c, h^[k + p * c] z₀ = h^[k] z₀ := per_mul (f := fun k => h^[k] z₀) eper
  have emod : ∀ k, h^[k] z₀ = h^[k % p] z₀ := per_mod (f := fun k => h^[k] z₀) eper
  have einj : ∀ a < p, ∀ b < p, h^[a] z₀ = h^[b] z₀ → a = b := by
    have key : ∀ a b, a < b → b < p → h^[a] z₀ ≠ h^[b] z₀ := by
      intro a b hab hbp heq
      apply hmin (p - b + a) (by omega) (by omega)
      rw [Function.iterate_add_apply, heq, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hbp.le, hpz]
    intro a ha b hb heq
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd heq (key a b h1 hb)
    · exact h1
    · exact absurd heq.symm (key b a h1 ha)
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℕ, Z = (range p).image (fun k => h^[k] z₀) := ⟨_, rfl⟩
  have memZ : ∀ k, h^[k] z₀ ∈ Z := fun k => by
    rw [hZ]; exact mem_image.mpr ⟨k % p, mem_range.mpr (Nat.mod_lt _ hp0), (emod k).symm⟩
  have Zmem : ∀ x ∈ Z, ∃ k, h^[k] z₀ = x := fun x hx => by
    rw [hZ] at hx; obtain ⟨k, -, hk⟩ := mem_image.mp hx; exact ⟨k, hk⟩
  have ZV : Z ⊆ V := by
    intro x hx; obtain ⟨k, rfl⟩ := Zmem x hx; exact hit z₀ hz₀ k
  have hp2 : 2 ≤ p := by
    by_contra hlt
    have hp1 : p = 1 := by omega
    rw [hp1] at hpz
    have := hout z₀ hz₀
    rw [show h z₀ = z₀ from hpz] at this
    exact loop_false hq free hz₀ this
  -- in-uniformity of the heir cycle
  have desc : ∀ x ∈ V, x ∉ Z → ∀ k, E x (h^[k + 1] z₀) = true → E x (h^[k] z₀) = true := by
    intro x hx hxZ k hk
    rw [Function.iterate_succ_apply'] at hk
    exact hheir _ (hit z₀ hz₀ k) x hx (fun hc => hxZ (by rw [hc]; exact memZ k)) hk
  have desc' : ∀ x ∈ V, x ∉ Z → ∀ j k, E x (h^[k + j] z₀) = true → E x (h^[k] z₀) = true := by
    intro x hx hxZ j
    induction j with
    | zero => intro k hk; simpa using hk
    | succ j ih => intro k hk; exact ih k (desc x hx hxZ (k + j) hk)
  have trans : ∀ x ∈ V, x ∉ Z → ∀ a b, E x (h^[a] z₀) = true → E x (h^[b] z₀) = true := by
    intro x hx hxZ a b hab
    apply desc' x hx hxZ (a + p * b - b) b
    have hb : b ≤ p * b := by nlinarith
    have h1 : b + (a + p * b - b) = a + p * b := by omega
    rw [h1, eperm a b]; exact hab
  have unif : BRsub.InUniform E V Z := by
    intro x hx y hy u hu huZ
    obtain ⟨a, rfl⟩ := Zmem x hx
    obtain ⟨b, rfl⟩ := Zmem y hy
    exact bool_eq_of_iff ⟨trans u hu huZ a b, trans u hu huZ b a⟩
  have hcard : 2 ≤ Z.card := by
    have hne : h^[0] z₀ ≠ h^[1] z₀ := fun hc => absurd (einj 0 (by omega) 1 (by omega) hc) (by omega)
    have := Finset.one_lt_card.mpr ⟨_, memZ 0, _, memZ 1, hne⟩
    omega
  have ZeqV : Z = V := by
    by_contra hne; exact noIn Z ZV hcard hne unif
  refine ⟨p, fun k => h^[k] z₀, hp2, fun k => hit z₀ hz₀ k, eper, einj, ?_, ?_⟩
  · intro v hv
    rw [← ZeqV, hZ] at hv
    obtain ⟨k, hk, hkv⟩ := mem_image.mp hv
    exact ⟨k, mem_range.mp hk, hkv⟩
  · intro k; exact (Function.iterate_succ_apply' h k z₀).symm

/-! ## Stage 2: out-neighbourhoods are intervals along the cycle -/

theorem interval_of_heir {q : ℕ} (hq : 1 ≤ q) {E : CH.Digraph} {V : Finset ℕ} (free : QFree E V q)
    {n : ℕ} {e : ℕ → ℕ} (hn : 1 ≤ n)
    (mem : ∀ k, e k ∈ V) (per : ∀ k, e (k + n) = e k) (inj : ∀ a < n, ∀ b < n, e a = e b → a = b)
    (out : ∀ k, E (e k) (e (k + 1)) = true)
    (heir : ∀ k, ∀ x ∈ V, x ≠ e k → E x (e (k + 1)) = true → E x (e k) = true) (i : ℕ) :
    ∃ L, 1 ≤ L ∧ L < n ∧ ∀ d < n, (E (e i) (e (i + d)) = true ↔ 1 ≤ d ∧ d ≤ L) := by
  classical
  have ne : ∀ a d, 1 ≤ d → d < n → e a ≠ e (a + d) := by
    intro a d h1 h2 heq
    rw [per_mod per a, per_mod per (a + d)] at heq
    have := inj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) heq
    have h3 := Nat.sub_mod_eq_zero_of_mod_eq this.symm
    rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt h2] at h3
    omega
  have down : ∀ d, 1 ≤ d → d < n → E (e i) (e (i + d + 1)) = true → E (e i) (e (i + d)) = true :=
    fun d h1 h2 hd => heir (i + d) (e i) (mem i) (ne i d h1 h2) hd
  have desc : ∀ d' d, 1 ≤ d' → d' ≤ d → d < n → E (e i) (e (i + d)) = true →
      E (e i) (e (i + d')) = true := by
    intro d' d h1
    induction d with
    | zero => intro h; omega
    | succ d ih =>
      intro hle hlt hd
      rcases Nat.eq_or_lt_of_le hle with h | h
      · rw [h]; exact hd
      · exact ih (by omega) (by omega) (down d (by omega) (by omega) hd)
  have loop : ∀ k, ¬ E (e k) (e k) = true := fun k => loop_false hq free (mem k)
  have hw : E (e i) (e (i + (n - 1) + 1)) = false := by
    rw [show i + (n - 1) + 1 = i + n by omega, per]; exact bool_false_of_not_true (loop i)
  have hex : ∃ L, E (e i) (e (i + L + 1)) = false := ⟨n - 1, hw⟩
  have hs := Nat.find_spec hex
  have hle := Nat.find_min' hex hw
  refine ⟨Nat.find hex, ?_, by omega, ?_⟩
  · by_contra h0
    have h00 : Nat.find hex = 0 := by omega
    rw [h00, Nat.add_zero] at hs
    have := out i
    rw [hs] at this
    cases this
  · intro d hd
    constructor
    · intro harc
      refine ⟨?_, ?_⟩
      · by_contra h0
        have : d = 0 := by omega
        subst this
        exact loop i harc
      · by_contra hgt
        have h1 := desc (Nat.find hex + 1) d (by omega) (by omega) hd harc
        have h2 : E (e i) (e (i + Nat.find hex + 1)) = true := h1
        rw [hs] at h2
        cases h2
    · rintro ⟨h1, h2⟩
      have hlt : d - 1 < Nat.find hex := by omega
      have h3 := bool_true_of_not_false (Nat.find_min hex hlt)
      rwa [show i + (d - 1) + 1 = i + d by omega] at h3

/-! ## Out-round digraphs -/

/-- `V` is enumerated periodically by `e` (period `n`), and the out-neighbourhood of `e i` is
`{e (i + 1), …, e (i + ℓ i)}`. -/
structure OutRound (E : CH.Digraph) (V : Finset ℕ) (n : ℕ) (e ℓ : ℕ → ℕ) : Prop where
  mem : ∀ k, e k ∈ V
  per : ∀ k, e (k + n) = e k
  inj : ∀ a < n, ∀ b < n, e a = e b → a = b
  surj : ∀ v ∈ V, ∃ k < n, e k = v
  lper : ∀ k, ℓ (k + n) = ℓ k
  lpos : ∀ k, 1 ≤ ℓ k
  llt : ∀ k, ℓ k < n
  arc : ∀ i d, d < n → (E (e i) (e (i + d)) = true ↔ 1 ≤ d ∧ d ≤ ℓ i)

/-- **Stages 1–2.** Heirs and no proper in-uniform set give an out-round digraph. -/
theorem outRound_of_heirs {q : ℕ} (hq : 1 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (free : QFree E V q)
    (noIn : ∀ U ⊆ V, 2 ≤ U.card → U ≠ V → ¬ BRsub.InUniform E V U)
    (heirs : ∀ a ∈ V, ∃ v ∈ V, E a v = true ∧ ∀ i ∈ V, i ≠ a → E i v = true → E i a = true)
    (hne : V.Nonempty) :
    ∃ n e ℓ, OutRound E V n e ℓ := by
  classical
  choose! h hV hout hheir using heirs
  obtain ⟨z, hz⟩ := hne
  obtain ⟨n, e, hn2, emem, eper, einj, esurj, estep⟩ := heir_cycle hq free noIn hV hout hheir hz
  have hint := fun i => interval_of_heir hq free (e := e) (by omega) emem eper einj
    (fun k => by rw [← estep k]; exact hout _ (emem k))
    (fun k x hx hne hx' => hheir _ (emem k) x hx hne (by rw [estep k]; exact hx')) i
  choose L hL1 hLn hLarc using hint
  refine ⟨n, e, fun k => L (k % n), ⟨emem, eper, einj, esurj, ?_, fun k => hL1 _, fun k => hLn _, ?_⟩⟩
  · intro k; simp only [Nat.add_mod_right]
  · intro i d hd
    have h1 : e i = e (i % n) := per_mod eper i
    have h2 : e (i + d) = e (i % n + d) := by
      have : i + d = (i % n + d) + n * (i / n) := by have := Nat.mod_add_div i n; linarith
      rw [this, per_mul eper]
    rw [h1, h2]; exact hLarc (i % n) d hd

#print axioms outRound_of_heirs

/-! ## Stage 3: the greedy chain does not wrap -/

/-- Greedy chain: `t 0 = i`, `t (k+1) = t k + ℓ (t k)` (not reduced mod `n`). -/
def chain (ℓ : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => i
  | k + 1 => chain ℓ i k + ℓ (chain ℓ i k)

theorem chain_succ (ℓ : ℕ → ℕ) (i k : ℕ) : chain ℓ i (k + 1) = chain ℓ i k + ℓ (chain ℓ i k) := rfl

theorem chain_shift (ℓ : ℕ → ℕ) (i j k : ℕ) : chain ℓ (chain ℓ i j) k = chain ℓ i (j + k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [chain_succ, ih]; rfl

section Round
variable {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} {n : ℕ} {e ℓ : ℕ → ℕ}

theorem OutRound.one_le (R : OutRound E V n e ℓ) : 1 ≤ n := by
  have := R.llt 0; omega

theorem chain_ge (R : OutRound E V n e ℓ) (i k : ℕ) : i + k ≤ chain ℓ i k := by
  induction k with
  | zero => exact le_refl i
  | succ k ih => rw [chain_succ]; have := R.lpos (chain ℓ i k); omega

theorem chain_walk (R : OutRound E V n e ℓ) (i k : ℕ) : Walk E V (e i) (e (chain ℓ i k)) k := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    refine ih.snoc (R.mem _) ?_
    exact (R.arc _ _ (R.llt _)).mpr ⟨R.lpos _, le_rfl⟩

theorem chain_lt (R : OutRound E V n e ℓ) (free : QFree E V q) (i : ℕ) :
    ∀ k ≤ q, chain ℓ i k < i + n := by
  intro k
  induction k with
  | zero => intro _; have := R.one_le; show i < i + n; omega
  | succ k ih =>
    intro hk
    have hk' := ih (by omega)
    by_contra hge
    rw [chain_succ] at hge
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have := R.llt i
      have h0' : chain ℓ i 0 = i := rfl
      rw [h0'] at hge
      omega
    · have hge2 := chain_ge R i k
      have harc := (R.arc (chain ℓ i k) (i + n - chain ℓ i k) (by omega)).mpr ⟨by omega, by omega⟩
      rw [show chain ℓ i k + (i + n - chain ℓ i k) = i + n by omega, R.per] at harc
      exact free (e i) (k + 1) (by omega) hk ((chain_walk R i k).snoc (R.mem i) harc)

/-! ## Stage 4: the flat sum -/

theorem image_eq (R : OutRound E V n e ℓ) : (range n).image e = V := by
  ext v; simp only [mem_image, mem_range]; constructor
  · rintro ⟨k, -, rfl⟩; exact R.mem k
  · intro hv; obtain ⟨k, hk, rfl⟩ := R.surj v hv; exact ⟨k, hk, rfl⟩

theorem sum_V (R : OutRound E V n e ℓ) (g : ℕ → ℚ) :
    ∑ u ∈ V, g u = ∑ s ∈ range n, g (e s) := by
  rw [← image_eq R, Finset.sum_image]
  intro a ha b hb hab; exact R.inj a (mem_range.mp ha) b (mem_range.mp hb) hab

theorem sum_range_per {F : ℕ → ℚ} {n : ℕ} (hn : 1 ≤ n) (per : ∀ s, F (s + n) = F s) (a : ℕ) :
    ∑ s ∈ range n, F s = ∑ s ∈ Ico a (a + n), F s := by
  induction a with
  | zero => rw [Nat.zero_add, Finset.range_eq_Ico]
  | succ a ih =>
    rw [ih, show a + 1 + n = a + n + 1 by omega, Finset.sum_Ico_succ_top (by omega : a + 1 ≤ a + n),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : a < a + n), per]
    exact add_comm _ _

theorem outW_eq (R : OutRound E V n e ℓ) (w : ℕ → ℚ) (i : ℕ) :
    outW E V w (e i) = ∑ s ∈ Ico (i + 1) (i + ℓ i + 1), w (e s) := by
  classical
  unfold outW
  rw [sum_V R]
  have hp : ∑ s ∈ range n, (if E (e i) (e s) = true then w (e s) else 0) =
      ∑ s ∈ Ico i (i + n), (if E (e i) (e s) = true then w (e s) else 0) :=
    sum_range_per (F := fun s => if E (e i) (e s) = true then w (e s) else 0) R.one_le
      (fun s => by simp only [R.per]) i
  rw [hp, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext s; simp only [mem_filter, mem_Ico]
  have hl := R.llt i
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have := (R.arc i (s - i) (by omega)).mp (by rw [show i + (s - i) = s by omega]; exact h3)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have := (R.arc i (s - i) (by omega)).mpr ⟨by omega, by omega⟩
    rwa [show i + (s - i) = s by omega] at this

theorem tele (R : OutRound E V n e ℓ) (w : ℕ → ℚ) (i m : ℕ) :
    ∑ k ∈ range m, outW E V w (e (chain ℓ i k)) = ∑ s ∈ Ico (i + 1) (chain ℓ i m + 1), w (e s) := by
  induction m with
  | zero => simp [chain]
  | succ m ih =>
    have h1 := chain_ge R i m
    rw [Finset.sum_range_succ, ih, outW_eq R w, chain_succ,
      Finset.sum_Ico_consecutive _ (by omega : i + 1 ≤ chain ℓ i m + 1)
        (by omega : chain ℓ i m + 1 ≤ chain ℓ i m + ℓ (chain ℓ i m) + 1)]

/-- **Stage 4.** At an index of maximal weight the greedy chain ends just before returning, and every
chain vertex before step `q` has maximal weight. -/
theorem flat (R : OutRound E V n e ℓ) (hq : 1 ≤ q) (free : QFree E V q)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, row q E V w i = 1) (i : ℕ) (hmax : ∀ s, w (e s) ≤ w (e i)) :
    chain ℓ i q + 1 = i + n ∧ ∀ k < q, w (e (chain ℓ i k)) = w (e i) := by
  have hn := R.one_le
  have hlt : chain ℓ i q < i + n := chain_lt R free i q le_rfl
  have hge := chain_ge R i q
  have hrows : ∑ k ∈ range q, row q E V w (e (chain ℓ i k)) = (q : ℚ) := by
    rw [Finset.sum_congr rfl (fun k _ => wr _ (R.mem (chain ℓ i k)))]
    simp
  simp only [row] at hrows
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, tele R w i q] at hrows
  have hmass : ∑ s ∈ Ico i (i + n), w (e s) = 1 := by
    have h1 : ∑ s ∈ range n, w (e s) = ∑ s ∈ Ico i (i + n), w (e s) :=
      sum_range_per (F := fun s => w (e s)) hn (fun s => by simp only [R.per]) i
    have h2 := sum_V R w
    unfold mass at wm
    rw [← h1, ← h2]; exact wm
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : i < i + n),
    ← Finset.sum_Ico_consecutive _ (by omega : i + 1 ≤ chain ℓ i q + 1)
      (by omega : chain ℓ i q + 1 ≤ i + n)] at hmass
  have hT : 0 ≤ ∑ s ∈ Ico (chain ℓ i q + 1) (i + n), w (e s) :=
    Finset.sum_nonneg (fun s _ => (hw _ (R.mem s)).le)
  have hdev : ∑ k ∈ range q, (w (e (chain ℓ i k)) - w (e i)) =
      ∑ k ∈ range q, w (e (chain ℓ i k)) - q * w (e i) := by
    rw [Finset.sum_sub_distrib]; simp
  have hle : ∑ k ∈ range q, (w (e (chain ℓ i k)) - w (e i)) ≤ 0 :=
    Finset.sum_nonpos (fun k _ => by linarith [hmax (chain ℓ i k)])
  have hqT : (q : ℚ) * ∑ s ∈ Ico (chain ℓ i q + 1) (i + n), w (e s) =
      ∑ k ∈ range q, (w (e (chain ℓ i k)) - w (e i)) := by
    rw [hdev]; linear_combination -hrows + (q : ℚ) * hmass
  have hqpos : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hT0 : ∑ s ∈ Ico (chain ℓ i q + 1) (i + n), w (e s) = 0 := by
    apply le_antisymm _ hT
    nlinarith
  refine ⟨?_, ?_⟩
  · by_contra hne
    have hlt' : chain ℓ i q + 1 < i + n := by omega
    have h1 : w (e (chain ℓ i q + 1)) ≤ ∑ s ∈ Ico (chain ℓ i q + 1) (i + n), w (e s) :=
      Finset.single_le_sum (f := fun s => w (e s)) (fun s _ => (hw _ (R.mem s)).le)
        (Finset.left_mem_Ico.mpr hlt')
    have := hw _ (R.mem (chain ℓ i q + 1))
    linarith
  · have hzero : ∑ k ∈ range q, (w (e (chain ℓ i k)) - w (e i)) = 0 := by
      rw [← hqT, hT0, mul_zero]
    have hall := (Finset.sum_eq_zero_iff_of_nonpos
      (fun k _ => by linarith [hmax (chain ℓ i k)])).mp hzero
    intro k hk
    have := hall k (mem_range.mpr hk)
    linarith

/-! ## Stage 5: propagation backwards around the cycle -/

theorem step_back (R : OutRound E V n e ℓ) (hq : 2 ≤ q) (free : QFree E V q)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, row q E V w i = 1) (j : ℕ) (hg : ∀ s, w (e s) ≤ w (e (j + 1))) :
    w (e j) = w (e (j + 1)) ∧ ℓ j = ℓ (j + 1) := by
  obtain ⟨h1, h2⟩ := flat R (by omega) free hw wm wr (j + 1) hg
  have hw1 : w (e (chain ℓ (j + 1) 1)) = w (e (j + 1)) := h2 1 (by omega)
  have hg' : ∀ s, w (e s) ≤ w (e (chain ℓ (j + 1) 1)) := by
    intro s; rw [hw1]; exact hg s
  obtain ⟨h3, h4⟩ := flat R (by omega) free hw wm wr (chain ℓ (j + 1) 1) hg'
  have hcq : chain ℓ (j + 1) q = j + n := by omega
  have h5 := h4 (q - 1) (by omega)
  rw [chain_shift, show 1 + (q - 1) = q by omega, hcq, R.per, hw1] at h5
  rw [chain_shift, show 1 + q = q + 1 by omega, chain_succ, hcq, R.lper] at h3
  have h6 : chain ℓ (j + 1) 1 = j + 1 + ℓ (j + 1) := rfl
  refine ⟨h5, by omega⟩

theorem all_const (R : OutRound E V n e ℓ) (hq : 2 ≤ q) (free : QFree E V q)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, row q E V w i = 1) (N : ℕ) (hg : ∀ s, w (e s) ≤ w (e N)) :
    ∀ m, (∀ s, w (e s) ≤ w (e (N - m))) ∧ ℓ (N - m) = ℓ N := by
  intro m
  induction m with
  | zero => exact ⟨by rw [Nat.sub_zero]; exact hg, by rw [Nat.sub_zero]⟩
  | succ m ih =>
    obtain ⟨g, hl⟩ := ih
    rcases Nat.eq_zero_or_pos (N - m) with h0 | hpos
    · rw [show N - (m + 1) = N - m by omega]; exact ⟨g, hl⟩
    · have hj : N - m = (N - (m + 1)) + 1 := by omega
      rw [hj] at g hl
      obtain ⟨hw', hl'⟩ := step_back R hq free hw wm wr (N - (m + 1)) g
      exact ⟨fun s => by rw [hw']; exact g s, by rw [hl', hl]⟩

/-- **Stage 5.** The interval length is a constant `r`, and `|V| = q r + 1`. -/
theorem round_const (R : OutRound E V n e ℓ) (hq : 2 ≤ q) (free : QFree E V q)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, row q E V w i = 1) :
    ∃ r, (∀ s, ℓ s = r) ∧ n = q * r + 1 := by
  have hn := R.one_le
  obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image V w ⟨e 0, R.mem 0⟩
  obtain ⟨i₀, -, rfl⟩ := R.surj x hx
  obtain ⟨N, hN⟩ : ∃ N, N = i₀ + n := ⟨_, rfl⟩
  have hg : ∀ s, w (e s) ≤ w (e N) := fun s => by rw [hN, R.per]; exact hxmax _ (R.mem s)
  have hall := all_const R hq free hw wm wr N hg
  have hr : ∀ s, ℓ s = ℓ N := by
    intro s
    rw [per_mod R.lper s]
    have hs : s % n < n := Nat.mod_lt _ (by omega)
    have := (hall (N - s % n)).2
    rwa [Nat.sub_sub_self (by omega)] at this
  refine ⟨ℓ N, hr, ?_⟩
  have hc : ∀ k, chain ℓ N k = N + k * ℓ N := by
    intro k
    induction k with
    | zero => simp [chain]
    | succ k ih => rw [chain_succ, ih, hr (N + k * ℓ N)]; ring
  have := (flat R (by omega) free hw wm wr N hg).1
  rw [hc] at this
  omega

/-! ## Stage 6: saturation -/

theorem walk_steps (R : OutRound E V n e ℓ) {r : ℕ} (hr : ∀ s, ℓ s = r) :
    ∀ c i j, j ≤ c * r → ∃ m ≤ c, Walk E V (e i) (e (i + j)) m := by
  intro c
  induction c with
  | zero =>
    intro i j hj
    rw [Nat.zero_mul] at hj
    have : j = 0 := by omega
    subst this
    exact ⟨0, le_rfl, by rw [Nat.add_zero]; exact .refl _⟩
  | succ c ih =>
    intro i j hj
    have hl := R.llt i
    have hp := R.lpos i
    rw [hr] at hl hp
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; exact ⟨0, by omega, by rw [Nat.add_zero]; exact .refl _⟩
    by_cases hjr : j ≤ r
    · refine ⟨1, by omega, .step (R.mem _) ?_ (.refl _)⟩
      exact (R.arc i j (by omega)).mpr ⟨hpos, by rw [hr]; exact hjr⟩
    · rw [Nat.succ_mul] at hj
      obtain ⟨m, hm, hwk⟩ := ih (i + r) (j - r) (by omega)
      rw [show i + r + (j - r) = i + j by omega] at hwk
      exact ⟨m + 1, by omega, .step (R.mem (i + r)) ((R.arc i r (by omega)).mpr ⟨hp, (hr i).ge⟩) hwk⟩

/-- **Stages 3–6.** An out-round `q`-free digraph with positive unit row weights of mass one is
saturated. -/
theorem sat_of_outRound (hq : 2 ≤ q) (R : OutRound E V n e ℓ) (free : QFree E V q)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, row q E V w i = 1) :
    BRsub.Sat q E V := by
  obtain ⟨r, hr, hnr⟩ := round_const R hq free hw wm wr
  have hqr : (q - 1) * r + r = q * r := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul]
  intro v hv u hu hnot
  obtain ⟨i, hi, rfl⟩ := R.surj v hv
  obtain ⟨s, hs, rfl⟩ := R.surj u hu
  rcases eq_or_ne s i with h | h
  · subst h; exact self_mem_ball (R.mem _)
  obtain ⟨j, hj1, hjn, hje⟩ : ∃ j, 1 ≤ j ∧ j < n ∧ e (i + j) = e s := by
    rcases lt_or_gt_of_ne h with h' | h'
    · exact ⟨s + n - i, by omega, by omega, by rw [show i + (s + n - i) = s + n by omega, R.per]⟩
    · exact ⟨s - i, by omega, by omega, by rw [show i + (s - i) = s by omega]⟩
  rw [← hje] at hnot ⊢
  have hjr : j ≤ (q - 1) * r := by
    by_contra hc
    apply hnot
    have := (R.arc (i + j) (n - j) (by omega)).mpr ⟨by omega, by rw [hr]; omega⟩
    rwa [show i + j + (n - j) = i + n by omega, R.per] at this
  obtain ⟨m, hm, hwk⟩ := walk_steps R hr (q - 1) i j hjr
  exact mem_ball.mpr ⟨R.mem _, m, hm, hwk⟩

end Round

/-- **Main theorem.** Heirs, no proper in-uniform set, and a positive unit row law force saturation. -/
theorem sat_of_heirs {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (free : QFree E V q)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1)
    (noIn : ∀ U ⊆ V, 2 ≤ U.card → U ≠ V → ¬ BRsub.InUniform E V U)
    (heirs : ∀ a ∈ V, ∃ v ∈ V, E a v = true ∧ ∀ i ∈ V, i ≠ a → E i v = true → E i a = true) :
    BRsub.Sat q E V := by
  rcases V.eq_empty_or_nonempty with h0 | hne
  · intro v hv; simp [h0] at hv
  · obtain ⟨n, e, ℓ, R⟩ := outRound_of_heirs (by omega) free noIn heirs hne
    exact sat_of_outRound hq R free hw wm wr

#print axioms sat_of_outRound
#print axioms sat_of_heirs

end LeanCH.BR.Closure.HeirRound
