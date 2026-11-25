import checkpoints.shen_extension.CollarLedger

/-!
# The bank count: short savers are outvoted by their banks

A purely combinatorial count on the two-ball ledger of `ReachLedger` at radii `i + j ≤ q`.
The *score* of a row `v` is `(ball D V v i).card + (ball D V v j).card`, the *level* `|V| + 1`.

Savers `S ⊆ V` may fall short of the level. Each saver `u` has a class `cls u`, each class `c` a
bank `bank c ⊆ V` of at least `b` rows. `mult S cls bank x` counts the classes (among
`S.image cls`) whose bank contains `x`; a bank row pays `π` above the level for each class it
serves. Savers of one class are pairwise gaps. If every class pays more through its bank than
its savers can recover, there is no saver.

* `core`: the count for an arbitrary row value `f` with `∑ f ≤ |V| L`.
* `bank_count_gen`: per-saver shortfalls `d`, per-class condition
  `∑_{class} d + m < m * m + b * π` (`m` the number of savers of the class).
* `bank_count`: uniform shortfall `δ` and `∀ m, m (δ + 1) < m * m + b π`.
* `bank_count_disjoint`: disjoint banks, every bank row `π` above the level.
* `no_thin_of_bank_count`: `CollarLedger.no_thin` re-derived from `bank_count_disjoint`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.BankCount
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer)
open ReachLedger (gap mem_gap ledger)
open CollarLedger (loops_equal twin_gap)

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-- The savers of class `c`. -/
def fiber (S : Finset ℕ) (cls : ℕ → ℕ) (c : ℕ) : Finset ℕ := S.filter (fun w => cls w = c)

/-- The number of classes whose bank contains `x`. -/
def mult (S : Finset ℕ) (cls : ℕ → ℕ) (bank : ℕ → Finset ℕ) (x : ℕ) : ℕ :=
  ((S.image cls).filter (fun c => x ∈ bank c)).card

theorem sum_mult {S : Finset ℕ} {cls : ℕ → ℕ} {bank : ℕ → Finset ℕ}
    (bankV : ∀ u ∈ S, bank (cls u) ⊆ V) :
    ∑ x ∈ V, mult S cls bank x = ∑ c ∈ S.image cls, (bank c).card := by
  simp only [mult, card_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun c hc => ?_)
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hc
  rw [← card_filter, filter_mem_eq_inter, inter_eq_right.mpr (bankV u hu)]

theorem sum_fiber {S : Finset ℕ} {cls : ℕ → ℕ} (g : ℕ → ℕ) :
    ∑ c ∈ S.image cls, ∑ w ∈ fiber S cls c, g w = ∑ u ∈ S, g u :=
  sum_fiberwise_of_maps_to (fun _u hu => mem_image_of_mem cls hu) g

theorem sum_fiber_card {S : Finset ℕ} {cls : ℕ → ℕ} :
    ∑ u ∈ S, (fiber S cls (cls u)).card =
      ∑ c ∈ S.image cls, (fiber S cls c).card * (fiber S cls c).card := by
  rw [← sum_fiber (fun w => (fiber S cls (cls w)).card)]
  refine sum_congr rfl (fun c _ => ?_)
  have : ∀ w ∈ fiber S cls c, (fiber S cls (cls w)).card = (fiber S cls c).card := by
    intro w hw
    rw [(mem_filter.mp hw).2]
  rw [sum_congr rfl this, sum_const, smul_eq_mul]

/-- **The count.** Row values `f` summing to at most `|V| L`. A saver `u` of a class with `m`
savers is at least `L + m + π k(u)` once its shortfall `d u` and one are added back; every other
row is at least `L + π k`. If every class has `∑ d + m < m * m + b π`, there is no saver. -/
theorem core {S : Finset ℕ} {cls : ℕ → ℕ} {bank : ℕ → Finset ℕ} {f d : ℕ → ℕ} {L b π : ℕ}
    (sv : S ⊆ V) (total : ∑ v ∈ V, f v ≤ V.card * L)
    (bankV : ∀ u ∈ S, bank (cls u) ⊆ V) (bcard : ∀ u ∈ S, b ≤ (bank (cls u)).card)
    (classpay : ∀ u ∈ S, ∑ w ∈ fiber S cls (cls u), d w + (fiber S cls (cls u)).card
      < (fiber S cls (cls u)).card * (fiber S cls (cls u)).card + b * π)
    (rowS : ∀ u ∈ S, L + (fiber S cls (cls u)).card + π * mult S cls bank u ≤ f u + d u + 1)
    (rowO : ∀ v ∈ V \ S, L + π * mult S cls bank v ≤ f v) : S = ∅ := by
  by_contra hS
  have Sne : S.Nonempty := nonempty_iff_ne_empty.mpr hS
  have Cne : (S.image cls).Nonempty := Sne.image cls
  have sS := sum_le_sum rowS
  have sO := sum_le_sum rowO
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, ← mul_sum] at sS sO
  rw [sum_fiber_card] at sS
  -- the shortfalls, class by class
  have hd : ∑ c ∈ S.image cls, (∑ w ∈ fiber S cls c, d w + (fiber S cls c).card) =
      ∑ u ∈ S, d u + S.card := by
    rw [sum_add_distrib, sum_fiber d]
    have := sum_fiber (S := S) (cls := cls) (fun _ => 1)
    simp only [sum_const, smul_eq_mul, mul_one] at this
    rw [this]
  have hcp : ∑ c ∈ S.image cls, (∑ w ∈ fiber S cls c, d w + (fiber S cls c).card) <
      ∑ c ∈ S.image cls, ((fiber S cls c).card * (fiber S cls c).card + b * π) := by
    refine sum_lt_sum_of_nonempty Cne (fun c hc => ?_)
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hc
    exact classpay u hu
  rw [hd, sum_add_distrib, sum_const, smul_eq_mul] at hcp
  -- the banks
  have hb : (S.image cls).card * b ≤ ∑ x ∈ V, mult S cls bank x := by
    rw [sum_mult bankV]
    have := sum_le_sum (s := S.image cls) (f := fun _ => b) (g := fun c => (bank c).card)
      (fun c hc => by
        obtain ⟨u, hu, rfl⟩ := mem_image.mp hc
        exact bcard u hu)
    rwa [sum_const, smul_eq_mul] at this
  have kV := sum_sdiff sv (f := mult S cls bank)
  have fV := sum_sdiff sv (f := f)
  have cV := card_sdiff_add_card_eq_card sv
  have pb := Nat.mul_le_mul_left π hb
  rw [← kV, Nat.mul_add] at pb
  have e1 : π * ((S.image cls).card * b) = (S.image cls).card * (b * π) := by ring
  have e2 : V.card * L = (V \ S).card * L + S.card * L := by rw [← cV]; ring
  omega

/-- **Bank count, per-saver shortfalls.** -/
theorem bank_count_gen {i j b π : ℕ} {S : Finset ℕ} {cls : ℕ → ℕ} {bank : ℕ → Finset ℕ}
    {d : ℕ → ℕ} (free : QFree D V q) (hij : i + j ≤ q) (sv : S ⊆ V)
    (bankV : ∀ u ∈ S, bank (cls u) ⊆ V) (bcard : ∀ u ∈ S, b ≤ (bank (cls u)).card)
    (short : ∀ u ∈ S, V.card + 1 ≤ (ball D V u i).card + (ball D V u j).card + d u)
    (rest : ∀ v ∈ V, v ∉ S → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card)
    (pays : ∀ x ∈ V, 0 < mult S cls bank x →
      V.card + 1 + π * mult S cls bank x ≤ (ball D V x i).card + (ball D V x j).card)
    (gaps : ∀ u ∈ S, ∀ u' ∈ S, cls u' = cls u → u' ≠ u → u' ∈ gap D V i j u)
    (classpay : ∀ u ∈ S, ∑ w ∈ fiber S cls (cls u), d w + (fiber S cls (cls u)).card
      < (fiber S cls (cls u)).card * (fiber S cls (cls u)).card + b * π) :
    S = ∅ := by
  set f : ℕ → ℕ := fun v => (ball D V v i).card + (ball D V v j).card + (gap D V i j v).card
    with hf
  have total : ∑ v ∈ V, f v ≤ V.card * (V.card + 1) := by
    simp only [hf, sum_add_distrib]
    exact (ledger free hij).le
  refine core sv total bankV bcard classpay (fun u hu => ?_) (fun v hv => ?_)
  · have uV := sv hu
    have sub : (fiber S cls (cls u)).erase u ⊆ gap D V i j u := by
      intro w hw
      obtain ⟨wne, wF⟩ := mem_erase.mp hw
      obtain ⟨wS, wc⟩ := mem_filter.mp wF
      exact gaps u hu w wS wc wne
    have g := card_le_card sub
    have uF : u ∈ fiber S cls (cls u) := mem_filter.mpr ⟨hu, rfl⟩
    rw [card_erase_of_mem uF] at g
    have pos : 0 < (fiber S cls (cls u)).card := card_pos.mpr ⟨u, uF⟩
    simp only [hf]
    rcases Nat.eq_zero_or_pos (mult S cls bank u) with h0 | hp
    · rw [h0, mul_zero]
      have := short u hu
      omega
    · have := pays u uV hp
      omega
  · obtain ⟨vV, vS⟩ := mem_sdiff.mp hv
    simp only [hf]
    rcases Nat.eq_zero_or_pos (mult S cls bank v) with h0 | hp
    · rw [h0, mul_zero]
      have := rest v vV vS
      omega
    · have := pays v vV hp
      omega

/-- **Bank count, uniform shortfall `δ`.** -/
theorem bank_count {i j b π δ : ℕ} {S : Finset ℕ} {cls : ℕ → ℕ} {bank : ℕ → Finset ℕ}
    (free : QFree D V q) (hij : i + j ≤ q) (sv : S ⊆ V)
    (bankV : ∀ u ∈ S, bank (cls u) ⊆ V) (bcard : ∀ u ∈ S, b ≤ (bank (cls u)).card)
    (short : ∀ u ∈ S, V.card + 1 ≤ (ball D V u i).card + (ball D V u j).card + δ)
    (rest : ∀ v ∈ V, v ∉ S → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card)
    (pays : ∀ x ∈ V, 0 < mult S cls bank x →
      V.card + 1 + π * mult S cls bank x ≤ (ball D V x i).card + (ball D V x j).card)
    (gaps : ∀ u ∈ S, ∀ u' ∈ S, cls u' = cls u → u' ≠ u → u' ∈ gap D V i j u)
    (pay : ∀ m, m * (δ + 1) < m * m + b * π) :
    S = ∅ := by
  refine bank_count_gen (d := fun _ => δ) free hij sv bankV bcard short rest pays gaps
    (fun u _ => ?_)
  have p := pay (fiber S cls (cls u)).card
  rw [sum_const, smul_eq_mul]
  have e : (fiber S cls (cls u)).card * (δ + 1) =
      (fiber S cls (cls u)).card * δ + (fiber S cls (cls u)).card := by ring
  omega

/-- **Disjoint banks.** Banks of distinct classes are disjoint and every bank row is `π` above
the level. -/
theorem bank_count_disjoint {i j b π δ : ℕ} {S : Finset ℕ} {cls : ℕ → ℕ}
    {bank : ℕ → Finset ℕ}
    (free : QFree D V q) (hij : i + j ≤ q) (sv : S ⊆ V)
    (bankV : ∀ u ∈ S, bank (cls u) ⊆ V) (bcard : ∀ u ∈ S, b ≤ (bank (cls u)).card)
    (short : ∀ u ∈ S, V.card + 1 ≤ (ball D V u i).card + (ball D V u j).card + δ)
    (rest : ∀ v ∈ V, v ∉ S → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card)
    (bankpay : ∀ u ∈ S, ∀ x ∈ bank (cls u),
      V.card + 1 + π ≤ (ball D V x i).card + (ball D V x j).card)
    (gaps : ∀ u ∈ S, ∀ u' ∈ S, cls u' = cls u → u' ≠ u → u' ∈ gap D V i j u)
    (disj : ∀ u ∈ S, ∀ u' ∈ S, cls u ≠ cls u' → Disjoint (bank (cls u)) (bank (cls u')))
    (pay : ∀ m, m * (δ + 1) < m * m + b * π) :
    S = ∅ := by
  refine bank_count free hij sv bankV bcard short rest (fun x _ hp => ?_) gaps pay
  have one : mult S cls bank x ≤ 1 := by
    refine card_le_one.mpr (fun c hc c' hc' => ?_)
    obtain ⟨cC, xc⟩ := mem_filter.mp hc
    obtain ⟨cC', xc'⟩ := mem_filter.mp hc'
    obtain ⟨u, hu, rfl⟩ := mem_image.mp cC
    obtain ⟨u', hu', rfl⟩ := mem_image.mp cC'
    by_contra ne
    exact disjoint_left.mp (disj u hu u' hu' ne) xc xc'
  obtain ⟨c, hc⟩ := card_pos.mp hp
  obtain ⟨cC, xc⟩ := mem_filter.mp hc
  obtain ⟨u, hu, rfl⟩ := mem_image.mp cC
  have := bankpay u hu x xc
  have e : mult S cls bank x = 1 := by omega
  rw [e, mul_one]
  exact this

/-- **The instance.** `CollarLedger.no_thin`, same hypotheses and conclusion, from
`bank_count_disjoint`: savers are the thin roots, the class of a thin root is the largest thin
root with the same heads, and the bank of a class is its heads. -/
theorem no_thin_of_bank_count {i j a b A B a' b' π δ : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 1) (hij : i + j ≤ q)
    (fa : ∀ v ∈ V, a ≤ (ball D V v i).card) (fb : ∀ v ∈ V, b ≤ (ball D V v j).card)
    (fa' : ∀ v ∈ V, a' ≤ (ball D V v (i+1)).card) (fb' : ∀ v ∈ V, b' ≤ (ball D V v (j+1)).card)
    (fat : ∀ v ∈ V, q + 1 ≤ (layer D V 2 v).card →
      A + B ≤ (ball D V v i).card + (ball D V v j).card)
    (fatpay : V.card + 1 ≤ A + B)
    (heads : V.card + 1 + π + 2*(q+1) ≤ a' + b' + i + j)
    (thinpay : V.card + 1 ≤ a + b + δ)
    (pay : ∀ m, m * (δ + 1) < m * m + (q+1) * π) :
    ∀ v ∈ V, q + 1 ≤ (layer D V 2 v).card := by
  set S := V.filter (fun v => (layer D V 2 v).card ≤ q) with hS
  set cls : ℕ → ℕ := fun u => (S.filter (fun w => outN D V w = outN D V u)).sup id with hcls
  have quota : ∀ w ∈ V, q + 1 ≤ (outN D V w).card := fun w hw => (reg w hw).ge
  have rep : ∀ u ∈ S, cls u ∈ S ∧ outN D V (cls u) = outN D V u := by
    intro u hu
    obtain ⟨w, hw, he⟩ := exists_mem_eq_sup (S.filter (fun w => outN D V w = outN D V u))
      ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩ id
    have : cls u = w := he
    rw [this]
    exact mem_filter.mp hw
  have cong : ∀ u u', outN D V u = outN D V u' → cls u = cls u' := by
    intro u u' h
    simp only [hcls, h]
  have sv : S ⊆ V := filter_subset _ _
  have thinOf : ∀ u ∈ S, u ∈ V ∧ (layer D V 2 u).card ≤ q := fun u hu => mem_filter.mp hu
  have empty : S = ∅ := by
    refine bank_count_disjoint (b := q+1) (bank := outN D V) (π := π) (δ := δ) free hij sv
      (fun u _ => outN_subset)
      (fun u hu => (reg (cls u) (sv (rep u hu).1)).ge)
      (fun u hu => ?_) (fun v hv vS => ?_) (fun u hu x hx => ?_)
      (fun u hu u' hu' hc ne => ?_) (fun u hu u' hu' ne => ?_) pay
    · have uV := sv hu
      have := fa u uV
      have := fb u uV
      omega
    · have vfat : q + 1 ≤ (layer D V 2 v).card := by
        by_contra h
        exact vS (mem_filter.mpr ⟨hv, by omega⟩)
      have := fat v hv vfat
      omega
    · obtain ⟨wS, -⟩ := rep u hu
      obtain ⟨wV, wthin⟩ := thinOf _ wS
      have bi := collar_ball (r := q+1) free hq wV (reg _ wV)
        (fun y hy => quota y (outN_subset hy)) (by omega) hx (j := i) (by omega)
      have bj := collar_ball (r := q+1) free hq wV (reg _ wV)
        (fun y hy => quota y (outN_subset hy)) (by omega) hx (j := j) (by omega)
      have := fa' _ wV
      have := fb' _ wV
      omega
    · have same : outN D V u = outN D V u' := by
        rw [← (rep u hu).2, ← (rep u' hu').2, hc]
      exact twin_gap free (sv hu) (sv hu') (Ne.symm ne) same (by omega) (by omega)
    · rw [disjoint_left]
      intro x hx hx'
      obtain ⟨wS, we⟩ := rep u hu
      obtain ⟨wS', we'⟩ := rep u' hu'
      obtain ⟨wV, wthin⟩ := thinOf _ wS
      obtain ⟨wV', wthin'⟩ := thinOf _ wS'
      have := loops_equal free hq reg wV wV' wthin wthin' hx hx'
      rw [we, we'] at this
      exact ne (cong u u' this)
  intro v hv
  by_contra h
  have : v ∈ S := mem_filter.mpr ⟨hv, by omega⟩
  rw [empty] at this
  simp at this

#print axioms core
#print axioms bank_count_gen
#print axioms bank_count
#print axioms bank_count_disjoint
#print axioms no_thin_of_bank_count
end LeanCH.BR.BankCount
