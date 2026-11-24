import checkpoints.shen_extension.ShortCycleBalance

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking

/-- Distinct labelled supports crossing a row, and their distinct successors. -/
def through (F : Finset (Finset ℕ)) (v : ℕ) := F.filter (fun C => v ∈ C)

noncomputable def turns (D : CH.Digraph) (F : Finset (Finset ℕ)) (v : ℕ) :=
  (through F v).image (fun C => internalHead D C v)

def omissions (D : CH.Digraph) (V C : Finset ℕ) (r : ℕ) :=
  (exterior D V C).card - (r - 1)

noncomputable def share (D : CH.Digraph) (V : Finset ℕ) (F : Finset (Finset ℕ))
    (r : ℕ) (stock : ℕ → ℚ) (C : Finset ℕ) (v : ℕ) : ℚ :=
  (stock v / (turns D F v).card) * ((1 : ℚ) / 2 ^ omissions D V C r)

theorem successor_mem {D V v C} (rooted : Rooted D V v C) :
    internalHead D C v ∈ outN D C v := by
  have positive : (outN D C v).Nonempty := card_pos.mp (by rw [rooted.one v rooted.root]; decide)
  simpa only [internalHead, dite_eq_left positive] using (outN D C v).min'_mem positive

theorem row_exterior {D V v C} (rooted : Rooted D V v C) :
    (outN D V v).erase (internalHead D C v) = exterior D V C ∩ outN D V v := by
  have head := successor_mem rooted
  ext z
  constructor
  · intro hz
    obtain ⟨ne, edge⟩ := mem_erase.mp hz
    refine mem_inter.mpr ⟨mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨v, rooted.root, edge⟩, ?_⟩, edge⟩
    intro hc
    exact ne (card_le_one.mp (rooted.one v rooted.root).le z
      (mem_outN.mpr ⟨hc, (mem_outN.mp edge).2⟩) _ head)
  · intro hz
    obtain ⟨outside, edge⟩ := mem_inter.mp hz
    have ne : z ≠ internalHead D C v := fun eq => (mem_sdiff.mp outside).2 (eq.symm ▸ outN_subset head)
    exact mem_erase.mpr ⟨ne, edge⟩

theorem row_omissions {D V v C r} (rooted : Rooted D V v C) (degree : (outN D V v).card = r) :
    (exterior D V C \ outN D V v).card = omissions D V C r := by
  have head := outN_mono rooted.sub v (successor_mem rooted)
  have split := card_sdiff_add_card_eq_card
    (inter_subset_left : exterior D V C ∩ outN D V v ⊆ exterior D V C)
  rw [inter_comm, sdiff_inter_self_right, inter_comm, ← row_exterior rooted,
    card_erase_of_mem head, degree] at split
  unfold omissions
  omega

theorem complete_row {D V v C r} (rooted : Rooted D V v C)
    (degree : (outN D V v).card = r) (size : (exterior D V C).card = r-1) :
    (outN D V v).erase (internalHead D C v) = exterior D V C := by
  have rz := row_exterior rooted
  have head := outN_mono rooted.sub v (successor_mem rooted)
  exact eq_of_subset_of_card_le (rz.symm ▸ inter_subset_left)
    (by rw [card_erase_of_mem head, degree, size])

/-- Each row funds all its selected physical supports out of one stock. -/
theorem row_budget {D V F r stock v}
    (rooted : ∀ C ∈ through F v, Rooted D V v C)
    (degree : (outN D V v).card = r) (nonneg : 0 ≤ stock v) :
    (∑ C ∈ through F v, share D V F r stock C v) ≤ stock v := by
  classical
  rcases (through F v).eq_empty_or_nonempty with empty | ⟨C, hc⟩
  · simpa [empty] using nonneg
  have pos : (0 : ℚ) < (turns D F v).card := by
    have native : 0 < (turns D F v).card :=
      card_pos.mpr ⟨internalHead D C v, mem_image_of_mem (fun K => internalHead D K v) hc⟩
    exact_mod_cast native
  have pack := root_packing rooted
  change (∑ C ∈ through F v, (1 : ℚ) / 2 ^ omissions D V C ((outN D V v).card))
      ≤ (turns D F v).card at pack
  rw [degree] at pack
  calc
    _ = (stock v / (turns D F v).card) * (∑ C ∈ through F v, (1 : ℚ) / 2 ^ omissions D V C r) := by
      rw [mul_sum]
      rfl
    _ ≤ (stock v / (turns D F v).card) * (turns D F v).card :=
      mul_le_mul_of_nonneg_left pack (div_nonneg nonneg pos.le)
    _ = stock v := div_mul_cancel₀ _ pos.ne'

/-- Double counting uses each geometric cycle and each row once, including
when several origins use the same support for different purposes. -/
theorem total_budget {D V F r stock}
    (rooted : ∀ C ∈ F, ∀ v ∈ C, Rooted D V v C)
    (sub : ∀ C ∈ F, C ⊆ V)
    (degree : ∀ v ∈ V, (outN D V v).card = r) (nonneg : ∀ v ∈ V, 0 ≤ stock v) :
    (∑ C ∈ F, ∑ v ∈ C, share D V F r stock C v) ≤ ∑ v ∈ V, stock v := by
  classical
  calc
    _ = ∑ C ∈ F, ∑ v ∈ V, if v ∈ C then share D V F r stock C v else 0 := by
      apply sum_congr rfl
      intro C hc
      have labels : V.filter (fun v => v ∈ C) = C := by
        ext v
        exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨sub C hc h, h⟩⟩
      rw [← sum_filter, labels]
    _ = ∑ v ∈ V, ∑ C ∈ F, if v ∈ C then share D V F r stock C v else 0 := sum_comm
    _ ≤ ∑ v ∈ V, stock v := by
      apply sum_le_sum
      intro v hv
      rw [← sum_filter]
      exact row_budget (fun C hc => rooted C (mem_filter.mp hc).1 v (mem_filter.mp hc).2)
        (degree v hv) (nonneg v hv)

/-- The number of successors in the same mixed family is controlled by the
largest allowed omission on those supports. -/
theorem turns_bound {D V q F r c v} (free : QFree D V q) (cut : c + 2 ≤ q)
    (rooted : ∀ C ∈ F, ∀ x ∈ C, Rooted D V x C)
    (degree : ∀ x ∈ V, (outN D V x).card = r)
    (width : ∀ C ∈ F, omissions D V C r ≤ c) :
    (turns D F v).card ≤ c + 1 := by
  apply CycleRowMultiplicity.successors free cut
  · exact fun C hc => rooted C (mem_filter.mp hc).1 v (mem_filter.mp hc).2
  · intro C hc
    obtain ⟨hf, hv⟩ := mem_filter.mp hc
    have cr := rooted C hf v hv
    have hm := outN_subset (successor_mem cr)
    have hr := rooted C hf _ hm
    rw [row_omissions hr (degree _ (hr.sub hm))]
    exact width C hf

/-- A complete bank is exclusive among supports with small omission when
each exterior label has too few heads in that same exterior bank. -/
theorem complete_exclusive {D V q r c d C K} (free : QFree D V q) (hq : 2 ≤ q)
    (rootC : ∀ v ∈ C, Rooted D V v C) (rootK : ∀ v ∈ K, Rooted D V v K)
    (regular : ∀ v ∈ V, (outN D V v).card = r)
    (complete : (exterior D V C).card = r-1)
    (sparse : ∀ w ∈ exterior D V C, (outN D (exterior D V C) w).card ≤ d)
    (width : omissions D V K r ≤ c) (limit : c+d < r-1)
    {v : ℕ} (vc : v ∈ C) (vk : v ∈ K) : C = K := by
  classical
  by_contra ne
  let E := exterior D V C
  let s := internalHead D C v
  let w := internalHead D K v
  have cr := rootC v vc
  have kr := rootK v vk
  have hs : s ∈ outN D C v := successor_mem cr
  have hw : w ∈ outN D K v := successor_mem kr
  have sv : s ∈ V := cr.sub (outN_subset hs)
  have wv : w ∈ V := kr.sub (outN_subset hw)
  have row := complete_row cr (regular v (cr.sub vc)) complete
  change (outN D V v).erase s = E at row
  by_cases diff : w = s
  · let F : Finset (Finset ℕ) := {C, K}
    have roots A (ha : A ∈ F) : Rooted D V v A := by
      rcases mem_insert.mp ha with rfl | other
      · exact cr
      · obtain rfl := mem_singleton.mp other
        exact kr
    have same A (ha : A ∈ F) : s ∈ outN D A v := by
      rcases mem_insert.mp ha with rfl | other
      · exact hs
      · obtain rfl := mem_singleton.mp other
        exact diff ▸ hw
    have budget := turn_packing roots same
    have empty : (exterior D V C \ exterior D V C).card = 0 := by simp
    simp only [F, sum_insert (notMem_singleton.mpr ne), sum_singleton, row, E, empty,
      pow_zero, div_one] at budget
    have pos : 0 < (1 : ℚ) / 2 ^ (exterior D V K \ exterior D V C).card := by positivity
    linarith
  · have we : w ∈ E := row ▸ mem_erase.mpr ⟨diff, outN_mono kr.sub v hw⟩
    have sc := outN_subset hs
    have se : s ∉ E := fun h => (mem_sdiff.mp h).2 sc
    have sr := rootC s sc
    have sw : D s w = true := by
      have h : w ∈ (outN D V s).erase (internalHead D C s) :=
        (complete_row sr (regular s sv) complete).symm ▸ (show w ∈ exterior D V C from we)
      exact (mem_outN.mp (mem_of_mem_erase h)).2
    have ws : D w s ≠ true := fun edge =>
      free s 2 (by decide) hq (.step wv sw (.step sv edge (.refl s)))
    let A := insert s (E.erase w)
    have ac : A.card = r-1 := by
      dsimp [A]
      have hpos := card_pos.mpr ⟨w, we⟩
      rw [card_insert_of_notMem (fun h => se (mem_of_mem_erase h)), card_erase_of_mem we]
      change E.card = r-1 at complete
      omega
    have ad : A ⊆ exterior D V K := by
      intro a ha
      have hit : a ∈ (outN D V v).erase w := by
        rcases mem_insert.mp ha with rfl | he
        · exact mem_erase.mpr ⟨Ne.symm diff, outN_mono cr.sub v hs⟩
        · obtain ⟨off, old⟩ := mem_erase.mp he
          exact mem_erase.mpr ⟨off, mem_of_mem_erase (row.symm ▸ old)⟩
      exact (mem_inter.mp ((row_exterior kr) ▸ hit)).1
    have keep : A ∩ outN D V w ⊆ outN D E w := by
      intro a ha
      obtain ⟨aa, aw⟩ := mem_inter.mp ha
      have arc := (mem_outN.mp aw).2
      rcases mem_insert.mp aa with rfl | he
      · exact (ws arc).elim
      · exact mem_outN.mpr ⟨mem_of_mem_erase he, arc⟩
    have l := (card_le_card keep).trans (sparse w we)
    have cash := card_sdiff_add_card_eq_card (inter_subset_left : A ∩ outN D V w ⊆ A)
    rw [inter_comm, sdiff_inter_self_right, inter_comm] at cash
    have charge := card_le_card (sdiff_subset_sdiff ad (Subset.rfl : outN D V w ⊆ outN D V w))
    rw [row_omissions (rootK w (outN_subset hw)) (regular w wv)] at charge
    omega

/-- Work in doubled units, so missing pairs can be kept as ordered labels. -/
def surplus (base score : ℕ) := if base < score then 2 * (score - base) - 1 else 0

def debit (base score : ℕ) := if score < base then 3 else if score = base then 1 else 0

theorem reach_ledger {D V q k b} (free : QFree D V q) (time : k+k ≤ q)
    (low : ∀ v ∈ V, b ≤ (ball D V v k).card + 1) :
    let score := fun v => (ball D V v k).card
    (DotClonePairCompletion.orderedIncomparable D V k).card + (∑ v ∈ V, surplus b (score v)) +
        V.card * (2*b+1) = (∑ v ∈ V, debit b (score v)) + V.card * (V.card+1) := by
  dsimp only
  have point (v) (hv : v ∈ V) :
      surplus b (ball D V v k).card + (2*b+1) =
        debit b (ball D V v k).card + 2*(ball D V v k).card := by
    have floor := low v hv
    unfold debit surplus
    split_ifs <;> omega
  have total := sum_congr (s₁ := V) rfl point
  conv at total =>
    lhs
    rw [sum_add_distrib, sum_const_nat (fun _ _ => rfl)]
  conv at total =>
    rhs
    rw [sum_add_distrib, ← mul_sum]
  have reach := DotClonePairCompletion.incomparable_reach_identity free time
  omega

theorem class_pairs {D V q k r} {U : Finset ℕ} (free : QFree D V q)
    (hq : 2 ≤ q) (time : k ≤ q) (reg : OutEq r D V) (sub : U ⊆ V)
    (same : ∀ a ∈ U, ∀ b ∈ U, N2 D V a = N2 D V b) :
    U.offDiag ⊆ DotClonePairCompletion.orderedIncomparable D V k := by
  intro e he
  obtain ⟨a, b, ne⟩ := mem_offDiag.mp he
  have ab := SecondShellClasses.missed free hq (sub a) (sub b) ne (same _ a _ b).subset
    (by rw [reg _ (sub a), reg _ (sub b)])
  have ba := SecondShellClasses.missed free hq (sub b) (sub a) ne.symm (same _ b _ a).subset
    (by rw [reg _ (sub a), reg _ (sub b)])
  exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨sub a, sub b, ne⟩,
    fun h => ab (ball_mono_radius time h), fun h => ba (ball_mono_radius time h)⟩

/-- Each class can spend its own ordered holes before requesting stock.
The residual is at most four doubled units, and at most one for a class
whose members individually owe at most one doubled unit. -/
theorem class_residual {U : Finset ℕ} {loss : ℕ → ℕ} {m : ℕ}
    (per : ∀ v ∈ U, loss v ≤ m) :
    (∑ v ∈ U, loss v) - U.offDiag.card ≤
      if m ≤ 1 then 1 else if m ≤ 3 then 4 else m*m := by
  have bill : (∑ v ∈ U, loss v) ≤ U.card*m := by
    simpa only [sum_const_nat (fun _ _ => rfl)] using sum_le_sum per
  have count : U.card*U.card-U.card = U.card*(U.card-1) := by
    simpa only [Nat.mul_one] using (Nat.mul_sub_left_distrib U.card U.card 1).symm
  rw [offDiag_card, count]
  split_ifs with small medium
  · by_cases tiny : U.card ≤ 1
    · exact (Nat.sub_le ..).trans (bill.trans (Nat.mul_le_mul tiny small))
    · have self : U.card*m ≤ U.card*(U.card-1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  · by_cases big : 4 ≤ U.card
    · have self : U.card*m ≤ U.card*(U.card-1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · have c : U.card = 0 ∨ U.card = 1 ∨ U.card = 2 ∨ U.card = 3 := by omega
      rcases c with e | e | e | e <;> rw [e] at bill ⊢ <;> omega
  · by_cases big : m < U.card
    · have self : U.card*m ≤ U.card*(U.card-1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · exact (Nat.sub_le ..).trans (bill.trans (Nat.mul_le_mul_right _ (by omega)))

/-- A single strict physical stock estimate closes the symmetric reach ledger
once all missing-pair charges use disjoint sets from that very graph. -/
theorem ledger_contradiction {D V q k b F r} (free : QFree D V q) (time : k+k ≤ q)
    (low : ∀ v ∈ V, b ≤ (ball D V v k).card + 1) (order : V.card ≤ 2*b)
    (rooted : ∀ C ∈ F, ∀ v ∈ C, Rooted D V v C) (sub : ∀ C ∈ F, C ⊆ V)
    (degree : ∀ v ∈ V, (outN D V v).card = r)
    {pairs : Finset (ℕ × ℕ)} (real : pairs ⊆ DotClonePairCompletion.orderedIncomparable D V k)
    (funded :
      let score := fun v => (ball D V v k).card
      (∑ v ∈ V, (debit b (score v) : ℚ)) <
        pairs.card + (∑ C ∈ F, ∑ v ∈ C, share D V F r (fun v => surplus b (score v)) C v)) :
    False := by
  dsimp only at funded
  have x := total_budget (stock := fun v => (surplus b (ball D V v k).card : ℚ)) rooted sub degree
    (fun _ _ => by positivity)
  have missed : (pairs.card : ℚ) ≤ (DotClonePairCompletion.orderedIncomparable D V k).card := by
    exact_mod_cast card_le_card real
  have capacity := reach_ledger free time low
  dsimp only at capacity
  have count := Nat.mul_le_mul_left V.card (show V.card+1 ≤ 2*b+1 by omega)
  have used : (DotClonePairCompletion.orderedIncomparable D V k).card +
      (∑ v ∈ V, surplus b (ball D V v k).card) ≤ ∑ v ∈ V, debit b (ball D V v k).card := by omega
  have paid : ((DotClonePairCompletion.orderedIncomparable D V k).card : ℚ) +
      (∑ v ∈ V, (surplus b (ball D V v k).card : ℚ)) ≤ ∑ v ∈ V, (debit b (ball D V v k).card : ℚ) := by
    exact_mod_cast used
  linarith only [funded, x, missed, paid]

#print axioms row_omissions
#print axioms row_budget
#print axioms total_budget
#print axioms turns_bound
#print axioms complete_exclusive
#print axioms reach_ledger
#print axioms class_pairs
#print axioms class_residual
#print axioms ledger_contradiction

end LeanCH.BR.PhysicalCycleStock
