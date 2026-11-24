import LeanCH.BR.BRWeightedCommonHeadDefect
import LeanCH.BR.BRFiniteWalk

/-! Internal vertices of a short return avoid both endpoint interfaces.
An actual positive-row gap supplies one further, distinct exterior vertex.
These are single-pair counts; no packing between different pairs is asserted. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def walkInterior (f : ℕ → ℕ) (l : ℕ) : Finset ℕ :=
  (range (l - 1)).image (fun i => f (i + 1))

def walkTrace (f : ℕ → ℕ) (l : ℕ) : Finset ℕ := (range (l + 1)).image f

theorem short_walk_index_injective {q l : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hl : l ≤ q) (f : ℕ → ℕ)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true) :
    Set.InjOn f (range (l + 1)) := by
  intro i hi j hj hij
  have hi' : i < l + 1 := mem_range.mp hi
  have hj' : j < l + 1 := mem_range.mp hj
  by_contra hn
  rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
  · have w := walk_between he hlt.le (by omega : j ≤ l)
    rw [← hij] at w
    exact hf (f i) (j - i) (by omega) (by omega) w
  · have w := walk_between he hgt.le (by omega : i ≤ l)
    rw [hij] at w
    exact hf (f j) (i - j) (by omega) (by omega) w

theorem short_walk_interior_geometry {q l : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hl : l ≤ q) (f : ℕ → ℕ) (h0 : f 0 ∈ V)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true) :
    (walkInterior f l).card = l - 1 ∧ walkInterior f l ⊆ V ∧
    Disjoint (walkInterior f l) (inN D M (f 0) ∪ outN D M (f l)) ∧
    f 0 ∉ walkInterior f l ∧ f l ∉ walkInterior f l := by
  have hinj := short_walk_index_injective hf hl f he
  have hcard : (walkInterior f l).card = l - 1 := by
    rw [walkInterior, card_image_of_injOn, card_range]
    intro i hi j hj hij
    have hi' : i < l - 1 := mem_range.mp hi
    have hj' : j < l - 1 := mem_range.mp hj
    have h := hinj (mem_range.mpr (by omega : i + 1 < l + 1))
      (mem_range.mpr (by omega : j + 1 < l + 1)) hij
    omega
  refine ⟨hcard, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    exact (he i (by have := mem_range.mp hi; omega)).1
  · apply disjoint_left.mpr
    intro a ha hC
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    have hi' : i < l - 1 := mem_range.mp hi
    rcases mem_union.mp hC with hI | hO
    · have wp := walk_between he (by omega : 0 ≤ i + 1) (by omega : i + 1 ≤ l)
      exact hf (f 0) ((i + 1 - 0) + 1) (by omega) (by omega)
        (wp.snoc h0 (mem_inN.mp hI).2)
    · have ws := walk_between he (by omega : i + 1 ≤ l) (le_refl l)
      exact hf (f l) ((l - (i + 1)) + 1) (by omega) (by omega)
        (.step (he i (by omega)).1 (mem_outN.mp hO).2 ws)
  · intro h
    obtain ⟨i, hi, hif⟩ := mem_image.mp h
    have hi' : i < l - 1 := mem_range.mp hi
    have h := hinj (mem_range.mpr (by omega : i + 1 < l + 1))
      (mem_range.mpr (by omega : 0 < l + 1)) hif
    omega
  · intro h
    obtain ⟨i, hi, hif⟩ := mem_image.mp h
    have hi' : i < l - 1 := mem_range.mp hi
    have h := hinj (mem_range.mpr (by omega : i + 1 < l + 1))
      (mem_range.mpr (by omega : l < l + 1)) hif
    omega

/-- Quantitative exposure outside arbitrary M, without cycle or saturation data. -/
theorem short_walk_exterior_exposure {q l : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hl : l ≤ q) (f : ℕ → ℕ) (h0 : f 0 ∈ V)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true) :
    (l - 1) + (inN D M (f 0) ∪ outN D M (f l)).card - M.card ≤
      (walkInterior f l \ M).card := by
  obtain ⟨hcard, hPV, hd, hnot0, hnotl⟩ := short_walk_interior_geometry (M := M) hf hl f h0 he
  have hdis : Disjoint (walkInterior f l ∩ M) (inN D M (f 0) ∪ outN D M (f l)) := by
    apply disjoint_left.mpr
    intro a ha hc
    exact disjoint_left.mp hd (mem_inter.mp ha).1 hc
  have hsub : (walkInterior f l ∩ M) ∪ (inN D M (f 0) ∪ outN D M (f l)) ⊆ M := by
    apply union_subset inter_subset_right
    exact union_subset (fun _ h => (mem_inN.mp h).1) outN_subset
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hc
  have hsplit := card_sdiff_add_card_inter (walkInterior f l) M
  omega

/-- The entire trace avoids both endpoint interfaces. M is arbitrary. -/
theorem short_walk_trace_geometry {q l : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hl : l ≤ q) (f : ℕ → ℕ)
    (h0 : f 0 ∈ V \ M) (hlast : f l ∈ V \ M)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true) :
    (walkTrace f l).card = l + 1 ∧ walkTrace f l ⊆ V ∧
      Disjoint (walkTrace f l) (inN D M (f 0) ∪ outN D M (f l)) := by
  have hgeom := short_walk_interior_geometry (M := M) hf hl f (mem_sdiff.mp h0).1 he
  have hCM : inN D M (f 0) ∪ outN D M (f l) ⊆ M :=
    union_subset (fun _ h => (mem_inN.mp h).1) outN_subset
  refine ⟨?_, ?_, ?_⟩
  · exact (card_image_of_injOn (short_walk_index_injective hf hl f he)).trans (card_range _)
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    have hi' := mem_range.mp hi
    by_cases hi0 : i = 0
    · subst i; exact (mem_sdiff.mp h0).1
    · have h := (he (i - 1) (by omega)).1
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using h
  · apply disjoint_left.mpr
    intro a ha hC
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    have hi' := mem_range.mp hi
    by_cases hi0 : i = 0
    · subst i; exact (mem_sdiff.mp h0).2 (hCM hC)
    by_cases hil : i = l
    · subst i; exact (mem_sdiff.mp hlast).2 (hCM hC)
    have hP : f i ∈ walkInterior f l :=
      mem_image.mpr ⟨i - 1, mem_range.mpr (by omega), by rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]⟩
    exact disjoint_left.mp hgeom.2.2.1 hP hC

/-- The whole actual gap avoids the trace; the exact needed path bound is l+1≤q.
No cycle, degree, saturation, positivity, or value hypothesis is used. -/
theorem short_walk_gap_trace_disjoint {q l : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hl : l + 1 ≤ q) (f : ℕ → ℕ)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true)
    {u : ℕ} (hu : u ∈ V) (hbu : D (f l) u = true) (hmiss : ¬ D u (f 0) = true) :
    Disjoint (outGap D V u (f l)) (walkTrace f l) := by
  apply disjoint_left.mpr
  intro g hg htrace
  obtain ⟨i, hi, hif⟩ := mem_image.mp htrace
  have hi' : i < l + 1 := mem_range.mp hi
  by_cases hi0 : i = 0
  · subst i
    exact hmiss (hif ▸ (mem_outGap.mp hg).2.1)
  · have ws := walk_between he (by omega : i ≤ l) (le_refl l)
    rw [hif] at ws
    exact hf (f l) ((l - i) + 2) (by omega) (by omega)
      (.step hu hbu (.step (mem_outGap.mp hg).1 (mem_outGap.mp hg).2.1 ws))

theorem short_walk_whole_gap_room {q l : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hl : l + 1 ≤ q) (hMV : M ⊆ V) (f : ℕ → ℕ)
    (h0 : f 0 ∈ V \ M) (hlast : f l ∈ V \ M)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true)
    {u : ℕ} (hu : u ∈ V) (hbu : D (f l) u = true) (hmiss : ¬ D u (f 0) = true)
    (hgap : outGap D V u (f l) ⊆ V \ M) :
    l + 1 + (inN D M (f 0) ∪ outN D M (f l)).card + (outGap D V u (f l)).card ≤ V.card := by
  obtain ⟨hcard, hWV, hWC⟩ := short_walk_trace_geometry hf (by omega : l ≤ q) f h0 hlast he
  have hGW := short_walk_gap_trace_disjoint hf hl f he hu hbu hmiss
  have hCM : inN D M (f 0) ∪ outN D M (f l) ⊆ M :=
    union_subset (fun _ h => (mem_inN.mp h).1) outN_subset
  have hCG : Disjoint (inN D M (f 0) ∪ outN D M (f l)) (outGap D V u (f l)) := by
    apply disjoint_left.mpr
    intro a ha hg
    exact (mem_sdiff.mp (hgap hg)).2 (hCM ha)
  have hd := Finset.disjoint_union_left.mpr ⟨hGW.symm, hCG⟩
  have hsub : (walkTrace f l ∪ (inN D M (f 0) ∪ outN D M (f l))) ∪
      outGap D V u (f l) ⊆ V :=
    union_subset (union_subset hWV (fun _ h => hMV (hCM h))) (fun _ h => (mem_outGap.mp h).1)
  have hc := card_le_card hsub
  rwa [card_union_of_disjoint hd, card_union_of_disjoint hWC, hcard] at hc

theorem short_walk_whole_gap_mass {q l : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hl : l + 1 ≤ q) (hMV : M ⊆ V) (f : ℕ → ℕ)
    (h0 : f 0 ∈ V \ M) (hlast : f l ∈ V \ M)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true)
    {u : ℕ} (hu : u ∈ V) (hbu : D (f l) u = true) (hmiss : ¬ D u (f 0) = true)
    (hgap : outGap D V u (f l) ⊆ V \ M) (a : ℕ → ℚ) (ha : ∀ v ∈ V, 0 ≤ a v) :
    mass (walkTrace f l) a + mass (inN D M (f 0) ∪ outN D M (f l)) a +
      mass (outGap D V u (f l)) a ≤ mass V a := by
  obtain ⟨hcard, hWV, hWC⟩ := short_walk_trace_geometry hf (by omega : l ≤ q) f h0 hlast he
  have hGW := short_walk_gap_trace_disjoint hf hl f he hu hbu hmiss
  have hCM : inN D M (f 0) ∪ outN D M (f l) ⊆ M :=
    union_subset (fun _ h => (mem_inN.mp h).1) outN_subset
  have hCG : Disjoint (inN D M (f 0) ∪ outN D M (f l)) (outGap D V u (f l)) := by
    apply disjoint_left.mpr
    intro v hv hg
    exact (mem_sdiff.mp (hgap hg)).2 (hCM hv)
  have hd := Finset.disjoint_union_left.mpr ⟨hGW.symm, hCG⟩
  have hsub : (walkTrace f l ∪ (inN D M (f 0) ∪ outN D M (f l))) ∪
      outGap D V u (f l) ⊆ V :=
    union_subset (union_subset hWV (fun _ h => hMV (hCM h))) (fun _ h => (mem_outGap.mp h).1)
  have h := mass_mono hsub ha
  simpa only [mass, sum_union hd, sum_union hWC] using h

/-- Equal rows replace the full gap mass by its exact charge, including the
entire reverse-gap debit after removing the actual head u. -/
theorem short_walk_whole_gap_charge {q l : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hl : l + 1 ≤ q) (hMV : M ⊆ V) (f : ℕ → ℕ)
    (h0 : f 0 ∈ V \ M) (hlast : f l ∈ V \ M)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true)
    {u : ℕ} (hu : u ∈ V) (hbu : D (f l) u = true) (hmiss : ¬ D u (f 0) = true)
    (hgap : outGap D V u (f l) ⊆ V \ M) (a : ℕ → ℚ) (ha : ∀ v ∈ V, 0 ≤ a v)
    (heq : row q D V a u = row q D V a (f l)) :
    (q : ℚ) * (mass (walkTrace f l) a + mass (inN D M (f 0) ∪ outN D M (f l)) a) +
      (q - 1 : ℚ) * a u + a (f l) + q * mass ((outGap D V (f l) u).erase u) a ≤
        q * mass V a := by
  have h := mul_le_mul_of_nonneg_left
    (short_walk_whole_gap_mass hf hl hMV f h0 hlast he hu hbu hmiss hgap a ha)
    (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
  have hcharge := equal_rows_arc_gap_exact a hu hbu (loopfree hf (by omega) hu) heq
  nlinarith

theorem last_layer_walk_exterior_exposure {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q) (hM : M.card = q + 1)
    (f : ℕ → ℕ) (h0 : f 0 ∈ V)
    (he : ∀ i, i < q - 1 → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true)
    (hdis : Disjoint (inN D M (f 0)) (outN D M (f (q - 1)))) :
    (inN D M (f 0)).card + (outN D M (f (q - 1))).card - 3 ≤
      (walkInterior f (q - 1) \ M).card := by
  have h := short_walk_exterior_exposure (M := M) hf (by omega : q - 1 ≤ q) f h0 he
  rw [card_union_of_disjoint hdis, hM] at h
  omega

/-- One further exterior witness is counted once for this path only. -/
theorem short_walk_contact_room {q l : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hl0 : 0 < l) (hl : l ≤ q) (hMV : M ⊆ V)
    (f : ℕ → ℕ) (h0 : f 0 ∈ V \ M) (hlast : f l ∈ V \ M)
    (he : ∀ i, i < l → f (i + 1) ∈ V ∧ D (f i) (f (i + 1)) = true)
    {g : ℕ} (hg : g ∈ V \ M) (hg0 : g ≠ f 0) (hgl : g ≠ f l)
    (hgP : g ∉ walkInterior f l) :
    (l - 1) + (inN D M (f 0) ∪ outN D M (f l)).card + 3 ≤ V.card := by
  obtain ⟨hcard, hPV, hd, hn0, hnl⟩ :=
    short_walk_interior_geometry (M := M) hf hl f (mem_sdiff.mp h0).1 he
  let A := walkInterior f l ∪ (inN D M (f 0) ∪ outN D M (f l))
  have hCM : inN D M (f 0) ∪ outN D M (f l) ⊆ M :=
    union_subset (fun _ h => (mem_inN.mp h).1) outN_subset
  have hAV : A ⊆ V := union_subset hPV (fun a ha => hMV (hCM ha))
  have hAcard : A.card = (l - 1) + (inN D M (f 0) ∪ outN D M (f l)).card := by
    dsimp only [A]
    rw [card_union_of_disjoint hd, hcard]
  have h0A : f 0 ∉ A := by
    intro h
    rcases mem_union.mp h with h | h
    · exact hn0 h
    · exact (mem_sdiff.mp h0).2 (hCM h)
  have hlA : f l ∉ A := by
    intro h
    rcases mem_union.mp h with h | h
    · exact hnl h
    · exact (mem_sdiff.mp hlast).2 (hCM h)
  have hgA : g ∉ A := by
    intro h
    rcases mem_union.mp h with h | h
    · exact hgP h
    · exact (mem_sdiff.mp hg).2 (hCM h)
  have hl0ne : f l ≠ f 0 := by
    intro h
    have hh := short_walk_index_injective hf hl f he
      (mem_range.mpr (by omega : l < l + 1)) (mem_range.mpr (by omega : 0 < l + 1)) h
    omega
  have hlA' : f l ∉ insert (f 0) A := by simp [hl0ne, hlA]
  have hgA' : g ∉ insert (f l) (insert (f 0) A) := by simp [hgl, hg0, hgA]
  have hsub : insert g (insert (f l) (insert (f 0) A)) ⊆ V :=
    insert_subset (mem_sdiff.mp hg).1
      (insert_subset (mem_sdiff.mp hlast).1 (insert_subset (mem_sdiff.mp h0).1 hAV))
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hgA', card_insert_of_notMem hlA', card_insert_of_notMem h0A, hAcard] at hc
  omega

/-- Positive equalized rows produce a gap outside M and outside the whole return.
Only equality of the selected head's row and the sender's row is used. -/
theorem missed_pair_order_lower {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hout : OutEq 1 D M) (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v)
    {z b u : ℕ} (hz : z ∈ V \ M) (hb : b ∈ V \ M)
    (hu : u ∈ outN D M b) (hv : ∃ v ∈ outN D M b, D u v = true)
    (hmiss : ¬ D u z = true) (heq : row q D V w u = row q D V w b)
    (hlast : b ∈ ball D V z (q - 1) \ ball D V z (q - 2)) :
    q + 1 + (inN D M z ∪ outN D M b).card ≤ V.card := by
  have huV : u ∈ V := hMV (outN_subset hu)
  have hbV := (mem_sdiff.mp hb).1
  have hbu := (mem_outN.mp hu).2
  obtain ⟨g, hg⟩ := equal_rows_arc_gap_nonempty (by omega : 1 ≤ q) w
    (fun v hv => (hw v hv).le) huV (hw b hbV) hbu (loopfree hf (by omega) huV) heq
  have hgExt := consecutive_sender_gap_exterior hout hu hv hg
  have hreturn := outGap_no_short_return (t := q - 2) (by omega) hf huV hbV hbu hg
  have hgb : g ≠ b := by
    intro h
    subst g
    exact hreturn (self_mem_ball hbV)
  have hgz : g ≠ z := by
    intro h
    subst g
    exact hmiss (mem_outGap.mp hg).2.1
  obtain ⟨f, hf0, hfl, hedges⟩ := (last_layer_exact_walk (by omega : 2 ≤ q) hlast).toFun
  have hgP : g ∉ walkInterior f (q - 1) := by
    intro h
    obtain ⟨i, hi, hif⟩ := mem_image.mp h
    have hi' : i < (q - 1) - 1 := mem_range.mp hi
    have ws := walk_between hedges (by omega : i + 1 ≤ q - 1) (le_refl (q - 1))
    rw [hif, hfl] at ws
    exact hreturn (mem_ball.mpr ⟨hbV, (q - 1) - (i + 1), by omega, ws⟩)
  have hc := short_walk_contact_room hf (by omega : 0 < q - 1) (by omega : q - 1 ≤ q)
    hMV f (by rwa [hf0]) (by rwa [hfl]) hedges hgExt
    (by rwa [hf0]) (by rwa [hfl]) hgP
  rw [hf0, hfl] at hc
  omega

theorem uncovered_rich_missed_order_lower {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hout : OutEq 1 D M) (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v)
    {z b u : ℕ} (hz : z ∈ cycleRichReceivers D V M) (hb : b ∈ V \ M)
    (hu : u ∈ outN D M b) (hv : ∃ v ∈ outN D M b, D u v = true)
    (hmiss : ¬ D u z = true) (heq : row q D V w u = row q D V w b)
    (hlast : b ∈ ball D V z (q - 1) \ ball D V z (q - 2))
    (hcommon : outN D M b ∩ inN D M z = ∅) : q + 5 ≤ V.card := by
  obtain ⟨hzExt, hI⟩ := mem_filter.mp hz
  have h := missed_pair_order_lower hq hf hMV hout w hw hzExt hb hu hv hmiss heq hlast
  have hdis : Disjoint (inN D M z) (outN D M b) :=
    (disjoint_iff_inter_eq_empty.mpr hcommon).symm
  rw [card_union_of_disjoint hdis] at h
  obtain ⟨v, hvb, huv⟩ := hv
  have huvne : u ≠ v := by
    intro he
    subst v
    exact loopfree hf (by omega) (hMV (outN_subset hu)) huv
  have hO : 1 < (outN D M b).card := one_lt_card.mpr ⟨u, hu, v, hvb, huvne⟩
  omega

/-- A bounded-order coverage supplier. No column equation, normalization,
common value, saturation, or |M|=q+1 assumption is needed. -/
theorem rich_last_layer_common_head_of_small_order {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hout : OutEq 1 D M) (horder : V.card ≤ q + 4)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v) (c : ℚ)
    (hr : ∀ v ∈ V, row q D V w v = c)
    {z b : ℕ} (hz : z ∈ cycleRichReceivers D V M)
    (hb : b ∈ consecutiveCycleSenders D V M)
    (hlast : b ∈ ball D V z (q - 1) \ ball D V z (q - 2)) :
    (outN D M b ∩ inN D M z).Nonempty := by
  by_contra hn
  have he := not_nonempty_iff_eq_empty.mp hn
  obtain ⟨hbExt, u, hu, v, hv, huv⟩ := mem_filter.mp hb
  have hmiss : ¬ D u z = true := by
    intro huz
    have huI : u ∈ inN D M z := mem_inN.mpr ⟨outN_subset hu, huz⟩
    have hh := mem_inter.mpr ⟨hu, huI⟩
    rw [he] at hh
    exact notMem_empty u hh
  have hbound := uncovered_rich_missed_order_lower hq hf hMV hout w hw hz hbExt hu
    ⟨v, hv, huv⟩ hmiss
    ((hr u (hMV (outN_subset hu))).trans (hr b (mem_sdiff.mp hbExt).1).symm) hlast he
  omega

end LeanCH.BR.WeightedSD
