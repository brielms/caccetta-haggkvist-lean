import LeanCH.BR.BR45Base

/-!
# A tight-parent bank cannot have exactly q+1 labels at critical order

All rows, balls, degrees and induced carriers belong to one unchanged graph.
Native proper-induced-host minimality supplies an actual tight incoming parent
at every label. Reverse-ball growth inside a bank of q+1 labels then bounds
returns to that bank by two. Its exterior keeps degree s-1.

The final contradiction explicitly assumes the same-cutoff degree-(s-1) order
bound. This file does not supply that induction hypothesis or prove full CH.
-/
namespace LeanCH.BR.DotTightParentCarrier
open BRq2 BRq3 BR45
open Classical

/-- Native vertex minimality, not an assumption about an edited graph. -/
def VertexMinimal (D : CH.Digraph) (V : Finset ℕ) (s : ℕ) : Prop :=
  ∀ W, W ⊆ V → W.Nonempty → W ≠ V →
    ∃ u ∈ W, (outN D W u).card < s

/-- Only the degree-(s-1) instance is assumed; no all-degree CH premise is hidden. -/
def PredDegreeOrder (q s : ℕ) : Prop :=
  ∀ (F : CH.Digraph) (W : Finset ℕ), QFree F W q →
    (∀ u ∈ W, s-1 ≤ (outN F W u).card) → W.Nonempty →
    q*(s-1)+1 ≤ W.card

noncomputable def tightRows (D : CH.Digraph) (V : Finset ℕ) (s : ℕ) : Finset ℕ :=
  V.filter (fun u => (outN D V u).card = s)

theorem mem_tightRows {D : CH.Digraph} {V : Finset ℕ} {s u : ℕ} :
    u ∈ tightRows D V s ↔ u ∈ V ∧ (outN D V u).card = s := Finset.mem_filter

theorem tightRows_subset {D : CH.Digraph} {V : Finset ℕ} {s : ℕ} :
    tightRows D V s ⊆ V := fun _ hu => (mem_tightRows.mp hu).1

private theorem outN_erase_eq {D : CH.Digraph} {V : Finset ℕ} (u v : ℕ) :
    outN D (V.erase v) u = (outN D V u).erase v := by
  ext x
  simp only [mem_outN, Finset.mem_erase]
  tauto

/-- Deleting just v forces a degree-s parent of v, on the original graph. -/
theorem exists_tight_parent {D : CH.Digraph} {V : Finset ℕ} {q s v : ℕ}
    (hq : 1 ≤ q) (hs : 1 ≤ s) (hf : QFree D V q)
    (hm : ∀ u ∈ V, s ≤ (outN D V u).card)
    (hminimal : VertexMinimal D V s) (hv : v ∈ V) :
    ∃ u ∈ tightRows D V s, D u v = true := by
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (outN D V v).card by
    have := hm v hv; omega)
  have hwv : w ≠ v := by
    intro he
    subst w
    exact loopfree hf hq hv (mem_outN.mp hw).2
  have hne : (V.erase v).Nonempty :=
    ⟨w, Finset.mem_erase.mpr ⟨hwv, outN_subset hw⟩⟩
  have hproper : V.erase v ≠ V := by
    intro he
    have hvErase : v ∈ V.erase v := he.symm ▸ hv
    exact (Finset.mem_erase.mp hvErase).1 rfl
  obtain ⟨u, hu, hsmall⟩ := hminimal (V.erase v) (Finset.erase_subset _ _) hne hproper
  have huV := Finset.mem_of_mem_erase hu
  have hlarge := hm u huV
  by_cases huv : D u v = true
  · have hvout : v ∈ outN D V u := mem_outN.mpr ⟨hv, huv⟩
    have hc := Finset.card_erase_add_one hvout
    rw [← outN_erase_eq u v] at hc
    exact ⟨u, mem_tightRows.mpr ⟨huV, by omega⟩, huv⟩
  · have hvout : v ∉ outN D V u := fun h => huv (mem_outN.mp h).2
    rw [outN_erase_eq, Finset.erase_eq_of_notMem hvout] at hsmall
    omega

private theorem reverse_walk {D : CH.Digraph} {W : Finset ℕ} {a b m : ℕ}
    (w : Walk D W a b m) (ha : a ∈ W) :
    Walk (fun x y => D y x) W b a m := by
  induction w with
  | refl a => exact .refl a
  | step hb hab _ ih => exact (ih hb).snoc ha hab

private theorem reverse_free {D : CH.Digraph} {W : Finset ℕ} {q : ℕ}
    (hf : QFree D W q) : QFree (fun x y => D y x) W q := by
  intro a m hm hmq w
  cases m with
  | zero => omega
  | succ m =>
    obtain ⟨_, _, ha, _⟩ := w.unsnoc
    exact hf a (m+1) hm hmq (reverse_walk w ha)

private theorem reverse_min_one {D : CH.Digraph} {V T : Finset ℕ}
    (hTV : T ⊆ V) (hcover : ∀ v ∈ V, ∃ a ∈ T, D a v = true) :
    ∀ a ∈ T, 1 ≤ (outN (fun x y => D y x) T a).card := by
  intro a ha
  obtain ⟨b, hb, hba⟩ := hcover a (hTV ha)
  exact Finset.card_pos.mpr ⟨b, mem_outN.mpr ⟨hb, hba⟩⟩

/-- Tight-parent coverage already forces at least q+1 distinct tight labels. -/
theorem parent_cover_card {D : CH.Digraph} {V T : Finset ℕ} {q : ℕ}
    (hq : 1 ≤ q) (hf : QFree D V q) (hne : V.Nonempty) (hTV : T ⊆ V)
    (hcover : ∀ v ∈ V, ∃ a ∈ T, D a v = true) :
    q+1 ≤ T.card := by
  obtain ⟨v,hv⟩ := hne
  obtain ⟨a,ha,_⟩ := hcover v hv
  have hc := dt_size hq (ball_q_one q hq)
    (reverse_free (hf.mono_set hTV)) (reverse_min_one hTV hcover) ⟨a,ha⟩
  simpa only [Nat.mul_one] using hc

/-- In a q+1 parent-covered bank, every internal row has at most one head. -/
theorem parent_bank_internal_cap {D : CH.Digraph} {V T : Finset ℕ} {q z : ℕ}
    (hq : 1 ≤ q) (hf : QFree D V q) (hTV : T ⊆ V) (hT : T.card = q+1)
    (hcover : ∀ v ∈ V, ∃ a ∈ T, D a v = true) (hz : z ∈ T) :
    (outN D T z).card ≤ 1 := by
  let R := ball (fun x y => D y x) T z (q-1)
  have hR := ball_one_growth (reverse_free (hf.mono_set hTV))
    (reverse_min_one hTV hcover) hz (q-1) (by omega)
  have hd : Disjoint (outN D T z) R := by
    apply Finset.disjoint_left.mpr
    intro x hx hxr
    obtain ⟨_, j, hj, w⟩ := mem_ball.mp hxr
    have wr : Walk D T x z j := reverse_walk w hz
    exact hf z (j+1) (by omega) (by omega)
      (.step (hTV (outN_subset hx)) (mem_outN.mp hx).2 (wr.mono hTV))
  have hc := Finset.card_le_card
    (Finset.union_subset (outN_subset (D:=D) (W:=T) (y:=z))
      (ball_subset (D:=fun x y => D y x) (W:=T) (u:=z) (k:=q-1)))
  rw [Finset.card_union_of_disjoint hd] at hc
  change q-1+1 ≤ R.card at hR
  omega

/-- One actual parent a→z excludes a whole reverse ball from z's return heads. -/
theorem parent_bank_return_cap {D : CH.Digraph} {V T : Finset ℕ} {q z : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hTV : T ⊆ V) (hT : T.card = q+1)
    (hcover : ∀ v ∈ V, ∃ a ∈ T, D a v = true) (hz : z ∈ V) :
    (outN D T z).card ≤ 2 := by
  obtain ⟨a,ha,haz⟩ := hcover z hz
  let R := ball (fun x y => D y x) T a (q-2)
  have hR := ball_one_growth (reverse_free (hf.mono_set hTV))
    (reverse_min_one hTV hcover) ha (q-2) (by omega)
  have hd : Disjoint (outN D T z) R := by
    apply Finset.disjoint_left.mpr
    intro x hx hxr
    obtain ⟨_, j, hj, w⟩ := mem_ball.mp hxr
    have wr : Walk D T x a j := reverse_walk w ha
    exact hf z ((j+1)+1) (by omega) (by omega)
      ((Walk.step (hTV (outN_subset hx)) (mem_outN.mp hx).2 (wr.mono hTV)).snoc hz haz)
  have hc := Finset.card_le_card
    (Finset.union_subset (outN_subset (D:=D) (W:=T) (y:=z))
      (ball_subset (D:=fun x y => D y x) (W:=T) (u:=a) (k:=q-2)))
  rw [Finset.card_union_of_disjoint hd] at hc
  change q-2+1 ≤ R.card at hR
  omega

/-- An actual exterior carrier. No IH or order bound is used in its construction. -/
theorem covered_bank_exterior_carrier {D : CH.Digraph} {V T : Finset ℕ} {q s : ℕ}
    (hq : 2 ≤ q) (hs : 2 ≤ s) (hf : QFree D V q)
    (hTV : T ⊆ V) (hT : T.card = q+1)
    (hcover : ∀ v ∈ V, ∃ a ∈ T, D a v = true)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hhigh : ∀ v ∈ V \ T, s+1 ≤ (outN D V v).card) :
    (V \ T).Nonempty ∧ ∀ v ∈ V \ T, s-1 ≤ (outN D (V \ T) v).card := by
  have split (v : ℕ) : (outN D V v).card =
      (outN D T v).card + (outN D (V \ T) v).card := by
    simpa only [Finset.union_sdiff_of_subset hTV] using
      card_outN_union (D:=D) (show Disjoint T (V \ T) from Finset.disjoint_sdiff) v
  constructor
  · obtain ⟨a,ha⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    have cap := parent_bank_internal_cap (by omega) hf hTV hT hcover ha
    have degree := hm a (hTV ha)
    have hsplit := split a
    obtain ⟨x,hx⟩ := Finset.card_pos.mp
      (show 0 < (outN D (V \ T) a).card by omega)
    exact ⟨x,outN_subset hx⟩
  · intro v hv
    have cap := parent_bank_return_cap hq hf hTV hT hcover (Finset.mem_sdiff.mp hv).1
    have degree := hhigh v hv
    have hsplit := split v
    omega

/-- Exactly q+1 tight rows force order at least q*s+2 via the actual exterior. -/
theorem tight_rows_eq_order_lower {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hq : 2 ≤ q) (hs : 2 ≤ s) (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hminimal : VertexMinimal D V s) (ih : PredDegreeOrder q s)
    (he : (tightRows D V s).card = q+1) :
    q*s+2 ≤ V.card := by
  let T := tightRows D V s
  have hTV : T ⊆ V := tightRows_subset
  have hcover : ∀ v ∈ V, ∃ a ∈ T, D a v = true :=
    fun v hv => exists_tight_parent (by omega) (by omega) hf hm hminimal hv
  have hhigh : ∀ v ∈ V \ T, s+1 ≤ (outN D V v).card := by
    intro v hv
    obtain ⟨hvV,hvT⟩ := Finset.mem_sdiff.mp hv
    have hdeg := hm v hvV
    have hne : (outN D V v).card ≠ s := fun h => hvT (mem_tightRows.mpr ⟨hvV,h⟩)
    omega
  obtain ⟨hne,hdeg⟩ := covered_bank_exterior_carrier hq hs hf hTV he hcover hm hhigh
  have bound := ih D (V \ T) (hf.mono_set Finset.sdiff_subset) hdeg hne
  have count := Finset.card_sdiff_add_card_eq_card hTV
  have hs1 : s-1+1=s := by omega
  have prod := congrArg (fun k => q*k) hs1
  simp only [Nat.mul_add, Nat.mul_one] at prod
  change (V \ T).card + (tightRows D V s).card = V.card at count
  omega

/-- The obstruction extends one label beyond critical order. -/
theorem tight_rows_ne_cutoff_succ {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hq : 2 ≤ q) (hs : 2 ≤ s) (hf : QFree D V q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hminimal : VertexMinimal D V s) (hn : V.card ≤ q*s+1)
    (ih : PredDegreeOrder q s) :
    (tightRows D V s).card ≠ q+1 := by
  intro he
  have bound := tight_rows_eq_order_lower hq hs hf hm hminimal ih he
  omega

/-- The stronger source-wide count; the predecessor-degree IH remains explicit. -/
theorem tight_rows_card_ge {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hq : 2 ≤ q) (hs : 2 ≤ s) (hf : QFree D V q) (hne : V.Nonempty)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hminimal : VertexMinimal D V s) (hn : V.card ≤ q*s)
    (ih : PredDegreeOrder q s) :
    q+2 ≤ (tightRows D V s).card := by
  have lo := parent_cover_card (by omega) hf hne tightRows_subset
    (fun v hv => exists_tight_parent (by omega) (by omega) hf hm hminimal hv)
  have ne := tight_rows_ne_cutoff_succ hq hs hf hm hminimal (by omega) ih
  omega

#print axioms exists_tight_parent
#print axioms parent_cover_card
#print axioms parent_bank_internal_cap
#print axioms parent_bank_return_cap
#print axioms covered_bank_exterior_carrier
#print axioms tight_rows_eq_order_lower
#print axioms tight_rows_ne_cutoff_succ
#print axioms tight_rows_card_ge
#check tight_rows_card_ge
end LeanCH.BR.DotTightParentCarrier
