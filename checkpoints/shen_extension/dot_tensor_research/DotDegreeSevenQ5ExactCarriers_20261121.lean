import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactSupport_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen
open scoped BigOperators

/-- A label reached from a return carrier in at most two steps, with at
most one missing B-head, forbids all B-arcs entering that carrier. -/
theorem exact_return_carrier_no_parent {D : CH.Digraph} {V B : Finset ℕ}
    (hf : QFree D V 5) (bV : B⊆V)
    {w x k : ℕ} (hw : w∈B) (_xV : x∈V) (hk : k≤2) (ret : Walk D V w x k)
    (miss : (B \ outN D V x).card≤1) :
    ∀ y∈B, D y w ≠ true := by
  have nw : w∉outN D V x := by
    intro h
    exact hf w (k+1) (by omega) (by omega)
      (ret.append (.step (bV hw) (mem_outN.mp h).2 (.refl w)))
  have hsingle : B \ outN D V x = {w} := by
    apply (eq_of_subset_of_card_le ?_ ?_).symm
    · simpa using mem_sdiff.mpr ⟨hw,nw⟩
    · simpa using miss
  intro y hy e
  have ne : y ≠ w := by
    rintro rfl
    exact loopfree hf (by decide) (bV hy) e
  have ey : D x y=true := by
    by_contra h
    have m : y∈B \ outN D V x :=
      mem_sdiff.mpr ⟨hy,fun m => h (mem_outN.mp m).2⟩
    rw [hsingle] at m
    exact ne (mem_singleton.mp m)
  exact hf w (k+2) (by omega) (by omega)
    (ret.append (.step (bV hy) ey (.step (bV hw) e (.refl w))))

/-- A witness retains its own two actual common-miss rows. Distinct
carriers cannot reuse either row of such a witness. -/
theorem exact_two_witness_carriers {D : CH.Digraph} {V A B R : Finset ℕ}
    (hmiss : ∀ x∈A, (B \ outN D V x).card≤1)
    (witness : ∀ w∈R, ∃ x∈A, ∃ y∈A, x≠y ∧ w∈B ∧
      w∉outN D V x ∧ w∉outN D V y) :
    2*R.card≤A.card := by
  classical
  let F (w : ℕ) := A.filter (fun x => w∈B \ outN D V x)
  have pair : (R : Set ℕ).PairwiseDisjoint F := by
    intro v hv w hw hne
    apply disjoint_left.mpr
    intro x h1 h2
    have k := hmiss x (mem_filter.mp h1).1
    have le := card_le_card (show {v,w} ⊆ B \ outN D V x by
      intro a ha
      rcases mem_insert.mp ha with h|h
      · subst a; exact (mem_filter.mp h1).2
      · rw [mem_singleton] at h
        subst a; exact (mem_filter.mp h2).2)
    rw [card_insert_of_notMem (by simpa using hne), card_singleton] at le
    omega
  have two (w) (hw : w∈R) : 2≤(F w).card := by
    obtain ⟨x,hx,y,hy,hne,wb,wx,wy⟩ := witness w hw
    have le := card_le_card (show {x,y} ⊆ F w by
      intro a ha
      rcases mem_insert.mp ha with h|h
      · subst a; exact mem_filter.mpr ⟨hx,mem_sdiff.mpr ⟨wb,wx⟩⟩
      · rw [mem_singleton] at h
        subst a; exact mem_filter.mpr ⟨hy,mem_sdiff.mpr ⟨wb,wy⟩⟩)
    rwa [card_insert_of_notMem (by simpa using hne),card_singleton] at le
  have upper := card_le_card (show R.biUnion F⊆A by
    intro x hx
    obtain ⟨w,hw,hx⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hx).1)
  rw [card_biUnion pair] at upper
  have lower : (∑ w ∈ R, (2 : ℕ)) ≤ ∑ w ∈ R, (F w).card :=
    Finset.sum_le_sum (fun w hw => two w hw)
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using lower.trans upper
/-- No nonempty bank of these actual short returns can survive if
every B-row's exits outside B or T belong to the same carrier bank. -/
theorem exact_no_nonempty_carrier_bank {D : CH.Digraph} {V A B R T : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card≤35)
    (cap : ∀ v∈V, (ball D V v 2).card≤15)
    (bV : B⊆V) (tV : T⊆V) (disj : Disjoint B T)
    (a7 : A.card≤7) (b7 : B.card=7) (t6 : T.card≤6)
    (hmiss : ∀ x∈A, (B \ outN D V x).card≤1)
    (witness : ∀ w∈R, ∃ x∈A, ∃ y∈A, x≠y ∧ w∈B ∧
      w∉outN D V x ∧ w∉outN D V y)
    (ret : ∀ w∈R, ∃ x∈A, x∈V ∧ ∃ k≤2, Walk D V w x k)
    (keep : ∀ b∈B \ R, outN D V b⊆B∪T) (rpos : R.Nonempty) : False := by
  have rb : R⊆B := by
    intro w hw
    obtain ⟨_,_,_,_,_,e,_,_⟩ := witness w hw
    exact e
  have size := exact_two_witness_carriers hmiss witness
  have eq := card_sdiff_of_subset rb
  have rp := rpos.card_pos
  have ne : (B \ R).Nonempty := card_pos.mp (by omega)
  apply exact_endpoint_no_supported_bank hf ho n cap
    ((sdiff_subset : B \ R⊆B).trans bV) tV (disj.mono_left sdiff_subset) ne (by omega) t6
  intro b hb y hy
  have kb := keep b hb hy
  rcases mem_union.mp kb with hyb|hyt
  · apply mem_union_left
    refine mem_sdiff.mpr ⟨hyb,?_⟩
    intro yr
    obtain ⟨x,hx,xV,k,hk,wr⟩ := ret y yr
    exact exact_return_carrier_no_parent hf bV hyb xV hk wr (hmiss x hx)
      b (mem_sdiff.mp hb).1 (mem_outN.mp hy).2
  · exact mem_union_right _ hyt

#print axioms exact_return_carrier_no_parent
#print axioms exact_two_witness_carriers
#print axioms exact_no_nonempty_carrier_bank

end LeanCH.BR.DotDegreeSevenLow



