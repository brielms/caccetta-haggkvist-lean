import checkpoints.shen_extension.ColumnBlockerEscape
import checkpoints.shen_extension.InducedPrimeTransition
import LeanCH.BR.BRWeightedCases

namespace LeanCH.BR.Closure.WeightedColumnEscape
open BRq2 BRq3 BR45 WeightedSD Finset

private theorem entry {D : CH.Digraph} {V : Finset ℕ} {p v x : ℕ}
    (eq : outN D V p = inN D V v) (hx : x ∈ V) : D p x=true ↔ D x v=true := by
  have same : x ∈ outN D V p ↔ x ∈ inN D V v := by rw [eq]
  simpa [mem_outN,mem_inN,hx] using same

/-- For a finite incidence matrix, containment of its column family in its row
family already gives equality. Repeated rows and columns are permitted. -/
theorem row_family_eq_columns {D : CH.Digraph} {V : Finset ℕ}
    (cols : ∀ v ∈ V, ∃ w ∈ V, outN D V w = inN D V v) :
    V.image (outN D V) = V.image (inN D V) := by
  classical
  let decode (T : Finset ℕ) := V.filter (fun j => ∃ r ∈ T, outN D V r = inN D V j)
  have decode_col {x} (hx : x ∈ V) : decode (inN D V x) = outN D V x := by
    ext z
    constructor
    · intro h
      obtain ⟨hz,r,hr,eq⟩ := mem_filter.mp h
      exact mem_outN.mpr ⟨hz,(entry eq hx).mp (mem_inN.mp hr).2⟩
    · intro h
      obtain ⟨hz,xz⟩ := mem_outN.mp h
      obtain ⟨r,hr,eq⟩ := cols z hz
      exact mem_filter.mpr ⟨hz,r,mem_inN.mpr ⟨hr,(entry eq hx).mpr xz⟩,eq⟩
  have sub : V.image (inN D V) ⊆ V.image (outN D V) := by
    rintro _ ht
    obtain ⟨v,hv,rfl⟩ := mem_image.mp ht
    obtain ⟨w,hw,eq⟩ := cols v hv
    exact mem_image.mpr ⟨w,hw,eq⟩
  have upper : V.image (outN D V) ⊆ (V.image (inN D V)).image decode := by
    intro T ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    exact mem_image.mpr ⟨_,mem_image_of_mem _ hx,decode_col hx⟩
  exact (eq_of_subset_of_card_le sub ((card_le_card upper).trans card_image_le)).symm

/-- For every specified vertex b, its row and two other rows are pairwise
disjoint and omit b. In a graph with a sink the empty row can be reused. -/
theorem three_rows_omit {D : CH.Digraph} {V : Finset ℕ} {b : ℕ}
    (safe : QFree D V 3) (cols : ∀ v ∈ V, ∃ w ∈ V, outN D V w = inN D V v)
    (hb : b ∈ V) :
    ∃ c ∈ V, ∃ p ∈ V,
      Disjoint (outN D V b) (outN D V c) ∧ Disjoint (outN D V b) (outN D V p) ∧
      Disjoint (outN D V c) (outN D V p) ∧ b ∉ outN D V b ∧ b ∉ outN D V c ∧
      b ∉ outN D V p := by
  classical
  have bb : b ∉ outN D V b := fun h => loopfree safe (by decide) hb (mem_outN.mp h).2
  by_cases heads : ∀ x ∈ V, 1 ≤ (outN D V x).card
  · have member := mem_image_of_mem (outN D V) hb
    rw [row_family_eq_columns cols] at member
    obtain ⟨a,ha,ba⟩ := mem_image.mp member
    obtain ⟨c,hc,cb⟩ := cols b hb
    obtain ⟨e,he,ec⟩ := cols c hc
    have next {j k : ℕ} (hk : k ∈ V) (eq : outN D V k = inN D V j) :
        Disjoint (inN D V j) (inN D V k) := disjoint_left.mpr (by
      intro t tj tk
      exact digonfree safe (by decide) hk (mem_inN.mp tj).1
        ((entry eq (mem_inN.mp tj).1).mpr (mem_inN.mp tj).2) (mem_inN.mp tk).2)
    have apart : Disjoint (outN D V b) (outN D V c) := by
      rw [← ba,cb]; exact next hb ba.symm
    have noC : b ∉ outN D V c := fun h => loopfree safe (by decide) hb ((entry cb hb).mp (mem_outN.mp h).2)
    by_cases disj : Disjoint (inN D V a) (inN D V c)
    · have noE : b ∉ outN D V e := by
        intro h
        have edge := (entry ec hb).mp (mem_outN.mp h).2
        obtain ⟨t,ht⟩ := card_pos.mp (heads c hc)
        have tb := (entry cb (outN_subset ht)).mp (mem_outN.mp ht).2
        exact safe b 3 (by decide) (by decide)
          (.step hc edge (.step (outN_subset ht) (mem_outN.mp ht).2 (.step hb tb (.refl b))))
      refine ⟨c,hc,e,he,apart,?_,?_,bb,noC,noE⟩
      · simpa only [← ba,ec] using disj
      · rw [cb,ec]; exact next hc cb
    · obtain ⟨x,xa,xc⟩ := not_disjoint_iff.mp disj
      have xv := (mem_inN.mp xa).1
      have bx := (entry ba.symm xv).mpr (mem_inN.mp xa).2
      have src := (ColumnBlockerEscape.local_counts safe heads (by decide) ha hb hc ba.symm cb
        (ec ▸ heads e he)).2 x (mem_inter.mpr ⟨xa,xc⟩)
      refine ⟨c,hc,x,xv,apart,?_,?_,bb,noC,fun h => digonfree safe (by decide) hb xv bx (mem_outN.mp h).2⟩
      · apply disjoint_left.mpr
        intro z zb xz
        obtain ⟨w,hw,matchZ⟩ := cols z (outN_subset zb)
        exact src.2 z (mem_inter.mpr ⟨ba.symm ▸ zb,xz⟩) w hw matchZ
      · apply disjoint_left.mpr
        intro t ct xt
        have tv := outN_subset ct
        have tb := (entry cb tv).mp (mem_outN.mp ct).2
        exact safe b 3 (by decide) (by decide)
          (.step xv bx (.step tv (mem_outN.mp xt).2 (.step hb tb (.refl b))))
  · push Not at heads
    obtain ⟨p,hp,size⟩ := heads
    have empty : outN D V p = ∅ := card_eq_zero.mp (by omega)
    exact ⟨p,hp,p,hp,by simp [empty],by simp [empty],by simp [empty],bb,by simp [empty],by simp [empty]⟩

private theorem out_sum {D : CH.Digraph} {V : Finset ℕ} {w : ℕ → ℚ} (u : ℕ) :
    outW D V w u = ∑ v ∈ outN D V u, w v := by simp [outW,outN,sum_filter]

/-- Every nonnegative rational weighting has a vertex whose weighted row score
is at most the whole mass. No normalization or twin-free condition is needed. -/
theorem light_row {D : CH.Digraph} {V : Finset ℕ} (safe : QFree D V 3) (live : V.Nonempty)
    (cols : ∀ v ∈ V, ∃ w ∈ V, outN D V w = inN D V v)
    (w : ℕ → ℚ) (nonneg : ∀ v ∈ V, 0 ≤ w v) :
    ∃ v ∈ V, row 3 D V w v ≤ mass V w := by
  classical
  obtain ⟨b,hb,top⟩ := V.exists_max_image w live
  obtain ⟨c,hc,p,hp,bc,bp,cp,mb,mc,mp⟩ := three_rows_omit safe cols hb
  let B := outN D V b
  let C := outN D V c
  let P := outN D V p
  have disj : Disjoint (B ∪ C) P := disjoint_union_left.mpr ⟨bp,cp⟩
  have miss : b ∉ (B ∪ C) ∪ P := by simp [B,C,P,mb,mc,mp]
  have sub : insert b ((B ∪ C) ∪ P) ⊆ V :=
    insert_subset hb (union_subset (union_subset outN_subset outN_subset) outN_subset)
  have bound := sum_le_sum_of_subset_of_nonneg (f:=w) sub (fun v hv _ => nonneg v hv)
  rw [sum_insert miss,sum_union disj,sum_union bc] at bound
  by_contra! high
  have rb := high b hb
  have rc := high c hc
  have rp := high p hp
  simp only [row,out_sum,Nat.cast_ofNat,mass] at rb rc rp
  dsimp only [B,C,P] at bound
  linarith [top c hc,top p hp]

/-- Direct input to the strict weighted prime transition, valid for any support. -/
theorem no_strict {D : CH.Digraph} {V : Finset ℕ} (safe : QFree D V 3) (live : V.Nonempty)
    (cols : ∀ v ∈ V, ∃ w ∈ V, outN D V w = inN D V v) (w : ℕ → ℕ) :
    ¬ ShenPrimeTransition.Strict 3 D V w := by
  obtain ⟨v,hv,le⟩ := light_row safe live cols (fun x => (w x : ℚ)) (by intros; positivity)
  exact fun high => (not_lt_of_ge le) (high v hv)

theorem no_strict_positive_rows {D : CH.Digraph} {V : Finset ℕ} (safe : QFree D V 3)
    (live : V.Nonempty) (cols : ∀ v ∈ V, ∃ w ∈ V, outN D V w = inN D V v) :
    ¬ StrictPositiveRows 3 D V := by
  rintro ⟨w,pos,unit,high⟩
  obtain ⟨v,hv,le⟩ := light_row safe live cols w (fun x hx => (pos x hx).le)
  rw [unit] at le
  exact (not_lt_of_ge le) (high v hv)

#print axioms row_family_eq_columns
#print axioms three_rows_omit
#print axioms light_row
#print axioms no_strict
#print axioms no_strict_positive_rows
end LeanCH.BR.Closure.WeightedColumnEscape
