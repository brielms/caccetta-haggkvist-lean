import checkpoints.shen_extension.ContainerTransfer

/-! Mixed-radius reachability on one host. The ordered pair (x,y) uses
the actual difference between its two reachability rows. -/
namespace LeanCH.BR.ShenLabelledReach
open BRq2 BRq3 BR45 ShenFirstStrip
open Classical

noncomputable def rowDiff (D : CH.Digraph) (V : Finset ℕ) (radius : ℕ → ℕ)
    (x y : ℕ) : Finset ℕ := ball D V x (radius x) \ ball D V y (radius y)

/-- Row x supplies a path. Only labels present in row x and absent from row y
can pay for its terminal predecessors. -/
noncomputable def cost (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) (radius : ℕ → ℕ)
    (x y : ℕ) : ℕ :=
  let e := (rowDiff D V radius x y).card
  if radius y+e+1≤q then min (radius x) e else radius x

theorem lift_entry {D : CH.Digraph} {V : Finset ℕ} {q x y : ℕ} {radius : ℕ → ℕ}
    (hf : QFree D V q) (hx : x∈V) (hr : radius x≤q)
    (hne : x≠y)
    (hxy : y∈ball D V x (radius x)) :
    ∃ l, 1≤l ∧ l≤cost D V q radius x y ∧ Walk D V x y l := by
  obtain ⟨_,l,hl,w⟩ := mem_ball.mp hxy
  refine ⟨l,?_,?_,w⟩
  · cases l with
    | zero => cases w; exact (hne rfl).elim
    | succ l => omega
  · dsimp only [cost]
    split_ifs with hz
    · exact le_min hl (ShenContainerTransfer.walk_length_le_target_omissions
        hf hx (Finset.Subset.refl _) hl (hl.trans hr) w hz le_rfl)
    · exact hl

/-- A named predecessor that can return to y inside the remaining budget
occupies a specific missing column in y's row. -/
theorem predecessor_cell {D : CH.Digraph} {V : Finset ℕ} {q x y z l : ℕ} {radius : ℕ → ℕ}
    (hf : QFree D V q) (hz : z∈ball D V x (radius x)) (hl : 0<l)
    (hw : Walk D V z y l) (hbudget : radius y+l≤q) : z∈rowDiff D V radius x y := by
  refine Finset.mem_sdiff.mpr ⟨hz,?_⟩
  intro hback
  obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hback
  exact hf y (j+l) (by omega) (by omega) (wj.append hw)

/-- If both labelled reach entries are present, x's ball must have at least
q-radius(y) private labels absent from y's ball. Swapping x,y gives the
second bound. This has no small-omission or common-container hypothesis. -/
theorem mutual_separation {D : CH.Digraph} {V : Finset ℕ} {q x y : ℕ} {radius : ℕ → ℕ}
    (hf : QFree D V q) (hx : x∈V) (hr : radius x≤q) (hne : x≠y)
    (hxy : y∈ball D V x (radius x)) (hyx : x∈ball D V y (radius y)) :
    q-radius y≤(rowDiff D V radius x y).card := by
  by_contra! small
  have guard : radius y+(rowDiff D V radius x y).card+1≤q := by omega
  obtain ⟨i,hi,hb,wi⟩ := lift_entry hf hx hr hne hxy
  simp [cost,guard] at hb
  obtain ⟨_,j,hj,wj⟩ := mem_ball.mp hyx
  exact hf x (i+j) (by omega) (by omega) (wi.append wj)

/-- For any sequence of named, non-diagonal reach entries, concatenate their
actual original walks, charging each entry its own row/column cost. -/
theorem lift_chain {D : CH.Digraph} {V C : Finset ℕ} {q : ℕ} {radius : ℕ → ℕ}
    (hf : QFree D V q) (hCV : C⊆V) (hr : ∀ x∈C, radius x≤q)
    (f : ℕ → ℕ) (l : ℕ)
    (hedge : ∀ i<l, f i∈C ∧ f i≠f (i+1) ∧ f (i+1)∈ball D V (f i) (radius (f i))) :
    ∃ m, l≤m ∧ m≤∑ i∈Finset.range l, cost D V q radius (f i) (f (i+1)) ∧
      Walk D V (f 0) (f l) m := by
  induction l with
  | zero => exact ⟨0,by omega,by simp,.refl _⟩
  | succ l ih =>
    obtain ⟨m,hl,hm,w⟩ := ih (fun i hi => hedge i (by omega))
    obtain ⟨hc,hne,hreach⟩ := hedge l (by omega)
    obtain ⟨j,hj,hcost,step⟩ := lift_entry hf (hCV hc) (hr _ hc) hne hreach
    refine ⟨m+j,by omega,?_,w.append step⟩
    rw [Finset.sum_range_succ]; omega

/-- Every actual labelled cycle exceeds the cutoff in the sum of its edge
costs, for all cutoffs, all bank sizes, and all admissible radius assignments. -/
theorem cycle_cost {D : CH.Digraph} {V C : Finset ℕ} {q : ℕ} {radius : ℕ → ℕ}
    (hf : QFree D V q) (hCV : C⊆V) (hr : ∀ x∈C, radius x≤q)
    (f : ℕ → ℕ) (l : ℕ)
    (hl : 0<l) (hclosed : f l=f 0)
    (hedge : ∀ i<l, f i∈C ∧ f i≠f (i+1) ∧ f (i+1)∈ball D V (f i) (radius (f i))) :
    q<∑ i∈Finset.range l, cost D V q radius (f i) (f (i+1)) := by
  obtain ⟨m,h1,h2,w⟩ := lift_chain hf hCV hr f l hedge
  rw [hclosed] at w
  by_contra! hbad
  exact hf _ m (by omega) (by omega) w

/-- At each eligible ordered pair at least one of the two literal reach
entries must vanish. -/
theorem pair_missing {D : CH.Digraph} {V C : Finset ℕ} {q x y : ℕ} {radius : ℕ → ℕ}
    (hf : QFree D V q) (hCV : C⊆V) (hr : ∀ x∈C, radius x≤q)
    (hx : x∈C) (hy : y∈C) (hne : x≠y)
    (hcost : cost D V q radius x y + cost D V q radius y x≤q) :
    y∉ball D V x (radius x) ∨ x∉ball D V y (radius y) := by
  by_contra! both
  obtain ⟨i,hi,h1,wx⟩ := lift_entry hf (hCV hx) (hr _ hx) hne both.1
  obtain ⟨j,_,h2,wy⟩ := lift_entry hf (hCV hy) (hr _ hy) hne.symm both.2
  exact hf _ (i+j) (by omega) (by omega) (wx.append wy)

#print axioms lift_entry
#print axioms predecessor_cell
#print axioms mutual_separation
#print axioms cycle_cost
#print axioms pair_missing

/-- Target labels that are outside the i-ball, reachable in l steps, and
whose j-ball leaves too few private labels in the actual l-ball of x. -/
noncomputable def forcedOmissions (D : CH.Digraph) (V : Finset ℕ) (q i j l x : ℕ) : Finset ℕ :=
  (ball D V x l \ ball D V x i).filter
    (fun y => (ball D V x l \ ball D V y j).card < q-j)

/-- Each of the selected pairs is an actual missing entry of the
complementary reach tensor. Distinct y give distinct entries in row x. -/
theorem forced_omission_cells {D : CH.Digraph} {V : Finset ℕ} {q i j l x : ℕ}
    (hf : QFree D V q) (hx : x∈V) (hl : l≤q) :
    forcedOmissions D V q i j l x ⊆ V \ (ball D V x i ∪ reverseBall D V x j) := by
  intro y hy
  obtain ⟨hyset,small⟩ := Finset.mem_filter.mp hy
  obtain ⟨hyreach,hyout⟩ := Finset.mem_sdiff.mp hyset
  refine Finset.mem_sdiff.mpr ⟨ball_subset hyreach,?_⟩
  intro hb
  rcases Finset.mem_union.mp hb with hi|hj
  · exact hyout hi
  obtain ⟨_,p,hp,wp⟩ := mem_ball.mp hyreach
  obtain ⟨_,r,hr,wr⟩ := mem_ball.mp (Finset.mem_filter.mp hj).2
  have pos : 0<p := by
    cases p with
    | zero => cases wp; exact (hyout (self_mem_ball hx)).elim
    | succ p => omega
  have hp' := ShenContainerTransfer.walk_length_le_target_omissions
    (i:=l) (j:=j) (K:=ball D V x l) (e:=(ball D V x l \ ball D V y j).card)
    hf hx (Finset.Subset.refl _) hp (hp.trans hl) wp (by omega) le_rfl
  exact hf x (p+r) (by omega) (by omega) (wp.append wr)

/-- Shen's two-ball capacity with an additional term computed from actual
three-vertex incidences. No minimum-degree, flatness or strip assumption. -/
theorem overlap_capacity {D : CH.Digraph} {V : Finset ℕ} {q i j l : ℕ}
    (hf : QFree D V q) (hpair : i+j≤q) (hl : l≤q) :
    (∑ x∈V, (forcedOmissions D V q i j l x).card) +
    (∑ x∈V, (ball D V x i).card) + (∑ x∈V, (ball D V x j).card) ≤ V.card*(V.card+1) := by
  have cells := Finset.sum_le_sum (s:=V) (fun x hx =>
    Finset.card_le_card (forced_omission_cells (i:=i) (j:=j) hf hx hl))
  have capacity := tensor_capacity_identity hf hpair
  omega

#print axioms forced_omission_cells
#print axioms overlap_capacity

/-- At equality every root outside the i-ball but inside its l-ball must
leave at least q-j actual labels uncovered in that l-ball. -/
theorem saturated_separation {D : CH.Digraph} {V : Finset ℕ} {q i j l A B x y : ℕ}
    (hf : QFree D V q) (hpair : i+j≤q) (hl : l≤q)
    (hA : ∀ u∈V, A≤(ball D V u i).card) (hB : ∀ u∈V, B≤(ball D V u j).card)
    (heq : A+B=V.card+1) (hx : x∈V) (hy : y∈ball D V x l \ ball D V x i) :
    q-j≤(ball D V x l \ ball D V y j).card := by
  by_contra! small
  have miss := forced_omission_cells (j:=j) hf hx hl
    (show y∈forcedOmissions D V q i j l x from Finset.mem_filter.mpr ⟨hy,small⟩)
  obtain ⟨hyV,hnot⟩ := Finset.mem_sdiff.mp miss
  apply hnot
  apply Finset.mem_union_right
  rw [two_balls_boundary_complement hf hpair hA hB heq hx]
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hyV,(Finset.mem_sdiff.mp hy).2⟩)

#print axioms saturated_separation

/-- A reach entry is available to a smaller-degree theorem only when its
own ordered-pair cost is paid. Original arcs are always available at cost one. -/
noncomputable def paidReach (D : CH.Digraph) (V : Finset ℕ) (q e : ℕ)
    (radius : ℕ → ℕ) : CH.Digraph := fun x y => decide
  (x≠y ∧ (D x y=true ∨ (y∈ball D V x (radius x) ∧ cost D V q radius x y≤e)))

/-- Apply a checked CH order theorem to the actual graph of paid entries.
Outgoing entries may use different overlap witnesses even within one row. -/
theorem paid_reach_order {D : CH.Digraph} {V C : Finset ℕ} {q e p d L : ℕ}
    {radius : ℕ → ℕ}
    (order : ∀ F W, QFree F W p → (∀ v∈W, d≤(outN F W v).card) → W.Nonempty → L≤W.card)
    (hf : QFree D V q) (hCV : C⊆V) (hr : ∀ x∈C, radius x≤q)
    (he : 1≤e) (hbudget : e*p≤q) (hne : C.Nonempty)
    (hrows : ∀ x∈C, d≤(outN (paidReach D V q e radius) C x).card) : L≤C.card := by
  apply order _ _ _ hrows hne
  apply DotTwoPassShellTransport.qfree_of_bounded_arc_lift hf hbudget
  intro x hx y hy hxy
  obtain ⟨hneq,edge|⟨hb,hcost⟩⟩ := of_decide_eq_true hxy
  · exact ⟨1,le_rfl,he,.step (hCV hy) edge (.refl y)⟩
  · obtain ⟨j,hj,hl,w⟩ := lift_entry hf (hCV hx) (hr x hx) hneq hb
    exact ⟨j,hj,hl.trans hcost,w⟩

/-- Degree three supplies an unconditional consumer at every positive p. -/
theorem paid_reach_degree_three {D : CH.Digraph} {V C : Finset ℕ} {q e p : ℕ}
    {radius : ℕ → ℕ} (hf : QFree D V q) (hCV : C⊆V) (hr : ∀ x∈C, radius x≤q)
    (he : 1≤e) (hp : 1≤p) (hbudget : e*p≤q) (hne : C.Nonempty)
    (hrows : ∀ x∈C, 3≤(outN (paidReach D V q e radius) C x).card) :
    p*3+1≤C.card :=
  paid_reach_order (fun _ _ h m ne => dt_size hp (ball_all p hp) h m ne)
    hf hCV hr he hbudget hne hrows

#print axioms paid_reach_degree_three
end LeanCH.BR.ShenLabelledReach
