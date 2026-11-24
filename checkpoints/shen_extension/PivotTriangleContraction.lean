import checkpoints.shen_extension.RecursiveDeficitLevels
import checkpoints.shen_extension.dot_tensor_research.DotOriginalStarReturn_20261118

/-! Compress a deleted set by two labels using independent copies of the same star. -/
namespace LeanCH.BR.Closure.PivotContraction
open Finset BRq2 BRq3 DotOriginalStarReturn DeficitLevels

/-- Adjoin the rows having at least two heads in the given set. -/
def grow (D : CH.Digraph) (U S : Finset ℕ) : Finset ℕ :=
  U.filter (fun x => x ∈ S ∨ 2 ≤ (outN D S x).card)

private theorem project_walk {D : CH.Digraph} {X W : Finset ℕ} (p : ℕ → ℕ)
    (into : ∀ x ∈ X, p x ∈ W) {a b j : ℕ}
    (w : Walk (fun x y => D (p x) (p y)) X a b j) : Walk D W (p a) (p b) j := by
  induction w with
  | refl => exact .refl _
  | step hb edge _ ih => exact .step (into _ hb) edge ih

/-- Replace the one new vertex of star_qfree with independent copies on K.
The two banks P and C have, respectively, a deficit payable by K and
enough heads outside P to pay for their share of the cut. -/
theorem twin_star {D : CH.Digraph} {W K P C : Finset ℕ} {d : ℕ}
    (safe : QFree D W 3) (klive : K.Nonempty) (wk : Disjoint W K)
    (pw : P ⊆ W) (cw : C ⊆ W) (pc : Disjoint P C)
    (heads : d ≤ C.card)
    (parentDegree : ∀ x ∈ P, d ≤ (outN D W x).card + K.card)
    (headDegree : ∀ x ∈ C, d ≤ (outN D (W \ P) x).card)
    (otherDegree : ∀ x ∈ W, x ∉ P → d ≤ (outN D W x).card) :
    ∃ E, QFree E (W ∪ K) 3 ∧ ∀ x ∈ W ∪ K, d ≤ (outN E (W ∪ K) x).card := by
  obtain ⟨z,zk⟩ := klive
  have fresh : z ∉ W := fun zw => disjoint_left.mp wk zw zk
  let p : ℕ → ℕ := fun x => if x ∈ K then z else x
  let H := star D W P C z
  let E : CH.Digraph := fun x y => H (p x) (p y)
  have old {x} (hx : x ∈ W) : p x = x := by simp [p,disjoint_left.mp wk hx]
  have copy {x} (hx : x ∈ K) : p x = z := by simp [p,hx]
  have maps (x) (hx : x ∈ W ∪ K) : p x ∈ insert z W := by
    rcases mem_union.mp hx with h | h
    · rw [old h]; exact mem_insert_of_mem h
    · rw [copy h]; exact mem_insert_self _ _
  have starSafe := star_qfree safe fresh pw cw pc
  refine ⟨E,fun a n hn hq w => starSafe (p a) n hn hq (project_walk p maps w),?_⟩
  have retained {x y} (xw : x ∈ W) (yw : y ∈ W) (edge : D x y = true)
      (cut : x ∉ C ∨ y ∉ P) : y ∈ outN E (W ∪ K) x := by
    apply mem_outN.mpr
    refine ⟨mem_union_left _ yw,?_⟩
    change H (p x) (p y) = true
    rw [old xw,old yw]
    exact (star_old_edge fresh xw yw).mpr ⟨edge,cut⟩
  intro x hx
  rcases mem_union.mp hx with xw | xk
  · by_cases xc : x ∈ C
    · apply (headDegree x xc).trans
      apply card_le_card
      intro y hy
      obtain ⟨yr,edge⟩ := mem_outN.mp hy
      exact retained xw (mem_sdiff.mp yr).1 edge (Or.inr (mem_sdiff.mp yr).2)
    have oldHeads : outN D W x ⊆ outN E (W ∪ K) x := fun y hy =>
      retained xw (mem_outN.mp hy).1 (mem_outN.mp hy).2 (Or.inl xc)
    by_cases xp : x ∈ P
    · have extra : K ⊆ outN E (W ∪ K) x := by
        intro k hk
        apply mem_outN.mpr
        refine ⟨mem_union_right _ hk,?_⟩
        change H (p x) (p k) = true
        rw [old xw,copy hk]
        exact (star_incoming fresh cw).mpr xp
      have cnt := card_le_card (union_subset oldHeads extra)
      rw [card_union_of_disjoint (wk.mono_left outN_subset)] at cnt
      exact (parentDegree x xp).trans cnt
    · exact (otherDegree x xw xp).trans (card_le_card oldHeads)
  · apply heads.trans
    apply card_le_card
    intro y hy
    apply mem_outN.mpr
    refine ⟨mem_union_left _ (cw hy),?_⟩
    change H (p x) (p y) = true
    rw [copy xk,old (cw hy)]
    exact (star_outgoing fresh pw).mpr hy

private theorem split_row {D : CH.Digraph} {U S : Finset ℕ} (sub : S ⊆ U) (x : ℕ) :
    (outN D (U \ S) x).card + (outN D S x).card = (outN D U x).card := by
  have eq : outN D (U \ S) x = outN D U x \ outN D S x := by
    ext y
    simp only [mem_outN,mem_sdiff]
    tauto
  have incl : outN D S x ⊆ outN D U x := fun y hy =>
    mem_outN.mpr ⟨sub (mem_outN.mp hy).1,(mem_outN.mp hy).2⟩
  rw [eq,card_sdiff_add_card_eq_card incl]

/-- At order 3d+2, a set containing all short cycles with no common external
parent contracts to order 3d if its second growth leaves d labels outside. -/
theorem critical_contraction {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (order : U.card = 3*d+2) (sub : S ⊆ U) (three : 3 ≤ S.card)
    (safe : QFree D (U \ S) 3)
    (degree : ∀ x ∈ U \ S, d+1 ≤ (outN D U x).card)
    (miss : ∀ x ∈ U \ S, (outN D S x).card < S.card)
    (size : (grow D U (grow D U S)).card ≤ 2*d+2) :
    ∃ E X, X.Nonempty ∧ X.card = 3*d ∧ QFree E X 3 ∧ ∀ x ∈ X, d ≤ (outN E X x).card := by
  let W := U \ S
  let F := grow D U S
  let F₂ := grow D U F
  let P := F \ S
  let C := U \ F₂
  obtain ⟨K,ks,kcard⟩ := exists_subset_card_eq (Nat.sub_le S.card 2)
  have klive : K.Nonempty := card_pos.mp (by omega)
  have wk : Disjoint W K := disjoint_left.mpr (fun _ xw xk => (mem_sdiff.mp xw).2 (ks xk))
  have fU : F ⊆ U := filter_subset _ _
  have ffU : F₂ ⊆ U := filter_subset _ _
  have sf : S ⊆ F := fun x hx => mem_filter.mpr ⟨sub hx,Or.inl hx⟩
  have ff : F ⊆ F₂ := fun x hx => mem_filter.mpr ⟨fU hx,Or.inl hx⟩
  have pw : P ⊆ W := fun x hx => mem_sdiff.mpr ⟨fU (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩
  have cw : C ⊆ W := fun x hx => mem_sdiff.mpr
    ⟨(mem_sdiff.mp hx).1,fun xs => (mem_sdiff.mp hx).2 (ff (sf xs))⟩
  have pc : Disjoint P C := disjoint_left.mpr (fun _ xp xc =>
    (mem_sdiff.mp xc).2 (ff (mem_sdiff.mp xp).1))
  have heads : d ≤ C.card := by
    have c := card_sdiff_add_card_eq_card ffU
    change (U \ F₂).card + F₂.card = U.card at c
    change F₂.card ≤ 2*d+2 at size
    change d ≤ (U \ F₂).card
    omega
  have parentDegree (x) (xp : x ∈ P) : d ≤ (outN D W x).card + K.card := by
    have deg := degree x (pw xp)
    have m := miss x (pw xp)
    have split := split_row (D:=D) sub x
    change d ≤ (outN D (U \ S) x).card + K.card
    omega
  have headDegree (x) (xc : x ∈ C) : d ≤ (outN D (W \ P) x).card := by
    have xU := (mem_sdiff.mp xc).1
    have few : ¬ 2 ≤ (outN D F x).card := fun many =>
      (mem_sdiff.mp xc).2 (mem_filter.mpr ⟨xU,Or.inr many⟩)
    have eq : W \ P = U \ F := by
      ext y
      simp only [W,P,mem_sdiff]
      grind
    rw [eq]
    have deg := degree x (cw xc)
    have split := split_row (D:=D) fU x
    omega
  have otherDegree (x) (xw : x ∈ W) (xp : x ∉ P) : d ≤ (outN D W x).card := by
    have few : ¬ 2 ≤ (outN D S x).card := fun many =>
      xp (mem_sdiff.mpr ⟨mem_filter.mpr ⟨(mem_sdiff.mp xw).1,Or.inr many⟩,(mem_sdiff.mp xw).2⟩)
    have deg := degree x xw
    have split := split_row (D:=D) sub x
    change d ≤ (outN D (U \ S) x).card
    omega
  obtain ⟨E,ef,ed⟩ := twin_star safe klive wk pw cw pc heads parentDegree headDegree otherDegree
  refine ⟨E,W ∪ K,klive.mono (subset_union_right),?_,ef,ed⟩
  rw [card_union_of_disjoint wk]
  have wsize := card_sdiff_add_card_eq_card sub
  change (U \ S).card + K.card = 3*d
  omega

/-- The exact lower-degree law bars the specified small second growth. -/
theorem growth_obstruction {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (law : OrderLaw 3 d (3*d+1)) (order : U.card = 3*d+2)
    (sub : S ⊆ U) (three : 3 ≤ S.card) (safe : QFree D (U \ S) 3)
    (degree : ∀ x ∈ U \ S, d+1 ≤ (outN D U x).card)
    (miss : ∀ x ∈ U \ S, (outN D S x).card < S.card) :
    2*d+3 ≤ (grow D U (grow D U S)).card := by
  by_contra! small
  obtain ⟨E,X,live,card,hf,deg⟩ := critical_contraction order sub three safe degree miss (by omega)
  have := law E X hf deg live
  omega

/-- The converse for one new label. Even arbitrary deletions among old labels
cannot evade the row bound or enlarge the bank of possible heads of v. -/
theorem one_vertex_necessary {D E : CH.Digraph} {W : Finset ℕ} {d v : ℕ}
    (fresh : v ∉ W) (safe : QFree E (insert v W) 3)
    (degree : ∀ x ∈ insert v W, d ≤ (outN E (insert v W) x).card)
    (old : ∀ x ∈ W, ∀ y ∈ W, E x y = true → D x y = true) :
    (∀ x ∈ W, d ≤ (outN D W x).card + 1) ∧
    let P := W.filter (fun x => (outN D W x).card < d)
    outN E (insert v W) v ⊆ (W \ P).filter (fun y => d ≤ (outN D (W \ P) y).card) := by
  let P := W.filter (fun x => (outN D W x).card < d)
  have split (x) (xw : x ∈ W) :
      outN E (insert v W) x ⊆ insert v (outN D W x) := by
    intro y hy
    obtain ⟨inX,edge⟩ := mem_outN.mp hy
    rcases mem_insert.mp inX with rfl | yw
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_outN.mpr ⟨yw,old _ xw _ yw edge⟩)
  have input (x) (xp : x ∈ P) : E x v = true := by
    obtain ⟨xw,low⟩ := mem_filter.mp xp
    by_contra no
    have sub : outN E (insert v W) x ⊆ outN D W x := by
      intro y hy
      refine (mem_insert.mp (split x xw hy)).resolve_left ?_
      intro e
      exact no (e ▸ (mem_outN.mp hy).2)
    have bound := card_le_card sub
    have floor := degree x (mem_insert_of_mem xw)
    omega
  constructor
  · intro x xw
    have cap := card_le_card (split x xw)
    rw [card_insert_of_notMem (fun h => fresh (mem_outN.mp h).1)] at cap
    exact (degree x (mem_insert_of_mem xw)).trans cap
  · change outN E (insert v W) v ⊆ (W \ P).filter _
    intro y hy
    obtain ⟨yX,vy⟩ := mem_outN.mp hy
    have vX := mem_insert_self v W
    have yw : y ∈ W := (mem_insert.mp yX).resolve_left (fun e =>
      loopfree safe (by decide) vX (e ▸ vy))
    have noBack := digonfree safe (by decide : 2 ≤ 3) vX yX vy
    have yp : y ∉ P := fun h => noBack (input y h)
    apply mem_filter.mpr
    refine ⟨mem_sdiff.mpr ⟨yw,yp⟩,(degree y yX).trans (card_le_card ?_)⟩
    intro z hz
    obtain ⟨zX,yz⟩ := mem_outN.mp hz
    have zw := (mem_insert.mp zX).resolve_left (fun e => noBack (e ▸ yz))
    have zp : z ∉ P := fun h => safe v 3 (by decide) (by decide)
      (.step yX vy (.step zX yz (.step vX (input z h) (.refl v))))
    exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨zw,zp⟩,old y yw z zw yz⟩

/-- Adjoining all common parents to S guarantees that each survivor misses a label. -/
theorem misses_after_parents {D : CH.Digraph} {U S : Finset ℕ} :
    let A := S ∪ U.filter (fun x => ∀ y ∈ S, D x y = true)
    ∀ x ∈ U \ A, (outN D A x).card < A.card := by
  classical
  intro A x hx
  by_contra! large
  have eq : outN D A x = A := eq_of_subset_of_card_le outN_subset large
  have every (y) (hy : y ∈ S) : D x y = true := by
    have ha : y ∈ outN D A x := eq.symm ▸ (mem_union_left _ hy : y ∈ A)
    exact (mem_outN.mp ha).2
  exact (mem_sdiff.mp hx).2 (mem_union_right _ (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,every⟩))

#print axioms one_vertex_necessary
#print axioms misses_after_parents
#print axioms twin_star
#print axioms critical_contraction
#print axioms growth_obstruction
end LeanCH.BR.Closure.PivotContraction
