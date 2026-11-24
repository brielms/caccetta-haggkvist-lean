import checkpoints.shen_extension.TwoReplacementNearMiss

namespace LeanCH.BR.Closure.SponsoredHeadPool
open Finset BRq2 BRq3 TwoReplacement TwoReplacement.NearMiss DeficitLevels

def parents (D : CH.Digraph) (W : Finset ℕ) (z : ℕ) := insert z (BR45.inN D W z)

/-- If the second parent set consists of parents of z, possibly including z,
all the old heads of z can serve the second copy with no further cuts. -/
theorem single_test {D : CH.Digraph} {W P Q : Finset ℕ} {z d : ℕ}
    (safe : QFree D W 3) (zw : z ∈ W) (sponsor : d ≤ (outN D W z).card)
    (q : Q ⊆ parents D W z)
    (base : ∀ x ∈ W, d ≤ (outN D W x).card+credit P Q x) :
    Feasible D W P Q d ↔ d ≤ (pool D W P Q P d).card := by
  constructor
  · exact fun test => test.2.1
  intro one
  have avoids {x} (head : x ∈ outN D W z) :
      x ∉ Q ∧ ∀ t ∈ outN D W x, t ∉ Q := by
    obtain ⟨xw,zx⟩ := mem_outN.mp head
    constructor
    · intro hit
      rcases mem_insert.mp (q hit) with rfl | parent
      · exact loopfree safe (by decide) zw zx
      · exact digonfree safe (by decide) zw xw zx (BR45.mem_inN.mp parent).2
    · intro t ht hit
      obtain ⟨tw,xt⟩ := mem_outN.mp ht
      rcases mem_insert.mp (q hit) with rfl | parent
      · exact digonfree safe (by decide) zw xw zx xt
      · exact safe z 3 (by decide) (by decide) (.step xw zx (.step tw xt
          (.step zw (BR45.mem_inN.mp parent).2 (.refl z))))
  have can {x : ℕ} {A : Finset ℕ} (head : x ∈ outN D W z) (hA : x ∈ pool D W P Q A d) :
      x ∈ pool D W P Q (A ∪ Q) d := by
    obtain ⟨xA,paid⟩ := mem_filter.mp hA
    obtain ⟨xw,xa⟩ := mem_sdiff.mp xA
    obtain ⟨xq,tq⟩ := avoids head
    have rows : outN D (W \ A) x ⊆ outN D (W \ (A ∪ Q)) x := by
      intro t ht
      obtain ⟨h,xt⟩ := mem_outN.mp ht
      obtain ⟨tw,ta⟩ := mem_sdiff.mp h
      exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨tw,fun u => (mem_union.mp u).elim ta
        (tq t (mem_outN.mpr ⟨tw,xt⟩))⟩,xt⟩
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨xw,fun u => (mem_union.mp u).elim xa xq⟩,
      paid.trans (Nat.add_le_add_right (card_le_card rows) _)⟩
  refine ⟨base,(assign_heads (pool_anti (R:=P) subset_union_left) (pool_anti (R:=Q) subset_union_right)).mp ?_⟩
  refine ⟨_,Subset.rfl,outN D W z,?_,one,sponsor,?_⟩
  · intro x head
    have xw := outN_subset head
    have emptyOk : x ∈ pool D W P Q ∅ d := by simp [pool,xw,base x xw]
    simpa only [empty_union] using can head emptyOk
  · exact fun x h => can (mem_inter.mp h).2 (mem_inter.mp h).1

private theorem split_row {D : CH.Digraph} {U S : Finset ℕ} (sub : S ⊆ U) (x : ℕ) :
    (outN D (U \ S) x).card+(outN D S x).card=(outN D U x).card := by
  have eq : outN D (U \ S) x = outN D U x \ outN D S x := by
    ext t; simp only [mem_outN,mem_sdiff]; tauto
  have inc : outN D S x ⊆ outN D U x := fun t ht =>
    mem_outN.mpr ⟨sub (outN_subset ht),(mem_outN.mp ht).2⟩
  rw [eq,card_sdiff_add_card_eq_card inc]

/-- Native row choices. All parents of z may pay the second copy. A
double-loss row needs the first copy only if it cannot parent the second. -/
theorem native_cap {D : CH.Digraph} {U S : Finset ℕ} {d z : ℕ}
    (law : OrderLaw 3 d (3*d+1)) (size : U.card=3*d+2) (sub : S ⊆ U)
    (four : S.card=4) (safe : QFree D (U \ S) 3)
    (exactRows : ∀ x ∈ U \ S, (outN D U x).card=d+1)
    (three : ∀ x ∈ U \ S, (outN D S x).card ≤ 3) (zw : z ∈ U \ S)
    (sponsor : d ≤ (outN D (U \ S) z).card)
    (covers : tripleRows D U S ⊆ parents D (U \ S) z) :
    let W := U \ S
    let R := doubleRows D U S
    let T := tripleRows D U S
    let J := parents D W z
    let P := T ∪ (R \ J)
    (pool D W P J P d).card < d ∧ commonBank D W R T d ⊆ pool D W P J P d := by
  intro W R T J P
  have jw : J ⊆ W := insert_subset zw (filter_subset _ _)
  have pw : P ⊆ W := union_subset (filter_subset _ _) (sdiff_subset.trans (filter_subset _ _))
  have base (x) (xw : x ∈ W) : d ≤ (outN D W x).card+credit P J x := by
    have count := split_row (D:=D) sub x
    rw [exactRows x xw] at count
    change (outN D W x).card + _ = _ at count
    by_cases xt : x ∈ T
    · have xj := covers xt
      have xp : x ∈ P := mem_union_left _ xt
      have := three x xw
      simp [credit,xp,show x ∈ J from xj]; omega
    have n3 : (outN D S x).card ≠ 3 := fun e => xt (mem_filter.mpr ⟨xw,e⟩)
    by_cases xr : x ∈ R
    · have lost : (outN D S x).card = 2 := (mem_filter.mp xr).2
      by_cases xj : x ∈ J
      · simp [credit,xj]; omega
      · have xp : x ∈ P := mem_union_right _ (mem_sdiff.mpr ⟨xr,xj⟩)
        simp [credit,xp,xj]; omega
    have n2 : (outN D S x).card ≠ 2 := fun e => xr (mem_filter.mpr ⟨xw,e⟩)
    have := three x xw
    omega
  constructor
  · by_contra! count
    exact critical_obstruction law size sub four safe P pw J jw ((single_test safe zw sponsor Subset.rfl base).mpr count)
  · have ps : P ⊆ T ∪ R := union_subset_union Subset.rfl sdiff_subset
    have kept : W \ (T ∪ R) ⊆ W \ P := fun y h =>
      mem_sdiff.mpr ⟨(mem_sdiff.mp h).1,fun yp => (mem_sdiff.mp h).2 (ps yp)⟩
    intro x hx
    obtain ⟨live,paid⟩ := mem_filter.mp hx
    have row : outN D (W \ (T ∪ R)) x ⊆ outN D (W \ P) x := fun y h =>
      mem_outN.mpr ⟨kept (outN_subset h),(mem_outN.mp h).2⟩
    exact mem_filter.mpr ⟨kept live,(paid.trans (card_le_card row)).trans (Nat.le_add_right _ _)⟩

#print axioms single_test
#print axioms native_cap

private theorem outside_pool_eq {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (law : OrderLaw 3 d (3*d+1)) (size : U.card=3*d+2) (sub : S ⊆ U)
    (four : S.card=4) (safe : QFree D (U \ S) 3)
    (exactRows : ∀ x ∈ U \ S, (outN D U x).card=d+1)
    (two : ∀ x ∈ U \ S, (outN D S x).card ≤ 2)
    (near : (commonBank D (U \ S) (doubleRows D U S) ∅ d).card+1=d) :
    let W := U \ S
    let R := doubleRows D U S
    let B := commonBank D W R ∅ d
    ∀ z ∈ W \ R, let J := parents D W z
      pool D W (R \ J) J (R \ J) d = B := by
  intro W R B z hz J
  obtain ⟨zw,zr⟩ := mem_sdiff.mp hz
  have nz : (outN D S z).card ≠ 2 := fun e => zr (mem_filter.mpr ⟨zw,e⟩)
  have sponsor : d ≤ (outN D W z).card := by
    have count := split_row (D:=D) sub z
    rw [exactRows z zw] at count
    change (outN D W z).card + _ = _ at count
    have := two z zw
    omega
  have empty : tripleRows D U S = ∅ := eq_empty_iff_forall_notMem.mpr (by
    intro x h; obtain ⟨xw,lost⟩ := mem_filter.mp h; have := two x xw; omega)
  let P := R \ J
  have cap := native_cap law size sub four safe exactRows (fun x hx => (two x hx).trans (by decide))
    zw sponsor (by rw [empty]; exact empty_subset _)
  dsimp only at cap
  simp only [empty,empty_union] at cap
  exact
    (eq_of_subset_of_card_le cap.2 (by change _ ≤ B.card; have h : B.card+1=d := near; have := cap.1; omega)).symm

/-- The missing head can be tracked across the child. If an exterior vertex
z is reached by r, some actual double-loss successor of r must miss z. -/
theorem native_missed_head {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (law : OrderLaw 3 d (3*d+1)) (size : U.card=3*d+2) (sub : S ⊆ U)
    (four : S.card=4) (safe : QFree D (U \ S) 3)
    (exactRows : ∀ x ∈ U \ S, (outN D U x).card=d+1)
    (two : ∀ x ∈ U \ S, (outN D S x).card ≤ 2)
    (near : (commonBank D (U \ S) (doubleRows D U S) ∅ d).card+1=d) :
    let W := U \ S
    let R := doubleRows D U S
    ∀ z ∈ W \ R, ∀ r ∈ R, D r z=true → ∃ t ∈ outN D R r, D t z≠true := by
  intro W R z hz r rr rz
  have rw' : R ⊆ W := filter_subset _ _
  let J := parents D W z
  let P := R \ J
  let B := commonBank D W R ∅ d
  have pools : pool D W P J P d = B := outside_pool_eq law size sub four safe exactRows two near z hz
  have rj : r ∈ J := mem_insert_of_mem (BR45.mem_inN.mpr ⟨rw' rr,rz⟩)
  have rp : r ∉ P := fun m => (mem_sdiff.mp m).2 rj
  have rb : r ∉ B := fun h => (mem_sdiff.mp (mem_filter.mp h).1).2 (mem_union_right _ rr)
  by_contra! no
  have same : outN D (W \ P) r = outN D W r := by
    ext t; constructor
    · intro h; exact mem_outN.mpr ⟨(mem_sdiff.mp (outN_subset h)).1,(mem_outN.mp h).2⟩
    · intro h
      obtain ⟨tw,rt⟩ := mem_outN.mp h
      refine mem_outN.mpr ⟨mem_sdiff.mpr ⟨tw,?_⟩,rt⟩
      intro tp
      obtain ⟨tr,tj⟩ := mem_sdiff.mp tp
      have tz := no t (mem_outN.mpr ⟨tr,rt⟩)
      exact tj (mem_insert_of_mem (BR45.mem_inN.mpr ⟨tw,by simpa using tz⟩))
  apply rb
  rw [← pools]
  refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨rw' rr,rp⟩,?_⟩
  rw [same]
  have lost : (outN D S r).card=2 := (mem_filter.mp rr).2
  have count := split_row (D:=D) sub r
  rw [exactRows r (rw' rr)] at count
  change (outN D W r).card + _ = _ at count
  simp [credit,rp,rj]; omega

#print axioms native_missed_head

/-- Keep both exterior labels. The middle labels counted by the intersection
are exactly the length-two paths from y to z through a double-loss row. -/
theorem two_step_cap {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (law : OrderLaw 3 d (3*d+1)) (size : U.card=3*d+2) (sub : S ⊆ U)
    (four : S.card=4) (safe : QFree D (U \ S) 3)
    (exactRows : ∀ x ∈ U \ S, (outN D U x).card=d+1)
    (two : ∀ x ∈ U \ S, (outN D S x).card ≤ 2)
    (near : (commonBank D (U \ S) (doubleRows D U S) ∅ d).card+1=d) :
    let W := U \ S
    let R := doubleRows D U S
    let E := W \ R
    let B := commonBank D W R ∅ d
    ∀ y ∈ E \ B, ∀ z ∈ E, (outN D E y).card +
      (outN D R y ∩ BR45.inN D W z).card + (if y=z ∨ D y z=true then 1 else 0) < d := by
  intro W R E B y hy z hz
  let J := parents D W z
  let P := R \ J
  have ⟨ye,yb⟩ := mem_sdiff.mp hy
  have ⟨yw,yr⟩ := mem_sdiff.mp ye
  have ⟨_,zr⟩ := mem_sdiff.mp hz
  have yp : y ∉ P := fun h => yr (mem_sdiff.mp h).1
  have jp : y ∈ J ↔ y=z ∨ D y z=true := by
    simp [J,parents,BR45.mem_inN,yw]
  have coins : credit P J y = (if y=z ∨ D y z=true then 1 else 0) := by
    simp [credit,yp,jp]
  have rows : outN D (W \ P) y = outN D E y ∪ (outN D R y ∩ BR45.inN D W z) := by
    ext t
    simp only [E,P,J,parents,mem_outN,BR45.mem_inN,mem_sdiff,mem_insert,mem_union,mem_inter]
    grind
  have dis : Disjoint (outN D E y) (outN D R y ∩ BR45.inN D W z) :=
    disjoint_left.mpr (fun t h h' => (mem_sdiff.mp (outN_subset h)).2 (outN_subset (mem_inter.mp h').1))
  by_contra! enough
  have eq : pool D W P J P d = B := outside_pool_eq law size sub four safe exactRows two near z hz
  apply yb
  rw [← eq]
  refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨yw,yp⟩,?_⟩
  rwa [rows,card_union_of_disjoint dis,coins]

#print axioms two_step_cap
end LeanCH.BR.Closure.SponsoredHeadPool
