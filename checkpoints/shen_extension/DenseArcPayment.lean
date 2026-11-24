import checkpoints.shen_extension.DenseArcRectangle
import checkpoints.shen_extension.PivotTriangleContraction
import checkpoints.shen_extension.UnitLoopCapstone

namespace LeanCH.BR.Closure.DenseArc
open Finset BRq2 BRq3 DeficitLevels

private theorem partition {D : CH.Digraph} {X T : Finset ℕ} (sub : T ⊆ X) (x : ℕ) :
    (outN D (X \ T) x).card + (outN D T x).card = (outN D X x).card := by
  have eq : outN D (X \ T) x = outN D X x \ outN D T x := by
    ext z; simp only [mem_outN,mem_sdiff]; tauto
  rw [eq,card_sdiff_add_card_eq_card (show outN D T x ⊆ outN D X x from
    fun z hz => mem_outN.mpr ⟨sub (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩)]

/-- Actual labelled return edges. The edge from y to h and from h to z
is supplied by the caller. Every member of K points to y. -/
def ReturnThrough (D : CH.Digraph) (V K : Finset ℕ) (d ℓ y z : ℕ) : Prop :=
  2 ≤ (outN D K z).card ∨
  (ℓ=3 ∧ ∃ b ∈ V \ insert y K, D z b=true ∧ (outN D V b).card=d+1 ∧
    K.card ≤ (outN D K b).card+(if D b y then 1 else 0))

/-- At the first failing degree, deleting the marked vertex and K, then
absorbing every row too short for its clones, forces overloaded original
heads. cap bounds the number of deleted labels seen by a surviving row. -/
theorem payment {D V d ℓ y} {K : Finset ℕ} (safe : QFree D V 3)
    (degree : ∀ v∈V, d+1 ≤ (outN D V v).card) (law : OrderLaw 3 d (3*d+1))
    (yv : y∈V) (kv : K ⊆ V) (parents : ∀p∈K, D p y=true)
    (cap : ∀ x∈V \ insert y K, (outN D (insert y K) x).card ≤ K.card)
    (budget : V.card ≤ 3*d+ℓ) (three : ℓ≤3) (enough : ℓ≤K.card) :
    ∃ bad ⊆ outN D V y, (outN D V y).card+1 ≤ d+bad.card ∧
      ∀ h∈bad, ∃ witnesses ⊆ outN D V h, (outN D V h).card+1 ≤ d+witnesses.card ∧
        ∀ z∈witnesses, ReturnThrough D V K d ℓ y z := by
  classical
  let S := insert y K
  let W := V \ S
  let H := outN D V y
  let m := S.card-ℓ
  let B := W.filter (fun x => (outN D W x).card+m<d)
  let U := W \ B
  let P := U.filter (fun x => (outN D U x).card<d)
  let C := H.filter (fun h => d ≤ (outN D (U \ P) h).card)
  have ys : y∉K := fun hy => loopfree safe (by decide) yv (parents _ hy)
  have sc : S.card=K.card+1 := card_insert_of_notMem ys
  have sv : S ⊆ V := insert_subset yv kv
  have wv : W ⊆ V := sdiff_subset
  have bw : B ⊆ W := filter_subset _ _
  have uw : U ⊆ W := sdiff_subset
  have pu : P ⊆ U := filter_subset _ _
  have cv : C ⊆ H := filter_subset _ _
  have miss (h) (hh : h∈H) (p) (ps : p∈S) : D h p ≠ true := by
    obtain ⟨hv,yh⟩ := mem_outN.mp hh
    rcases mem_insert.mp ps with rfl | pk
    · exact digonfree safe (by decide) yv hv yh
    · intro hp
      exact safe y 3 (by decide) (by decide)
        (.step hv yh (.step (kv pk) hp (.step yv (parents _ pk) (.refl _))))
  have hw (h) (hh : h∈H) : h∈W := by
    refine mem_sdiff.mpr ⟨(mem_outN.mp hh).1,?_⟩
    intro hs
    rcases mem_insert.mp hs with rfl | hk
    · exact loopfree safe (by decide) yv (mem_outN.mp hh).2
    · exact digonfree safe (by decide) yv (kv hk) (mem_outN.mp hh).2 (parents _ hk)
  have old (h) (hh : h∈H) : outN D W h = outN D V h := by
    ext p; simp only [W,mem_outN,mem_sdiff]
    exact ⟨fun t => ⟨t.1.1,t.2⟩,fun t => ⟨⟨t.1,fun ps => miss h hh p ps t.2⟩,t.2⟩⟩
  have hu (h) (hh : h∈H) : h∈U := by
    refine mem_sdiff.mpr ⟨hw h hh,?_⟩
    intro hb
    have short := (mem_filter.mp hb).2
    rw [old h hh] at short
    have := degree h (mem_outN.mp hh).1
    omega
  have baseline (x) (hx : x∈U) : d ≤ (outN D U x).card+(m+B.card) := by
    have ⟨xw,xb⟩ := mem_sdiff.mp hx
    have ge : d ≤ (outN D W x).card+m := by
      by_contra! short; exact xb (mem_filter.mpr ⟨xw,short⟩)
    have split := partition (D:=D) bw x
    have lim := card_le_card (show outN D B x ⊆ B from outN_subset)
    dsimp only [U]; omega
  have few : C.card < d := by
    by_contra! big
    have sb : Disjoint S B := disjoint_left.mpr (fun x xs xb => (mem_sdiff.mp (bw xb)).2 xs)
    have sbc := card_union_of_disjoint sb
    have mp : 0<m := by dsimp [m]; omega
    have mb : m+B.card ≤ (S∪B).card := by dsimp [m]; omega
    obtain ⟨J,js,jc⟩ := exists_subset_card_eq mb
    have uj : Disjoint U J := by
      apply disjoint_left.mpr; intro x xu xj
      rcases mem_union.mp (js xj) with xs|xb
      · exact (mem_sdiff.mp (uw xu)).2 xs
      · exact (mem_sdiff.mp xu).2 xb
    have cu : C ⊆ U := fun h hc => hu h (cv hc)
    have pc : Disjoint P C := by
      apply disjoint_left.mpr; intro x xp xc
      have ge := (mem_filter.mp xc).2
      have lt := (mem_filter.mp xp).2
      have mono : outN D (U\P) x ⊆ outN D U x := fun z hz =>
        mem_outN.mpr ⟨(mem_sdiff.mp (mem_outN.mp hz).1).1,(mem_outN.mp hz).2⟩
      have := card_le_card mono
      omega
    have live : J.Nonempty := card_pos.mp (by omega)
    obtain ⟨E,ef,ed⟩ := PivotContraction.twin_star (safe.mono_set (uw.trans wv)) live uj pu cu pc big
      (fun x hx => jc ▸ baseline x (pu hx)) (fun x hx => (mem_filter.mp hx).2)
      (fun x xu xp => by by_contra! lt; exact xp (mem_filter.mpr ⟨xu,lt⟩))
    have price := law E _ ef ed (live.mono (subset_union_right (s₁:=U)))
    rw [card_union_of_disjoint uj,jc] at price
    have s1 := card_sdiff_add_card_eq_card sv
    have s2 := card_sdiff_add_card_eq_card bw
    dsimp only [W,U,m] at price
    dsimp only [W] at s2
    omega
  have badc := card_sdiff_add_card_eq_card cv
  refine ⟨H\C,sdiff_subset,by change H.card+1 ≤ d+(H\C).card; omega,?_⟩
  intro h hb
  obtain ⟨hh,hc⟩ := mem_sdiff.mp hb
  have poor : (outN D (U\P) h).card<d := by
    by_contra! ok; exact hc (mem_filter.mpr ⟨hh,ok⟩)
  have first := partition (D:=D) bw h
  rw [old h hh] at first
  have second := partition (D:=D) pu h
  let Z := outN D B h ∪ outN D P h
  have disj : Disjoint (outN D B h) (outN D P h) := disjoint_left.mpr (fun z zb zp =>
    (mem_sdiff.mp (pu (mem_outN.mp zp).1)).2 (mem_outN.mp zb).1)
  have zc : Z.card=_ := card_union_of_disjoint disj
  have zw (z) (hz : z∈Z) : z∈W ∧ D h z=true := by
    rcases mem_union.mp hz with b|p
    · exact ⟨bw (mem_outN.mp b).1,(mem_outN.mp b).2⟩
    · exact ⟨uw (pu (mem_outN.mp p).1),(mem_outN.mp p).2⟩
  refine ⟨Z,(fun z hz => mem_outN.mpr ⟨wv (zw z hz).1,(zw z hz).2⟩),by
    change (outN D (W\B) h).card + _ = _ at first
    change (outN D (U\P) h).card + _ = (outN D (W\B) h).card at second
    omega,?_⟩
  intro z hz
  obtain ⟨zW,he⟩ := zw z hz
  have zd := degree z (wv zW)
  have zy : D z y ≠ true := fun e => safe y 3 (by decide) (by decide)
    (.step (mem_outN.mp hh).1 (mem_outN.mp hh).2 (.step (wv zW) he (.step yv e (.refl _))))
  have split := partition (D:=D) sv z
  have same : outN D S z=outN D K z := by ext p; simp only [S,mem_outN,mem_insert]; grind
  rw [same] at split
  by_cases short : (outN D W z).card<d
  · left; change (outN D W z).card+_= _ at split; omega
  have zp : z∈P := by
    rcases mem_union.mp hz with b|p
    · have := (mem_filter.mp (mem_outN.mp b).1).2; omega
    · exact (mem_outN.mp p).1
  have loss := partition (D:=D) bw z
  have now := (mem_filter.mp zp).2
  change (outN D U z).card+_= _ at loss
  obtain ⟨b,hit⟩ := card_pos.mp (show 0<(outN D B z).card by omega)
  have bb := (mem_outN.mp hit).1
  have lift := (mem_filter.mp bb).2
  have lim := cap b (bw bb)
  have bs := partition (D:=D) sv b
  change (outN D W b).card + (outN D S b).card = _ at bs
  have bd := degree b (wv (bw bb))
  have one : (outN D S b).card ≤ (outN D K b).card+1 := by
    have inc : outN D S b ⊆ insert y (outN D K b) := by
      intro p hp
      rcases mem_insert.mp (mem_outN.mp hp).1 with rfl|pk
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_outN.mpr ⟨pk,(mem_outN.mp hp).2⟩)
    exact (card_le_card inc).trans (card_insert_le _ _)
  change (outN D S b).card ≤ K.card at lim
  dsimp only [m] at lift
  refine Or.inr ⟨by omega,b,bw bb,(mem_outN.mp hit).2,by omega,?_⟩
  by_cases byy : D b y=true
  · simp [byy]; omega
  · have eq : outN D S b=outN D K b := by ext p; simp only [S,mem_outN,mem_insert]; grind
    rw [if_neg byy,Nat.add_zero,← eq]
    omega

#print axioms payment

/-- The same dense fan supplies both the maximization and the returns.
Two net deletions suffice below top order, leaving only four-cycle returns. -/
def FanReturns (D : CH.Digraph) (V : Finset ℕ) (d : ℕ) : Prop :=
  ∃ u ∈ V, ∃ y ∈ V, D u y=true ∧
    (∀ v ∈ V, ∀ z ∈ V, D v z=true → (middle D V v z).card ≤ (middle D V u y).card) ∧
    4*(d+1) ≤ V.card+3*(middle D V u y).card ∧
    let ℓ := if V.card≤3*d+2 then 2 else 3
    let K := insert u (middle D V u y)
    ∃ bad ⊆ outN D V y, (outN D V y).card+1 ≤ d+bad.card ∧
      ∀ h∈bad, ∃ witnesses ⊆ outN D V h, (outN D V h).card+1 ≤ d+witnesses.card ∧
        ∀ z∈witnesses, ReturnThrough D V K d ℓ y z

theorem at_origin {d} (O : Origin 3 (d+1)) (law : OrderLaw 3 d (3*d+1)) :
    FanReturns O.G O.V d := by
  classical
  have order := O.order
  have dpos := UnitState.origin_degree_pos O
  have big : 4 ≤ d+1 := by
    by_contra! small
    have half : HalfLawSupply.HalfLaw d := by
      have : d≤2 := by omega
      interval_cases d <;> first | exact HalfLawSupply.halfLaw_one | exact HalfLawSupply.halfLaw_two
    exact HalfLawSupply.no_source_of_halfLaw (s:=d+1) (by omega) (by simpa using half)
      O.free O.ne order O.deg
  obtain ⟨u,uv,y,yv,e,top,rich⟩ := supply O.free O.ne (by omega : 0<d+1) O.deg
  refine ⟨u,uv,y,yv,e,top,rich,?_⟩
  let F := middle O.G O.V u y
  let K := insert u F
  let ℓ := if O.V.card≤3*d+2 then 2 else 3
  have uf : u∉F := fun h => loopfree O.free (by decide) uv (mem_outN.mp (mem_filter.mp h).1).2
  have kc : K.card=F.card+1 := card_insert_of_notMem uf
  have members (p) (hp : p∈K) : p∈O.V ∧ O.G p y=true := by
    rcases mem_insert.mp hp with rfl|pf
    · exact ⟨uv,e⟩
    · exact ⟨(mem_outN.mp (mem_filter.mp pf).1).1,(mem_filter.mp pf).2⟩
  have yk : y∉K := fun hy => loopfree O.free (by decide) yv (members _ hy).2
  have cap (x) (hx : x∈O.V \ insert y K) : (outN O.G (insert y K) x).card ≤ K.card := by
    by_contra! high
    have sc := card_insert_of_notMem yk
    have eq := eq_of_subset_of_card_le (show outN O.G (insert y K) x ⊆ insert y K from outN_subset)
      (by omega)
    have hit (p) (hp : p∈insert y K) : O.G x p = true :=
      (mem_outN.mp (eq.symm ▸ hp)).2
    have inc : K ⊆ middle O.G O.V x y := fun p hp =>
      mem_filter.mpr ⟨mem_outN.mpr ⟨(members p hp).1,hit p (mem_insert_of_mem hp)⟩,(members p hp).2⟩
    have first := card_le_card inc
    have last := top x (mem_sdiff.mp hx).1 y yv (hit y (mem_insert_self _ _))
    change _ ≤ F.card at last
    omega
  have l3 : ℓ≤3 := by unfold ℓ; split <;> omega
  have bd : O.V.card ≤ 3*d+ℓ := by unfold ℓ; split <;> omega
  change 4*(d+1)≤O.V.card+3*F.card at rich
  exact payment O.free O.deg law yv (fun _ hp => (members _ hp).1) (fun _ hp => (members _ hp).2)
    cap bd l3 (show ℓ≤K.card by omega)

/-- The family graph retains the previous recursive alternatives on the same
least-degree origin and carries the new return witnesses on that origin. -/
theorem from_candidate {D V q s} (hq : 2≤q) (free : QFree D V q) (live : V.Nonempty)
    (bound : V.card ≤ q*s) (deg : ∀ v∈V, s ≤ (outN D V v).card) :
    ∃ d, d+1≤s ∧ ∃ (O : Origin q (d+1)) (st : State), PackingFrontier.Frontier O st ∧
      UnitLoopCapstone.AlternativesWithLoops O st ∧ (q=3 → FanReturns O.G O.V d) := by
  obtain ⟨d,le,O,st,fr,alt⟩ := UnitLoopCapstone.from_candidate hq free live bound deg
  refine ⟨d,le,O,st,fr,alt,?_⟩
  rintro rfl
  exact at_origin O fr.lower

#print axioms at_origin
#print axioms from_candidate
end LeanCH.BR.Closure.DenseArc
