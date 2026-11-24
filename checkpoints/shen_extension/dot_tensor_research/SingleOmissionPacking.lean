import LeanCH.BR.BRFiniteWalk
import LeanCH.BR.BR45KillC

namespace LeanCH.BR.SingleOmissionPacking
open Finset BRq2 BRq3 BR45
abbrev Sink (D : CH.Digraph) (A : Finset ℕ) (s : ℕ) := ∀ z∈A, D s z≠true

/-- A path to a sink omits the other sink, leaving at most q−2 arcs. -/
private theorem short {D A q} (f : QFree D A q) (hq : 4≤q) (n : A.card≤q)
    {s t} (sA : s∈A) (tA : t∈A) (st : s≠t) (ss : Sink D A s) (ts : Sink D A t)
    {v w k} (vA : v∈A) (p : Walk D A v w k) : k+2≤q := by
  classical
  by_contra! big
  obtain ⟨g,g0,_,ed⟩ := p.toFun
  have inj : (range (q-1) : Set ℕ).InjOn g := by
    intro i hi j hj eq
    change i∈range (q-1) at hi
    change j∈range (q-1) at hj
    simp only [mem_range] at hi hj
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with lt|gt
    · have path := walk_between ed lt.le (by omega : j≤k)
      rw [←eq] at path
      exact f _ _ (by omega) (by omega) path
    · have path := walk_between ed gt.le (by omega : i≤k)
      rw [eq] at path
      exact f _ _ (by omega) (by omega) path
  have sub : (range (q-1)).image g ⊆ (A.erase s).erase t := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    have i6 := mem_range.mp hi
    have e := ed i (by omega)
    have gm : g i∈A := by
      cases i with
      | zero => simpa only [g0] using vA
      | succ j => exact (ed j (by omega)).1
    exact mem_erase.mpr ⟨fun eq=>ts _ e.1 (eq ▸ e.2),
      mem_erase.mpr ⟨fun eq=>ss _ e.1 (eq ▸ e.2),gm⟩⟩
  have h := card_le_card sub
  rw [card_image_of_injOn inj,card_range,card_erase_of_mem (mem_erase.mpr ⟨st.symm,tA⟩),
    card_erase_of_mem sA] at h
  omega

private noncomputable def basin (D : CH.Digraph) (A : Finset ℕ) (b : ℕ) : Finset ℕ := by
  classical
  exact A.filter (fun z=>∃r∈outN D A b, ∃ k, Walk D A r z k)

private theorem packed_path {D A b q} (f : QFree D A q) (n : A.card≤q)
    (live : (outN D A b).Nonempty) :
    ∃ r∈outN D A b, ∃ s∈A, Sink D A s ∧ ∃m, Walk D A r s m ∧
      (outN D A b).card+m≤(basin D A b).card := by
  classical
  let P (k : ℕ) := ∃r∈outN D A b, ∃s∈A, Sink D A s ∧ Walk D A r s k
  obtain ⟨r,rr⟩ := live
  obtain ⟨s,sa,ss,k,kl,walk⟩ := reach_sink_of_card f n (mem_outN.mp rr).1
  have ex : ∃k,P k := ⟨k,r,rr,s,sa,ss,walk⟩
  let m := Nat.find ex
  have ml : m<q := (Nat.find_min' ex (show P k from ⟨r,rr,s,sa,ss,walk⟩)).trans_lt (by omega)
  obtain ⟨r,rr,s,sa,ss,w⟩ := (Nat.find_spec ex : P m)
  obtain ⟨g,g0,gm,ed⟩ := w.toFun
  let J := (range (m+1)).erase 0
  have inj : (J:Set ℕ).InjOn g := by
    intro i hi j hj eq
    have il := mem_range.mp (mem_of_mem_erase (show i∈J from hi))
    have jl := mem_range.mp (mem_of_mem_erase (show j∈J from hj))
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with lt|gt
    · have path := walk_between ed lt.le (by omega : j≤m)
      rw [←eq] at path
      exact f _ _ (by omega) (by omega) path
    · have path := walk_between ed gt.le (by omega : i≤m)
      rw [eq] at path
      exact f _ _ (by omega) (by omega) path
  have rc : outN D A b⊆basin D A b := fun x hx=>
    mem_filter.mpr ⟨(mem_outN.mp hx).1,x,hx,0,.refl _⟩
  have cross (i) (hi : i∈J) : g i∉outN D A b := by
    intro rmem
    have il := mem_range.mp (mem_of_mem_erase hi)
    have ni := (mem_erase.mp hi).1
    have path := walk_between ed (by omega : i≤m) le_rfl
    rw [gm] at path
    have := Nat.find_min' ex (show P (m-i) from ⟨_,rmem,s,sa,ss,path⟩)
    change m≤m-i at this
    omega
  have sub : J.image g⊆basin D A b := by
    intro x hx
    obtain ⟨i,im,rfl⟩ := mem_image.mp hx
    have il := mem_range.mp (mem_of_mem_erase im)
    have ip := (mem_erase.mp im).1
    have path := walk_between ed (Nat.zero_le i) (by omega : i≤m)
    rw [g0,Nat.sub_zero] at path
    have gmA : g i∈A := by
      cases i with
      | zero => contradiction
      | succ j => exact (ed j (by omega)).1
    exact mem_filter.mpr ⟨gmA,r,rr,i,path⟩
  have dis : Disjoint (outN D A b) (J.image g) := disjoint_left.mpr (by
    intro x hx xi
    obtain ⟨i,im,rfl⟩ := mem_image.mp xi
    exact cross i im hx)
  have count := card_le_card (union_subset rc sub)
  rw [card_union_of_disjoint dis,card_image_of_injOn inj] at count
  have jc : J.card=m := by simp [J]
  exact ⟨r,rr,s,sa,ss,m,w,by omega⟩


/-- Two first-layer sinks contradict simultaneous saturation of the sinks'
two-step balls. The two-step lower bound is used only at actual sinks. -/
theorem two_sinks_false_of_sink_ball_size {D V A B T q} (hq : 4≤q) (hf : QFree D V q)
    (av : A⊆V) (bv : B⊆V) (na : A.card≤q)
    {s₀ t₀ : ℕ} (sA : s₀∈A) (tA : t₀∈A) (st : s₀≠t₀)
    (sSink : Sink D A s₀) (tSink : Sink D A t₀)
    (omitOne : ∀s∈A,Sink D A s → ∃b∈B,outN D V s=B.erase b)
    (row : ∀ b∈B, outN D V b⊆(A∪B)∪T)
    (ballSize : ∀s∈A,Sink D A s → B.card+T.card+2≤(ball D V s 2).card) : False := by
  classical
  let R := fun b=>outN D A b
  let M := B.filter (fun b=>(R b).Nonempty)
  let f := hf.mono_set av
  have mb : M⊆B := filter_subset _ _
  have live (i) (im : i∈M) : (R i).Nonempty := (mem_filter.mp im).2
  have sr (v) (hv : v∈A) {w k} (p : Walk D A v w k) : k+2≤q :=
    short f hq na sA tA st sSink tSink hv p
  have omitReach {i r s k} (im : i∈B) (rm : r∈R i) (p : Walk D A r s k)
      (sA : s∈A) : D s i≠true := by
    intro si
    have k5 := sr r (mem_outN.mp rm).1 p
    exact hf r (k+1+1) (by omega) (by omega)
      (((p.mono av).snoc (bv im) si).snoc (av (mem_outN.mp rm).1) (mem_outN.mp rm).2)
  have exc {i r s k} (im : i∈B) (rm : r∈R i) (p : Walk D A r s k) (sa : s∈A)
      (ss : Sink D A s) : outN D V s=B.erase i := by
    obtain ⟨j,jb,eq⟩ := omitOne s sa ss
    have ij : i=j := by
      by_contra ne
      have h : i∈outN D V s := eq ▸ mem_erase.mpr ⟨ne,im⟩
      exact omitReach im rm p sa (mem_outN.mp h).2
    simpa only [ij] using eq
  have color {i j s} (ib : i∈B) (jb : j∈B)
      (ei : outN D V s=B.erase i) (ej : outN D V s=B.erase j) : i=j := by
    by_contra ne
    have h : i∈B.erase j := mem_erase.mpr ⟨ne,ib⟩
    rw [←ej,ei] at h
    exact (mem_erase.mp h).1 rfl
  have disj {i j} (im : i∈M) (jm : j∈M) (ne : i≠j) :
      Disjoint (basin D A i) (basin D A j) := disjoint_left.mpr (by
    intro z zi zj
    obtain ⟨za,r,rm,k,p⟩ := mem_filter.mp zi
    obtain ⟨_,a,am,h,w⟩ := mem_filter.mp zj
    obtain ⟨s,sa,ss,_,_,tail⟩ := reach_sink_of_card f na za
    exact ne (color (mb im) (mb jm) (exc (mb im) rm (p.append tail) sa ss)
      (exc (mb jm) am (w.append tail) sa ss)))
  have spec (i) (im : i∈M) : ∃ r∈R i, ∃ s∈A, Sink D A s ∧ ∃m,
      Walk D A r s m ∧ (R i).card+m≤(basin D A i).card :=
    packed_path f na (live i im)
  choose r rr s sa ss m p bound using spec
  have out (i) (im : i∈M) := exc (mb im) (rr i im) (p i im) (sa i im) (ss i im)
  have cross {i j} (im : i∈M) (jm : j∈M) (ij : i≠j) : q≤m i im+m j jm+3 := by
    have si : j∈outN D V (s i im) := out i im ▸ mem_erase.mpr ⟨ij.symm,mb jm⟩
    have sj : i∈outN D V (s j jm) := out j jm ▸ mem_erase.mpr ⟨ij,mb im⟩
    have a := (p i im).mono av
    have b := (p j jm).mono av
    have wa := (a.snoc (bv (mb jm)) (mem_outN.mp si).2).snoc
      (av (mem_outN.mp (rr j jm)).1) (mem_outN.mp (rr j jm)).2
    have wb := (b.snoc (bv (mb im)) (mem_outN.mp sj).2).snoc
      (av (mem_outN.mp (rr i im)).1) (mem_outN.mp (rr i im)).2
    by_contra! small
    exact hf _ _ (by omega) (by omega) (wa.append wb)
  let pred (i : ℕ) := ∃y∈B,D y i=true
  have long (i) (im : i∈M) (par : pred i) : q≤m i im+2 := by
    obtain ⟨y,yb,yi⟩ := par
    have yi' : y≠i := by rintro rfl; exact loopfree hf (by omega) (bv yb) yi
    have sy : y∈outN D V (s i im) := out i im ▸ mem_erase.mpr ⟨yi',yb⟩
    have path := (((p i im).mono av).snoc (bv yb) (mem_outN.mp sy).2).snoc (bv (mb im)) yi
    by_contra! sm
    exact hf _ _ (by omega) (by omega)
      (path.snoc (av (mem_outN.mp (rr i im)).1) (mem_outN.mp (rr i im)).2)
  have tax {s i} (as : s∈A) (stop : Sink D A s) (ib : i∈B) (eq : outN D V s=B.erase i)
      (E : Finset ℕ) (cover : ∀j∈M,j≠i→R j⊆E) :
      2≤E.card+(if pred i then 1 else 0) := by
    let X := B.erase i
    let Q : Finset ℕ := if pred i then {i} else ∅
    have qq : Q.card=(if pred i then 1 else 0) := by dsimp [Q]; split <;> simp
    have cntX : X.card+1=B.card := by
      have := card_pos.mpr (show B.Nonempty from ⟨_,ib⟩)
      simp only [X,card_erase_of_mem ib]; omega
    have cub : ball D V s 2 ⊆ insert s (((X∪T)∪E)∪Q) := by
      intro z z2
      by_cases same : z=s
      · exact mem_insert.mpr (Or.inl same)
      apply mem_insert_of_mem
      obtain ⟨y,hy,yz⟩ := exists_pred (av as) z2 same
      rcases (mem_ball_one (av as)).mp hy with rfl|ys
      · have h : z∈X := by change z∈B.erase i; rw [←eq]; exact mem_outN.mpr ⟨ball_subset z2,yz⟩
        exact mem_union_left _ (mem_union_left _ (mem_union_left _ h))
      have yX : y∈X := by change y∈B.erase i; rwa [←eq]
      obtain ⟨yi,yB⟩ := mem_erase.mp yX
      have zrow := row y yB (mem_outN.mpr ⟨ball_subset z2,yz⟩)
      rcases mem_union.mp zrow with ab|zt
      · rcases mem_union.mp ab with za|zb
        · have zr : z∈R y := mem_outN.mpr ⟨za,yz⟩
          exact mem_union_left _ (mem_union_right _ (cover y (mem_filter.mpr ⟨yB,⟨_,zr⟩⟩) yi zr))
        · by_cases zi : z=i
          · subst z
            have hp : pred i := ⟨_,yB,yz⟩
            exact mem_union_right _ (by simp [Q,hp])
          · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_erase.mpr ⟨zi,zb⟩)))
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ zt))
    have c := card_le_card cub
    have c0 := card_insert_le s (((X∪T)∪E)∪Q)
    have c1 := card_union_le ((X∪T)∪E) Q
    have c2 := card_union_le (X∪T) E
    have c3 := card_union_le X T
    have b := ballSize s as stop
    omega
  have many (i) (ib : i∈B) (x) (xa : x∈A) (stop : Sink D A x)
      (ex : outN D V x=B.erase i) : ∃j∈M,j≠i := by
    by_contra! all
    have u := tax xa stop ib ex ∅ (fun j jm ne => (ne (all j jm)).elim)
    simp only [card_empty,zero_add] at u
    split at u <;> omega
  obtain ⟨a,ab,eq⟩ := omitOne s₀ sA sSink
  obtain ⟨i,im,_⟩ := many a ab s₀ sA sSink eq
  obtain ⟨j,jm,ji⟩ := many i (mb im) _ (sa i im) (ss i im) (out i im)
  have pos (v) (vm : v∈M) := card_pos.mpr (live v vm)
  have inside (v : ℕ) : basin D A v ⊆ A := filter_subset _ _
  have two := card_le_card (union_subset (inside i) (inside j))
  rw [card_union_of_disjoint (disj im jm ji.symm)] at two
  have bi := bound i im
  have bj := bound j jm
  have ij := cross im jm ji.symm
  have all (k) (km : k∈M) : k=i ∨ k=j := by
    by_contra! ne
    have unionDis := Finset.disjoint_union_left.mpr ⟨disj im km ne.1.symm,disj jm km ne.2.symm⟩
    have cnt := card_le_card (union_subset (union_subset (inside i) (inside j)) (inside k))
    rw [card_union_of_disjoint unionDis,card_union_of_disjoint (disj im jm ji.symm)] at cnt
    have ki := cross km im ne.1
    have kj := cross km jm ne.2
    have bk := bound k km
    have := pos k km
    have := pos i im
    have := pos j jm
    omega
  have ti := tax (sa i im) (ss i im) (mb im) (out i im) (R j) (by
    intro k km ne; obtain e|rfl := all k km; exact (ne e).elim; exact Subset.rfl)
  have tj := tax (sa j jm) (ss j jm) (mb jm) (out j jm) (R i) (by
    intro k km ne; obtain rfl|e := all k km; exact Subset.rfl; exact (ne e).elim)
  have := pos i im
  have := pos j jm
  have di := long i im
  have dj := long j jm
  by_cases pi : pred i <;> by_cases pj : pred j <;>
    simp only [pi,pj,ite_true,ite_false,Nat.add_zero] at ti tj <;>
    first
    | exact (by omega)
    | exact (by have h := di pi; omega)
    | exact (by have h := dj pj; omega)
    | exact (by have h := di pi; have k := dj pj; omega)

/-- Compatibility interface with the two-step bound on every first-layer row. -/
theorem two_sinks_false {D V A B T q} (hq : 4≤q) (hf : QFree D V q)
    (av : A⊆V) (bv : B⊆V) (na : A.card≤q)
    {s₀ t₀ : ℕ} (sA : s₀∈A) (tA : t₀∈A) (st : s₀≠t₀)
    (sSink : Sink D A s₀) (tSink : Sink D A t₀)
    (omitOne : ∀s∈A,Sink D A s → ∃b∈B,outN D V s=B.erase b)
    (row : ∀ b∈B, outN D V b⊆(A∪B)∪T)
    (ballSize : ∀s∈A,B.card+T.card+2≤(ball D V s 2).card) : False :=
  two_sinks_false_of_sink_ball_size hq hf av bv na sA tA st sSink tSink omitOne row
    (fun s hs _ => ballSize s hs)

#print axioms two_sinks_false_of_sink_ball_size
#print axioms two_sinks_false
end LeanCH.BR.SingleOmissionPacking

namespace LeanCH.BR.SingleOmissionPacking
open Finset BRq2 BRq3 BR45

/-- At a unique first-layer sink the next three-step ball must grow. -/
theorem unique_successor {D : CH.Digraph} {V : Finset ℕ} {u a r q t : ℕ}
    (hr : 4≤r) (rq : r≤q) (ht : t<r)
    (hf : QFree D V q) (ho : OutEq r D V) (hu : u∈V)
    (b2u : (ball D V u 2).card=2*r+2) (b2a : 2*r+2≤(ball D V a 2).card)
    (b3u : (ball D V u 3).card=2*r+2+t)
    (ha : a∈outN D V u) (sink : Sink D (outN D V u) a)
    (unique : ∀x∈outN D V u, Sink D (outN D V u) x → x=a) :
    q=r ∧ t+1=r ∧ (ball D V a 2).card=2*r+2 ∧
    (ball D V a 2).card+(ball D V u 4 \ ball D V u 3).card+1≤(ball D V a 3).card := by
  classical
  let A := outN D V u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  let W := ball D V u 4 \ ball D V u 3
  let B' := outN D V a
  have aV : a ∈ V := (mem_outN.mp ha).1
  have A1 : A ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).2 (Or.inr hx)
  have AV : A ⊆ V := A1.trans ball_subset
  have BV : B ⊆ V := fun _ hx => ball_subset (mem_sdiff.mp hx).1
  have TV : T ⊆ V := fun _ hx => ball_subset (mem_sdiff.mp hx).1
  have WV : W ⊆ V := fun _ hx => ball_subset (mem_sdiff.mp hx).1
  have A7 : A.card = r := ho u hu
  have ba : B'.card = r := ho a aV
  have B8 : B.card = r+1 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    change B.card+(ball D V u 1).card=(ball D V u 2).card at h
    rw [card_B1 (hf.mono_bound (by omega : 4≤q)) hu, ho u hu, b2u] at h
    omega
  have T6 : T.card = t := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+(ball D V u 2).card=(ball D V u 3).card at h
    rw [b2u,b3u] at h
    omega
  have B'B : B' ⊆ B := by
    intro y hy
    obtain ⟨hyV,hay⟩ := mem_outN.mp hy
    refine mem_sdiff.mpr ⟨ball_step (A1 ha) hyV hay,?_⟩
    intro hy1
    rcases (mem_ball_one hu).1 hy1 with rfl | hyA
    · exact no_back_arc hf hu (A1 ha) (by omega : 1+1≤q) hay
    · exact sink y hyA hay
  have forward (b) (hb : b∈B') (y) (hy : y∈V) (hby : D b y=true) :
      y∈B∪T ∨ y∈A := by
    have b2u := (mem_sdiff.mp (B'B hb)).1
    have y3 := ball_step b2u hy hby
    by_cases y2 : y∈ball D V u 2
    · by_cases y1 : y∈ball D V u 1
      · rcases (mem_ball_one hu).1 y1 with rfl | hyA
        · exact (no_back_arc hf hu b2u (by omega : 2+1≤q) hby).elim
        · exact Or.inr hyA
      · exact Or.inl (mem_union_left _ (mem_sdiff.mpr ⟨y2,y1⟩))
    · exact Or.inl (mem_union_right _ (mem_sdiff.mpr ⟨y3,y2⟩))
  have long (v) (hv : v∈A) (b) (hb : b∈B') (hbv : D b v=true)
      (m) (walk : Walk D A v a m) : q≤m+1 := by
    by_contra! short
    exact hf v (m+1+1) (by omega) (by omega)
      (((walk.mono AV).snoc (BV (B'B hb)) (mem_outN.mp hb).2).snoc (AV hv) hbv)
  have ex : ∃ v∈A, ∃ b∈B', D b v=true := by
    by_contra no
    have sub : ball D V a 2 ⊆ insert a (B ∪ T) := by
      intro y hy
      by_cases eq : y=a
      · exact mem_insert.mpr (Or.inl eq)
      obtain ⟨b,hb,hby⟩ := exists_pred aV hy eq
      rcases (mem_ball_one aV).mp hb with rfl | hb'
      · exact mem_insert_of_mem (mem_union_left _ (B'B (mem_outN.mpr ⟨ball_subset hy,hby⟩)))
      rcases forward b hb' y (ball_subset hy) hby with hyBT | hyA
      · exact mem_insert_of_mem hyBT
      · exact (no ⟨y,hyA,b,hb',hby⟩).elim
    have h := (card_le_card sub).trans ((card_insert_le _ _).trans (Nat.succ_le_succ (card_union_le _ _)))
    rw [B8,T6] at h
    omega
  obtain ⟨v,hv,b,hb,hbv⟩ := ex
  obtain ⟨p⟩ := exists_shortest_sink_path (hf.mono_set AV) (by omega) hv
  have last : p.vertex p.len = a := unique _ (p.mem _ le_rfl) p.sink
  have len : p.len+1 = q := by
    have walk := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start,last,Nat.sub_zero] at walk
    have h := long v hv b hb hbv p.len walk
    have hb := p.bounded
    omega
  have inj := p.injective (hf.mono_set AV) (by omega)
  have full : (range (p.len+1)).image p.vertex = A := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact p.mem i (by have := mem_range.mp hi; omega)
    · rw [card_image_of_injOn inj,card_range]
      omega
  have allret (y) (hy : y∈A) (c) (hc : c∈B') (hcy : D c y=true) : y=v := by
    have hy' : y∈(range (p.len+1)).image p.vertex := full.symm ▸ hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy'
    have ile : i≤p.len := by have := mem_range.mp hi; omega
    have w := p.walk ile le_rfl
    rw [last] at w
    have h := long _ hy c hc hcy _ w
    have iz : i=0 := by omega
    rw [iz,p.start]
  let C := insert a (insert v (B∪T))
  have sub : ball D V a 2 ⊆ C := by
    intro y hy
    by_cases eq : y=a
    · exact mem_insert.mpr (Or.inl eq)
    obtain ⟨c,hc,hcy⟩ := exists_pred aV hy eq
    rcases (mem_ball_one aV).mp hc with rfl | hc'
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (B'B (mem_outN.mpr ⟨ball_subset hy,hcy⟩))))
    rcases forward c hc' y (ball_subset hy) hcy with hyBT | hyA
    · exact mem_insert_of_mem (mem_insert_of_mem hyBT)
    · exact mem_insert_of_mem (mem_insert.mpr (Or.inl (allret y hyA c hc' hcy)))
  have upper := (card_insert_le a (insert v (B∪T))).trans (Nat.succ_le_succ
    ((card_insert_le v (B∪T)).trans (Nat.succ_le_succ (card_union_le B T))))
  change C.card≤B.card+T.card+1+1 at upper
  have sizecap := card_le_card sub
  have eqC : ball D V a 2=C := eq_of_subset_of_card_le sub (by omega)
  have tf : T ⊆ ball D V a 2 := by
    rw [eqC]
    exact fun y hy => mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ hy))
  have w3 : W ⊆ ball D V a 3 := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := ball_succ_pred hu (mem_sdiff.mp hy).1 (mem_sdiff.mp hy).2
    have hxT : x∈T := mem_sdiff.mpr ⟨hx,fun x2 => (mem_sdiff.mp hy).2 (ball_step x2 (WV hy) hxy)⟩
    exact ball_step (tf hxT) (WV hy) hxy
  let y := p.vertex 1
  have yA : y∈A := p.mem 1 (by omega)
  have yneV : y≠v := fun eq => by
    have e : p.vertex 1 = p.vertex 0 := eq.trans p.start.symm
    have z := inj (by simp; omega : 1 ∈ range (p.len+1)) (by simp : 0 ∈ range (p.len+1)) e
    omega
  have yneA : y≠a := fun eq => by
    have e : p.vertex 1 = p.vertex p.len := eq.trans last.symm
    have z := inj (by simp; omega : 1 ∈ range (p.len+1)) (by simp : p.len ∈ range (p.len+1)) e
    omega
  have y3 : y∈ball D V a 3 := by
    have hv2 : v ∈ ball D V a 2 := by
      rw [eqC]
      exact mem_insert_of_mem (mem_insert_self _ _)
    exact ball_step hv2 (AV yA) (by simpa [y,p.start] using p.edge 0 (by omega))
  have ynot : y∉ C ∪ W := by
    have y1 := A1 yA
    have y2 := ball_mono_radius (by decide : 1≤2) y1
    have y3u := ball_mono_radius (by decide : 2≤3) y2
    simp only [C,mem_union,mem_insert]
    rintro ((e|e|hB|hT)|hW)
    · exact yneA e
    · exact yneV e
    · exact (mem_sdiff.mp hB).2 y1
    · exact (mem_sdiff.mp hT).2 y2
    · exact (mem_sdiff.mp hW).2 y3u
  have C3u : C ⊆ ball D V u 3 := by
    intro x hx
    simp only [C,mem_insert,mem_union] at hx
    rcases hx with rfl|rfl|hx|hx
    · exact ball_mono_radius (by decide : 1≤3) (A1 ha)
    · exact ball_mono_radius (by decide : 1≤3) (A1 hv)
    · exact ball_mono_radius (by decide : 2≤3) (mem_sdiff.mp hx).1
    · exact (mem_sdiff.mp hx).1
  have disj : Disjoint C W := disjoint_left.mpr fun x hx hw => (mem_sdiff.mp hw).2 (C3u hx)
  have big : insert y (C∪W) ⊆ ball D V a 3 := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact y3
    rcases mem_union.mp hx with hx | hx
    · exact ball_mono_radius (by decide : 2≤3) (eqC.symm ▸ hx)
    · exact w3 hx
  have cnt := card_le_card big
  rw [card_insert_of_notMem ynot,card_union_of_disjoint disj,←eqC] at cnt
  change (ball D V a 2).card+W.card+1≤(ball D V a 3).card at cnt
  have l := p.bounded
  exact ⟨by omega,by omega,by omega,cnt⟩
#print axioms unique_successor
end LeanCH.BR.SingleOmissionPacking



namespace LeanCH.BR.SingleOmissionPacking
open Finset BRq2 BRq3 BR45
/-- Move to the actual out-neighbour forced by the small third layer. -/
theorem recursive_successor {q r t D V} (hr : 4≤r) (rq : r≤q) (ht : t<r)
    (free : QFree D V q) (ho : OutEq r D V) {u : ℕ} (hu : u∈V)
    (b2u : (ball D V u 2).card=2*r+2)
    (b2 : ∀v∈outN D V u,2*r+2≤(ball D V v 2).card)
    (b3u : (ball D V u 3).card=2*r+2+t) :
    q=r ∧ t+1=r ∧ ∃a∈outN D V u, Sink D (outN D V u) a ∧
      (∀z∈outN D V u, Sink D (outN D V u) z → z=a) ∧
      (ball D V a 2).card=2*r+2 ∧
      (ball D V a 2).card+(ball D V u 4 \ ball D V u 3).card+1≤(ball D V a 3).card := by
  classical
  have hf := free

  let A := outN D V u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  have av : A⊆V := outN_subset
  have bv : B⊆V := fun _ mx=>ball_subset (mem_sdiff.mp mx).1
  have na : A.card=r := ho _ hu
  have nb : B.card=r+1 := by
    have e := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    change B.card+_= _ at e
    rw [card_B1 (hf.mono_bound (by omega : 4≤q)) hu,ho u hu,b2u] at e
    omega
  have nt : T.card=t := by
    have e := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+_= _ at e
    rw [b2u,b3u] at e
    omega
  have one (s) (sa : s∈A) (ss : Sink D A s) : ∃b∈B,outN D V s=B.erase b := by
    have s1 := (mem_ball_one hu).2 (Or.inr sa)
    have inc : outN D V s⊆B := by
      intro z zm
      obtain ⟨zv,sz⟩ := mem_outN.mp zm
      refine mem_sdiff.mpr ⟨ball_step s1 zv sz,?_⟩
      intro z1
      rcases (mem_ball_one hu).1 z1 with rfl|za
      · exact no_back_arc hf hu s1 (by omega : 1+1≤q) sz
      · exact ss z za sz
    have size := ho s (av sa)
    have c := card_sdiff_add_card_eq_card inc
    obtain ⟨b,bm⟩ := card_pos.mp (show 0<(B\outN D V s).card by omega)
    obtain ⟨bb,bn⟩ := mem_sdiff.mp bm
    refine ⟨b,bb,eq_of_subset_of_card_le (fun z hz=>mem_erase.mpr ⟨fun e=>bn (e ▸ hz),inc hz⟩) ?_⟩
    rw [card_erase_of_mem bb,nb,size]; omega
  have row (b) (bm : b∈B) : outN D V b⊆(A∪B)∪T := by
    intro z zm
    obtain ⟨zv,bz⟩ := mem_outN.mp zm
    have b2u := (mem_sdiff.mp bm).1
    have z3 := ball_step b2u zv bz
    by_cases z2 : z∈ball D V u 2
    · apply mem_union_left
      by_cases z1 : z∈ball D V u 1
      · rcases (mem_ball_one hu).1 z1 with rfl|za
        · exact (no_back_arc hf hu b2u (by omega : 2+1≤q) bz).elim
        · exact mem_union_left _ za
      · exact mem_union_right _ (mem_sdiff.mpr ⟨z2,z1⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨z3,z2⟩)
  obtain ⟨s,sa,ss⟩ := exists_sink (T:=A) (hf.mono_set av) (card_pos.mp (by omega)) (na.le.trans rq)
  by_cases unique : ∀t∈A, Sink D A t → t=s
  · obtain ⟨qr,rt,aa,inc⟩ := unique_successor hr rq ht free ho hu b2u (b2 s sa) b3u sa ss unique
    exact ⟨qr,rt,s,sa,ss,unique,aa,inc⟩
  · push Not at unique
    obtain ⟨t,ta,ts,ts'⟩ := unique
    exfalso
    exact two_sinks_false (hr.trans rq) hf av bv (na.le.trans rq) sa ta ts'.symm ss ts one row
      (fun v vm=>by have l := b2 v vm; rw [nb,nt]; omega)


#print axioms recursive_successor
end LeanCH.BR.SingleOmissionPacking
