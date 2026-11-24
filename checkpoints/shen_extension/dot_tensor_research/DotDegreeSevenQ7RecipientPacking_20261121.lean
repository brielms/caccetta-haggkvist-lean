import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileUnique_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7PrefixTwinBudget_20261121

namespace LeanCH.BR.DotDegreeSevenQ7.Packing
open Finset BRq2 BRq3 BR45
abbrev Sink (D : CH.Digraph) (A : Finset ℕ) (s : ℕ) := ∀ z∈A, D s z≠true

/-- With two sinks a path on seven acyclic labels has at most five edges.
The first six tails would all be different nonsinks. -/
private theorem short {D A} (f : QFree D A 7) (n : A.card=7)
    {s t} (sA : s∈A) (tA : t∈A) (st : s≠t) (ss : Sink D A s) (ts : Sink D A t)
    {v w k} (vA : v∈A) (p : Walk D A v w k) : k≤5 := by
  classical
  by_contra! big
  obtain ⟨g,g0,_,ed⟩ := p.toFun
  have inj : (range 6 : Set ℕ).InjOn g := by
    intro i hi j hj eq
    change i∈range 6 at hi
    change j∈range 6 at hj
    simp only [mem_range] at hi hj
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with lt|gt
    · have path := walk_between ed lt.le (by omega : j≤k)
      rw [←eq] at path
      exact f _ _ (by omega) (by omega) path
    · have path := walk_between ed gt.le (by omega : i≤k)
      rw [eq] at path
      exact f _ _ (by omega) (by omega) path
  have sub : (range 6).image g ⊆ (A.erase s).erase t := by
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
    card_erase_of_mem sA,n] at h
  omega

private noncomputable def basin (D : CH.Digraph) (A : Finset ℕ) (b : ℕ) : Finset ℕ := by
  classical
  exact A.filter (fun z=>∃r∈outN D A b, ∃ k, Walk D A r z k)

private theorem packed_path {D A b} (f : QFree D A 7) (n : A.card=7)
    (live : (outN D A b).Nonempty) :
    ∃ r∈outN D A b, ∃ s∈A, Sink D A s ∧ ∃m, Walk D A r s m ∧
      (outN D A b).card+m≤(basin D A b).card := by
  classical
  let P (k : ℕ) := ∃r∈outN D A b, ∃s∈A, Sink D A s ∧ Walk D A r s k
  obtain ⟨r,rr⟩ := live
  obtain ⟨s,sa,ss,k,kl,walk⟩ := reach_sink_of_card f n.le (mem_outN.mp rr).1
  have ex : ∃k,P k := ⟨k,r,rr,s,sa,ss,walk⟩
  let m := Nat.find ex
  have ml : m<7 := (Nat.find_min' ex (show P k from ⟨r,rr,s,sa,ss,walk⟩)).trans_lt (by omega)
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


/-- A seven-label first layer with two sinks cannot have the saturated
second-ball sizes at its sinks. Only the first three native layers enter. -/
theorem two_sinks_false {D V A B T} (hf : QFree D V 7)
    (av : A⊆V) (bv : B⊆V) (na : A.card=7) (nb : B.card=8) (nt : T.card=6)
    {s₀ t₀ : ℕ} (sA : s₀∈A) (tA : t₀∈A) (st : s₀≠t₀)
    (sSink : Sink D A s₀) (tSink : Sink D A t₀)
    (omitOne : ∀s∈A,Sink D A s → ∃b∈B,outN D V s=B.erase b)
    (row : ∀ b∈B, outN D V b⊆(A∪B)∪T)
    (ballSize : ∀s∈A,16≤(ball D V s 2).card) : False := by
  classical
  let R := fun b=>outN D A b
  let M := B.filter (fun b=>(R b).Nonempty)
  let f := hf.mono_set av
  have mb : M⊆B := filter_subset _ _
  have live (i) (im : i∈M) : (R i).Nonempty := (mem_filter.mp im).2
  have sr (v) (hv : v∈A) {w k} (p : Walk D A v w k) : k≤5 :=
    short f na sA tA st sSink tSink hv p
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
    obtain ⟨s,sa,ss,_,_,tail⟩ := reach_sink_of_card f na.le za
    exact ne (color (mb im) (mb jm) (exc (mb im) rm (p.append tail) sa ss)
      (exc (mb jm) am (w.append tail) sa ss)))
  have spec (i) (im : i∈M) : ∃ r∈R i, ∃ s∈A, Sink D A s ∧ ∃m,
      Walk D A r s m ∧ (R i).card+m≤(basin D A i).card :=
    packed_path f na (live i im)
  choose r rr s sa ss m p bound using spec
  have out (i) (im : i∈M) := exc (mb im) (rr i im) (p i im) (sa i im) (ss i im)
  have cross {i j} (im : i∈M) (jm : j∈M) (ij : i≠j) : 4≤m i im+m j jm := by
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
  have long (i) (im : i∈M) (par : pred i) : 5≤m i im := by
    obtain ⟨y,yb,yi⟩ := par
    have yi' : y≠i := by rintro rfl; exact loopfree hf (by decide) (bv yb) yi
    have sy : y∈outN D V (s i im) := out i im ▸ mem_erase.mpr ⟨yi',yb⟩
    have path := (((p i im).mono av).snoc (bv yb) (mem_outN.mp sy).2).snoc (bv (mb im)) yi
    by_contra! sm
    exact hf _ _ (by omega) (by omega)
      (path.snoc (av (mem_outN.mp (rr i im)).1) (mem_outN.mp (rr i im)).2)
  have tax {s i} (as : s∈A) (ib : i∈B) (eq : outN D V s=B.erase i)
      (E : Finset ℕ) (cover : ∀j∈M,j≠i→R j⊆E) :
      2≤E.card+(if pred i then 1 else 0) := by
    let X := B.erase i
    let Q : Finset ℕ := if pred i then {i} else ∅
    have qq : Q.card=(if pred i then 1 else 0) := by dsimp [Q]; split <;> simp
    have cntX : X.card=7 := by simp [X,card_erase_of_mem ib,nb]
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
    have b := ballSize s as
    omega
  have many (i) (ib : i∈B) (x) (xa : x∈A) (ex : outN D V x=B.erase i) : ∃j∈M,j≠i := by
    by_contra! all
    have u := tax xa ib ex ∅ (fun j jm ne => (ne (all j jm)).elim)
    simp only [card_empty,zero_add] at u
    split at u <;> omega
  obtain ⟨a,ab,eq⟩ := omitOne s₀ sA sSink
  obtain ⟨i,im,_⟩ := many a ab s₀ sA eq
  obtain ⟨j,jm,ji⟩ := many i (mb im) _ (sa i im) (out i im)
  have pos (v) (vm : v∈M) := card_pos.mpr (live v vm)
  have inside (v : ℕ) : basin D A v ⊆ A := filter_subset _ _
  have two := card_le_card (union_subset (inside i) (inside j))
  rw [card_union_of_disjoint (disj im jm ji.symm),na] at two
  have bi := bound i im
  have bj := bound j jm
  have ij := cross im jm ji.symm
  have all (k) (km : k∈M) : k=i ∨ k=j := by
    by_contra! ne
    have unionDis := Finset.disjoint_union_left.mpr ⟨disj im km ne.1.symm,disj jm km ne.2.symm⟩
    have cnt := card_le_card (union_subset (union_subset (inside i) (inside j)) (inside k))
    rw [card_union_of_disjoint unionDis,card_union_of_disjoint (disj im jm ji.symm),na] at cnt
    have ki := cross km im ne.1
    have kj := cross km jm ne.2
    have bk := bound k km
    have := pos k km
    have := pos i im
    have := pos j jm
    omega
  have ti := tax (sa i im) (mb im) (out i im) (R j) (by
    intro k km ne; obtain e|rfl := all k km; exact (ne e).elim; exact Subset.rfl)
  have tj := tax (sa j jm) (mb jm) (out j jm) (R i) (by
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

#print axioms two_sinks_false
end LeanCH.BR.DotDegreeSevenQ7.Packing
