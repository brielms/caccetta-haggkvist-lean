import checkpoints.shen_extension.TallBankTransfer

namespace LeanCH.BR.TallBankTransfer

open Finset BRq2 BRq3

/-- When the two actual sinks exhaust a first-layer bank's second layer,
their common second layer must fit entirely in the original third layer.
This excludes a duplicate charge under the strict layer-size inequality. -/
theorem common_sink_layer_fits_third {D : CH.Digraph} {V : Finset ℕ} {q u a b : ℕ}
    (free : QFree D V q) (time : 3 ≤ q) (uv : u ∈ V)
    (size : (outN D V u).card ≤ q)
    (ha : a ∈ outN D V u) (hb : b ∈ outN D V u) (ne : a ≠ b)
    (sa : ∀ z ∈ outN D V u, D a z ≠ true)
    (sb : ∀ z ∈ outN D V u, D b z ≠ true)
    (all : ∀ s ∈ outN D V u, (∀ z ∈ outN D V u, D s z ≠ true) → s = a ∨ s = b)
    (rows : outN D V a ∪ outN D V b = ball D V u 2 \ ball D V u 1)
    (same : ball D V a 2 \ ball D V a 1 = ball D V b 2 \ ball D V b 1) :
    ball D V a 2 \ ball D V a 1 ⊆ ball D V u 3 \ ball D V u 2 := by
  let X := outN D V u
  have xv : X ⊆ V := outN_subset
  have av := xv ha
  have bv := xv hb
  intro z hz
  have za : z ∈ ball D V a 2 := (mem_sdiff.mp hz).1
  have zb : z ∈ ball D V b 2 := (mem_sdiff.mp (same ▸ hz)).1
  have noX : z ∉ X := by
    intro zx
    obtain ⟨s, hs, stop, i, hi, path⟩ :=
      sink_path_le_of_two_sinks (free.mono_set xv) size ha hb ne sa sb zx
    have entry (j) (hj : j ∈ V) (reach : z ∈ ball D V j 2)
        (off : z ∉ ball D V j 1) (same : s = j) : False := by
      obtain ⟨_,n,ni,walk⟩ := mem_ball.mp reach
      have npos : 0 < n := by
        by_contra! hn
        exact off (mem_ball_of_walk walk (by omega) (xv zx))
      have ret : Walk D V z j i := same ▸ path.mono xv
      exact free j _ (by omega) (by change X.card ≤ q at size; omega) (walk.append ret)
    rcases all s hs stop with ea | eb
    · exact entry a av za (mem_sdiff.mp hz).2 ea
    · exact entry b bv zb (mem_sdiff.mp (same ▸ hz)).2 eb
  have noY : z ∉ ball D V u 2 \ ball D V u 1 := by
    intro zy
    rcases mem_union.mp (rows.symm ▸ zy) with zA | zB
    · exact (mem_sdiff.mp hz).2 ((mem_ball_one av).mpr (Or.inr zA))
    · exact (mem_sdiff.mp (same ▸ hz)).2 ((mem_ball_one bv).mpr (Or.inr zB))
  have nu : z ≠ u := by
    intro zu
    exact no_back_arc free av (zu ▸ za) (by omega : 2 + 1 ≤ q) (mem_outN.mp ha).2
  refine mem_sdiff.mpr ⟨ball_trans (ball_of_adj av (mem_outN.mp ha).2) za, ?_⟩
  intro z2
  by_cases z1 : z ∈ ball D V u 1
  · rcases (mem_ball_one uv).mp z1 with rfl | hit
    · exact nu rfl
    · exact noX hit
  · exact noY (mem_sdiff.mpr ⟨z2,z1⟩)

/-- A return between equal banks at diagonal cutoff fixes both endpoints
of every back arc. The receiving path uses all first-bank labels, and
the sole returning tail has no parent in the second bank. -/
theorem equal_bank_return_shape {D : CH.Digraph} {V X Y : Finset ℕ} {q r x b : ℕ}
    (free : QFree D V q) (diag : r ≤ q) (room : 3 ≤ r)
    (xv : X ⊆ V) (yv : Y ⊆ V) (sizeX : X.card = r) (sizeY : Y.card = r)
    (degree : ∀ v ∈ X, r ≤ (outN D (X ∪ Y) v).card)
    (complete : ∀ s ∈ X, (∀ z ∈ X, D s z ≠ true) → ∀ d ∈ Y, D s d = true)
    (hx : x ∈ X) (hb : b ∈ Y) (back : D b x = true) :
    ∃ path : ShortestSinkPath D X x,
      path.len + 1 = q ∧ (range (path.len + 1)).image path.vertex = X ∧
      (∀ y ∈ Y, ∀ v ∈ X, D y v = true → y = b ∧ v = x) ∧
      ∀ y ∈ Y, D y b ≠ true := by
  classical
  obtain ⟨path⟩ := exists_shortest_sink_path (free.mono_set xv) (by omega) hx
  have minLength {y v : ℕ} (hy : y ∈ Y) (hv : v ∈ X) (edge : D y v = true)
      {m : ℕ} {s : ℕ} (hs : s ∈ X) (stop : ∀ z ∈ X, D s z ≠ true)
      (walk : Walk D X v s m) : q ≤ m + 1 := by
    by_contra! h
    exact free v _ (by omega) (by omega)
      (((walk.mono xv).snoc (yv hy) (complete s hs stop y hy)).snoc (xv hv) edge)
  have longest : path.len + 1 = q := by
    have fullWalk := path.walk (Nat.zero_le _) le_rfl
    rw [path.start,Nat.sub_zero] at fullWalk
    have lower := minLength hb hx back (path.mem _ le_rfl) path.sink fullWalk
    have upper := path.bounded
    omega
  have full : (range (path.len + 1)).image path.vertex = X := by
    apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
      exact path.mem i (by have := mem_range.mp hi; omega)
    · rw [card_image_of_injOn (path.injective (free.mono_set xv) (by omega)),card_range,longest,sizeX]
      exact diag
  have atMost : (outN D X x).card ≤ 1 := by
    have cap : outN D X x ⊆ {path.vertex 1} := by
      intro v hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp (full.symm ▸ (mem_outN.mp hv).1)
      have arc : D (path.vertex 0) (path.vertex i) = true := by
        simpa only [path.start] using (mem_outN.mp hv).2
      have iBound : i ≤ path.len := by have := mem_range.mp hi; omega
      have h := path.no_chord (free.mono_set xv) (by omega : X.card ≤ q)
        (Nat.zero_le _) iBound arc
      exact mem_singleton.mpr (congrArg path.vertex h)
    exact (card_le_card cap).trans_eq (card_singleton _)
  have excluded : b ∉ outN D Y x := fun arc =>
    digonfree free (by omega) (xv hx) (yv hb) (mem_outN.mp arc).2 back
  have inY : outN D Y x = Y.erase b := by
    apply eq_of_subset_of_card_le
    · intro y hy
      exact mem_erase.mpr ⟨fun same => excluded (same ▸ hy),outN_subset hy⟩
    · have inc : outN D (X ∪ Y) x ⊆ outN D X x ∪ outN D Y x := by
        intro y hy
        obtain ⟨hm,he⟩ := mem_outN.mp hy
        rcases mem_union.mp hm with hx | hy
        · exact mem_union_left _ (mem_outN.mpr ⟨hx,he⟩)
        · exact mem_union_right _ (mem_outN.mpr ⟨hy,he⟩)
      have h := (card_le_card inc).trans (card_union_le _ _)
      have d := degree x hx
      rw [card_erase_of_mem hb,sizeY]
      omega
  refine ⟨path,longest,full,?_,?_⟩
  · intro y hy v hv entry
    have eq : v = x := by
      obtain ⟨i,hi,rfl⟩ := mem_image.mp (full.symm ▸ hv)
      have h := minLength hy hv entry (path.mem _ le_rfl) path.sink
        (path.walk (by have := mem_range.mp hi; omega) le_rfl)
      have i0 : i = 0 := by omega
      rw [i0,path.start]
    refine ⟨?_,eq⟩
    by_contra diff
    have xy := mem_outN.mp (inY.symm ▸ mem_erase.mpr ⟨diff,hy⟩)
    exact digonfree free (by omega) (xv hx) (yv hy) xy.2 (eq ▸ entry)
  · intro y hy yb
    have off : y ≠ b := fun e => loopfree free (by omega) (yv hb) (e ▸ yb)
    have xy := mem_outN.mp (inY.symm ▸ mem_erase.mpr ⟨off,hy⟩)
    exact free x 3 (by decide) (by omega)
      (.step (yv hy) xy.2 (.step (yv hb) yb (.step (xv hx) back (.refl x))))

/-- A weak two-ball on the diagonal has equally sized first and second
layers. Its first-layer sinks cover every actual second-layer label. Any
return from the second layer to the first has a unique physical entrance. -/
theorem weak_equal_shell {D : CH.Digraph} {V : Finset ℕ} {q r a : ℕ}
    (free : QFree D V q) (diag : r ≤ q) (room : 3 ≤ r)
    (reg : OutEq r D V) (av : a ∈ V) (weak : (ball D V a 2).card = 2 * r + 1) :
    let P := outN D V a
    let Q := ball D V a 2 \ ball D V a 1
    Q.card = r ∧
    (∀ s ∈ P, (∀ z ∈ P, D s z ≠ true) → outN D V s = Q) ∧
    ((∀ y ∈ Q, ∀ x ∈ P, D y x ≠ true) ∨
      ∃ x ∈ P, ∃ b ∈ Q, D b x = true ∧
        ∃ path : ShortestSinkPath D P x,
          path.len + 1 = q ∧ (range (path.len + 1)).image path.vertex = P ∧
          (∀ y ∈ Q, ∀ v ∈ P, D y v = true → y = b ∧ v = x) ∧
          ∀ y ∈ Q, D y b ≠ true) := by
  classical
  let P := outN D V a
  let Q := ball D V a 2 \ ball D V a 1
  have pv : P ⊆ V := outN_subset
  have qv : Q ⊆ V := sdiff_subset.trans ball_subset
  have pa (x) (hx : x ∈ P) : x ∈ ball D V a 1 := (mem_ball_one av).mpr (Or.inr hx)
  have pc : P.card = r := reg a av
  have b1 : (ball D V a 1).card = r + 1 := by
    have same : ball D V a 1 = insert a P := by
      ext z
      exact (mem_ball_one av).trans mem_insert.symm
    rw [same,card_insert_of_notMem,pc]
    exact fun h => loopfree free (by omega) av (mem_outN.mp h).2
  have qc : Q.card = r := by
    have capacity := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=a) (by decide : 1 ≤ 2))
    change Q.card + (ball D V a 1).card = (ball D V a 2).card at capacity
    omega
  have keep {x : ℕ} (hx : x ∈ P) : outN D V x ⊆ P ∪ Q := by
    intro z hz
    obtain ⟨zv, xz⟩ := mem_outN.mp hz
    have z2 := ball_step (pa x hx) zv xz
    by_cases z1 : z ∈ ball D V a 1
    · rcases (mem_ball_one av).mp z1 with rfl | zp
      · exact (no_back_arc free av (pa x hx) (by omega : 1 + 1 ≤ q) xz).elim
      · exact mem_union_left _ zp
    · exact mem_union_right _ (mem_sdiff.mpr ⟨z2,z1⟩)
  have full (s) (hs : s ∈ P) (stop : ∀ z ∈ P, D s z ≠ true) : outN D V s = Q := by
    apply eq_of_subset_of_card_le
    · intro z hz
      rcases mem_union.mp (keep hs hz) with inP | inQ
      · exact (stop z inP (mem_outN.mp hz).2).elim
      · exact inQ
    · rw [qc,reg _ (pv hs)]
  refine ⟨qc,full,?_⟩
  by_cases h : ∀ y ∈ Q, ∀ x ∈ P, D y x ≠ true
  · exact Or.inl h
  · push Not at h
    obtain ⟨b,hb,x,hx,arc⟩ := h
    have maintained (v) (hv : v ∈ P) : r ≤ (outN D (P ∪ Q) v).card := by
      apply (reg _ (pv hv)).ge.trans
      apply card_le_card
      exact fun _ h => mem_outN.mpr ⟨keep hv h,(mem_outN.mp h).2⟩
    exact Or.inr ⟨x,hx,b,hb,arc,
      equal_bank_return_shape free diag room pv qv pc qc maintained
        (fun s hs stop d hd =>
          (mem_outN.mp ((full s hs stop).symm ▸ (show d ∈ Q from hd))).2) hx hb arc⟩

/-- At a weak sink of a tight parent, each second-ball return to the
parent's first layer replaces one actual omitted label in the union of
the parent's third layer and the sink's sole missing second-layer head. -/
theorem weak_sink_entry_ledger {D : CH.Digraph} {V : Finset ℕ} {q r u a : ℕ}
    (free : QFree D V q) (diag : r ≤ q) (room : 3 ≤ r)
    (reg : OutEq r D V) (uv : u ∈ V) (ha : a ∈ outN D V u)
    (stop : ∀ x ∈ outN D V u, D a x ≠ true)
    (two : (ball D V u 2 \ ball D V u 1).card = r + 1)
    (three : (ball D V u 3 \ ball D V u 2).card + 1 = r)
    (weak : (ball D V a 2).card = 2 * r + 1) :
    let X := outN D V u
    let Y := ball D V u 2 \ ball D V u 1
    let Z := ball D V u 3 \ ball D V u 2
    let Q := ball D V a 2 \ ball D V a 1
    ∃ b ∈ Y, outN D V a = Y.erase b ∧ Q ⊆ X ∪ insert b Z ∧
      (Q ∩ X).card = ((insert b Z) \ Q).card := by
  classical
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let Q := ball D V a 2 \ ball D V a 1
  obtain ⟨av,ua⟩ := mem_outN.mp ha
  obtain ⟨b,by_,row⟩ := sink_row_omission free (by omega) reg uv ha stop two
  have qc : Q.card = r := (weak_equal_shell free diag room reg av weak).1
  have bc : (insert b Z).card = r := by
    have off : b ∉ Z := fun h => (mem_sdiff.mp h).2 (mem_sdiff.mp by_).1
    rw [card_insert_of_notMem off]
    exact three
  have apart : Disjoint X (insert b Z) := disjoint_left.mpr (by
    intro c cx cz
    have c1 := (mem_ball_one uv).mpr (Or.inr cx)
    rcases mem_insert.mp cz with rfl | cZ
    · exact (mem_sdiff.mp by_).2 c1
    · exact (mem_sdiff.mp cZ).2 (ball_mono_radius (by decide : 1 ≤ 2) c1))
  have incl : Q ⊆ X ∪ insert b Z := by
    intro z hz
    have az2 := (mem_sdiff.mp hz).1
    have z3 := ball_trans (ball_of_adj av ua) az2
    by_cases z2 : z ∈ ball D V u 2
    · by_cases z1 : z ∈ ball D V u 1
      · rcases (mem_ball_one uv).mp z1 with rfl | zx
        · exact (no_back_arc free av az2 (by omega : 2 + 1 ≤ q) ua).elim
        · exact mem_union_left _ zx
      · have zy : z ∈ Y := mem_sdiff.mpr ⟨z2,z1⟩
        have zb : z = b := by
          by_contra reject
          exact (mem_sdiff.mp hz).2 ((mem_ball_one av).mpr
            (Or.inr (row.symm ▸ (mem_erase.mpr ⟨reject,zy⟩ : z ∈ Y.erase b))))
        exact mem_union_right _ (mem_insert.mpr (Or.inl zb))
    · exact mem_union_right _ (mem_insert_of_mem (mem_sdiff.mpr ⟨z3,z2⟩))
  have eq : Q \ X = Q ∩ insert b Z := by
    ext z
    constructor
    · intro h
      obtain ⟨zq,off⟩ := mem_sdiff.mp h
      exact mem_inter.mpr ⟨zq,(mem_union.mp (incl zq)).resolve_left off⟩
    · intro h
      exact mem_sdiff.mpr ⟨(mem_inter.mp h).1,
        fun zx => disjoint_left.mp apart zx (mem_inter.mp h).2⟩
  have slots := card_sdiff_add_card_inter Q X
  have holes := card_sdiff_add_card_inter (insert b Z) Q
  rw [eq,qc] at slots
  rw [inter_comm,bc] at holes
  have balance : (Q ∩ X).card = ((insert b Z) \ Q).card := by omega
  exact ⟨b,by_,row,incl,balance⟩

#print axioms common_sink_layer_fits_third
#print axioms equal_bank_return_shape
#print axioms weak_equal_shell
#print axioms weak_sink_entry_ledger
end LeanCH.BR.TallBankTransfer
