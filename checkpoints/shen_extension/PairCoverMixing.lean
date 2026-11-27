import checkpoints.shen_extension.LoneRow

/-! A regular digraph in which every two heads have a common predecessor
has a quantitative return bound. -/

namespace LeanCH.BR.PairCoverMixing
open Finset BRq2 BRq3 BR45

variable {ι : Type*} [Fintype ι]

private def step (A : ι → ι → ℝ) (f : ι → ℝ) (i : ι) := ∑ j, A i j * f j

private def iter (A : ι → ι → ℝ) (f : ι → ℝ) : ℕ → ι → ℝ
  | 0 => f
  | k+1 => step A (iter A f k)

private def gram (A : ι → ι → ℝ) (i j : ι) := ∑ w, A w i * A w j

private theorem energy {A : ι → ι → ℝ} {s : ℝ}
    (rows : ∀ i, ∑ j, A i j = s) (cols : ∀ j, ∑ i, A i j = s)
    (cover : ∀ i j, 1 ≤ gram A i j) (f : ι → ℝ) (zero : ∑ i, f i = 0) :
    ∑ i, (step A f i)^2 ≤ (s^2 - Fintype.card ι) * ∑ i, (f i)^2 := by
  classical
  let E i j := gram A i j - 1
  have symm (i j) : E i j = E j i := by simp [E, gram, mul_comm]
  have rowE (i) : ∑ j, E i j = s^2 - Fintype.card ι := by
    simp only [E, gram, sum_sub_distrib]
    rw [sum_comm]
    simp_rw [← mul_sum, rows, ← sum_mul, cols]
    simp [sq]
  have colE (j) : ∑ i, E i j = s^2 - Fintype.card ι := by
    simpa only [fun i => symm i j] using rowE j
  have double (w) :
      (step A f w)^2 = ∑ i, ∑ j, A w i * A w j * (f i * f j) := by
    simp only [step, sq, sum_mul, mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have swap (i) : ∑ w, ∑ j, A w i * A w j * (f i * f j) =
      ∑ j, gram A i j * (f i * f j) := by
    rw [sum_comm]
    simp only [gram, sum_mul]
  have first : ∑ w, (step A f w)^2 = ∑ i, ∑ j, gram A i j * (f i * f j) := by
    simp_rw [double]
    rw [sum_comm]
    simp_rw [swap]
  have replace (i j) : gram A i j * (f i * f j) =
      E i j * (f i * f j) + f i * f j := by unfold E; ring
  rw [first]
  simp only [replace, sum_add_distrib, ← mul_sum, zero, mul_zero, add_zero]
  have major (i j) : E i j * (f i * f j) ≤
      E i j * (f i)^2 / 2 + E i j * (f j)^2 / 2 := by
    have pos : 0 ≤ E i j := sub_nonneg.mpr (cover i j)
    nlinarith [mul_nonneg pos (sq_nonneg (f i - f j))]
  apply (sum_le_sum (fun i _ => sum_le_sum (fun j _ => major i j))).trans
  simp only [sum_add_distrib, ← sum_div]
  have diag (i) : ∑ j, E i j * (f i)^2 = (s^2 - Fintype.card ι) * (f i)^2 := by
    rw [← sum_mul, rowE]
  have other : (∑ i, ∑ j, E i j * (f j)^2) = (s^2 - Fintype.card ι) * ∑ j, (f j)^2 := by
    rw [sum_comm]; simp_rw [← sum_mul, colE]; rw [mul_sum]
  simp_rw [diag]
  rw [other, ← mul_sum]
  linarith

private theorem iter_energy {A : ι → ι → ℝ} {s : ℝ}
    (rows : ∀ i, ∑ j, A i j = s) (cols : ∀ j, ∑ i, A i j = s)
    (cover : ∀ i j, 1 ≤ gram A i j) (pos : 0 ≤ s^2 - Fintype.card ι)
    (f : ι → ℝ) (zero : ∑ i, f i = 0) (k : ℕ) :
    ∑ i, iter A f k i = 0 ∧
      ∑ i, (iter A f k i)^2 ≤ (s^2 - Fintype.card ι)^k * ∑ i, (f i)^2 := by
  induction k with
  | zero => simpa [iter] using And.intro zero (le_refl (∑ i, (f i)^2))
  | succ k ih =>
    constructor
    · simp only [iter, step]
      rw [sum_comm]; simp_rw [← sum_mul, cols]; rw [← mul_sum, ih.1, mul_zero]
    · exact (energy rows cols cover _ ih.1).trans
        (by simpa only [pow_succ', mul_assoc] using mul_le_mul_of_nonneg_left ih.2 pos)

/-- A common predecessor for every pair, together with regularity, bounds
the length of a missing return by the number of labels and the degree. -/
theorem regular_return_bound {D : CH.Digraph} {V : Finset ℕ} {q s k : ℕ}
    (live : V.Nonempty) (free : QFree D V q) (hk : 0 < k) (kq : k ≤ q)
    (rows : OutEq s D V) (cols : ∀ j ∈ V, (inN D V j).card = s)
    (pair : ∀ i ∈ V, ∀ j ∈ V, ∃ w ∈ V, D w i = true ∧ D w j = true)
    (de : (V.card : ℝ) ≤ (s : ℝ)^2) :
    ((s : ℝ)^k)^2 ≤ ((s : ℝ)^2 - V.card)^k * (V.card : ℝ)^2 := by
  classical
  let A (i j : ↥V) : ℝ := if D i j = true then 1 else 0
  have count (P : ℕ → Prop) [DecidablePred P] :
      (∑ i : ↥V, if P i.val then (1:ℝ) else 0) = (V.filter P).card := by
    calc _ = ∑ j ∈ V, if P j then (1:ℝ) else 0 := sum_attach V _
         _ = _ := by simp
  have rsum (i : ↥V) : ∑ j, A i j = s := by
    calc _ = ((outN D V i).card : ℝ) := count _
         _ = _ := by rw [rows _ i.property]
  have csum (j : ↥V) : ∑ i, A i j = s := by
    calc _ = ((inN D V j).card : ℝ) := count _
         _ = _ := by rw [cols _ j.property]
  have cov (i j : ↥V) : 1 ≤ gram A i j := by
    obtain ⟨w,wv,wi,wj⟩ := pair i i.property j j.property
    let a : ↥V := ⟨w,wv⟩
    have b := single_le_sum (s := (univ : Finset ↥V)) (f := fun v => A v i * A v j)
      (fun v _ => by dsimp [A]; positivity) (mem_univ a)
    simpa [gram, A, a, wi, wj] using b
  obtain ⟨v,vV⟩ := live
  let a : ↥V := ⟨v,vV⟩
  let N : ℝ := V.card
  let delta (i : ↥V) : ℝ := if i = a then 1 else 0
  let f (i : ↥V) := N * delta i - 1
  have dsum : ∑ i, delta i = 1 := by simp [delta]
  have fsum : ∑ i, f i = 0 := by
    simp only [f, sum_sub_distrib, ← mul_sum, dsum, mul_one, sum_const, card_univ,
      nsmul_eq_mul, Fintype.card_coe, N, sub_self]
  have finit : ∑ i, (f i)^2 ≤ N^2 := by
    have eq (i : ↥V) : (f i)^2 = (N^2 - 2*N) * delta i + 1 := by
      by_cases h : i = a
      · simp [f, delta, h]; ring
      · simp [f, delta, h]
    simp only [eq, sum_add_distrib, ← mul_sum, dsum, mul_one, sum_const, card_univ,
      nsmul_eq_mul, Fintype.card_coe]
    have hn : 0 ≤ N := Nat.cast_nonneg _
    change N^2 - 2*N + N ≤ N^2
    linarith
  have cent (d : ℕ) (i : ↥V) : iter A f d i = N * iter A delta d i - (s:ℝ)^d := by
    induction d generalizing i with
    | zero => simp [iter, f]
    | succ d ih =>
      simp only [iter, step, ih, mul_sub, sum_sub_distrib]
      simp_rw [mul_left_comm (A i _) N, ← mul_sum, ← sum_mul, rsum, pow_succ']
  have empty (d : ℕ) (i : ↥V) (no : ¬Walk D V i a d) : iter A delta d i = 0 := by
    induction d generalizing i with
    | zero =>
      have diff : i ≠ a := by rintro rfl; exact no (.refl _)
      simp [iter, delta, diff]
    | succ d ih =>
      apply sum_eq_zero
      intro j _
      by_cases ed : D i j = true
      · rw [ih j (fun walk => no (.step j.property ed walk)), mul_zero]
      · simp [A, ed]
  have atA := cent k a
  rw [empty k a (free _ _ hk kq), mul_zero, zero_sub] at atA
  have b := single_le_sum (f := fun i => (iter A f k i)^2)
    (fun i _ => sq_nonneg _) (mem_univ a)
  rw [atA, neg_sq] at b
  have nonneg : 0 ≤ (s:ℝ)^2 - Fintype.card ↥V := by simpa using sub_nonneg.mpr de
  have total := (iter_energy rsum csum cov nonneg f fsum k).2
  rw [Fintype.card_coe] at total nonneg
  exact (b.trans total).trans (mul_le_mul_of_nonneg_left finit (pow_nonneg nonneg _))

/-- At bank size two every label has at least `q+1` predecessors. The
predecessors of a given label cover all other labels using at most `s-1`
more heads per predecessor. -/
theorem pair_band_indegree {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (free : QFree D V q) (rows : OutEq s D V) (hq : 1 ≤ q) (hs : 2 ≤ s)
    (band : V.card = q*(s-1)+2) (none : BypassRepair.NoHost q (s-1)) (p : ℕ) (pv : p ∈ V) :
    q+1 ≤ (inN D V p).card := by
  classical
  let P := inN D V p
  let S (x : ℕ) := (outN D V x).erase p
  have cover : V.erase p ⊆ P.biUnion S := by
    intro h hh
    obtain ⟨hp,hv⟩ := mem_erase.mp hh
    obtain ⟨x,xv,_,_,xp,xh,_⟩ := LoneRow.pair_parent none free hq hs
      (fun v hv => (rows v hv).ge) band pv hv hp.symm
    exact mem_biUnion.mpr ⟨x,mem_inN.mpr ⟨xv,xp⟩,mem_erase.mpr ⟨hp,mem_outN.mpr ⟨hv,xh⟩⟩⟩
  have sizes (x) (hx : x ∈ P) : (S x).card = s-1 := by
    obtain ⟨xv,xp⟩ := mem_inN.mp hx
    change ((outN D V x).erase p).card = s-1
    rw [card_erase_of_mem (mem_outN.mpr ⟨pv,xp⟩), rows x xv]
  have bound := (card_le_card cover).trans card_biUnion_le
  rw [sum_congr rfl sizes, sum_const, nsmul_eq_mul] at bound
  change (V.erase p).card ≤ P.card * (s-1) at bound
  rw [card_erase_of_mem pv, band] at bound
  by_contra short
  have small : P.card ≤ q := by change (inN D V p).card ≤ q; omega
  have bad := bound.trans (Nat.mul_le_mul_right (s-1) small)
  omega

/-- At and above the diagonal `q = s-1`, the lower-degree hypothesis excludes
the entire order `q*(s-1)+2` for `s ≥ 8`. -/
theorem two_label_near_diagonal {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (live : V.Nonempty) (free : QFree D V q) (rows : OutEq s D V)
    (hs : 8 ≤ s) (diagonal : s ≤ q+1) (none : BypassRepair.NoHost q (s-1)) :
    V.card ≠ q*(s-1)+2 := by
  classical
  intro band
  have indeg := pair_band_indegree free rows (by omega) (by omega) band none
  have low (p) (pv : p ∈ V) : s ≤ (inN D V p).card := diagonal.trans (indeg p pv)
  have total : (∑ j ∈ V, s) = ∑ j ∈ V, (inN D V j).card := by
    rw [← sum_congr rfl rows]
    exact Compose.ThinRigid.sum_out_eq_sum_in D V
  have cols (p) (pv : p ∈ V) : (inN D V p).card = s := ((sum_eq_sum_iff_of_le low).mp total p pv).symm
  obtain ⟨p,pv⟩ := live
  have pq := indeg p pv
  rw [cols p pv] at pq
  have qeq : q+1 = s := by omega
  have pair (i) (hi : i ∈ V) (j) (hj : j ∈ V) : ∃ w ∈ V, D w i = true ∧ D w j = true := by
    by_cases eq : i = j
    · subst j
      have pos : 0 < (inN D V i).card := by rw [cols i hi]; omega
      obtain ⟨w,hw⟩ := card_pos.mp pos
      obtain ⟨wv,wi⟩ := mem_inN.mp hw
      exact ⟨w,wv,wi,wi⟩
    · obtain ⟨w,wv,_,_,wi,wj,_⟩ := LoneRow.pair_parent none free (by omega) (by omega)
        (fun v hv => (rows v hv).ge) band hi hj eq
      exact ⟨w,wv,wi,wj⟩
  have hr : (8:ℝ) ≤ s := by exact_mod_cast hs
  have ord : (V.card:ℝ) = (s:ℝ)^2 - 2*s + 3 := by
    have ordN : V.card = q*q+2 := by simpa only [show s-1=q by omega] using band
    have ordR : (V.card:ℝ) = (q:ℝ)*q+2 := by exact_mod_cast ordN
    have qs : (q:ℝ)+1 = s := by exact_mod_cast qeq
    nlinarith only [ordR,qs,congrArg (fun x : ℝ => x^2) qs]
  have de : (V.card:ℝ) ≤ (s:ℝ)^2 := by linarith
  have cost := regular_return_bound ⟨p,pv⟩ free (by decide : 0 < 6) (by omega) rows cols pair de
  have lt : (s:ℝ)^2 - V.card < 2*s := by linarith
  have npos : (0:ℝ) < V.card := by exact_mod_cast card_pos.mpr (show V.Nonempty from ⟨p,pv⟩)
  have power : ((s:ℝ)^2 - V.card)^6 < (2*s)^6 := pow_lt_pow_left₀ lt (sub_nonneg.mpr de) (by decide)
  have upper : ((s:ℝ)^2 - V.card)^6 * (V.card:ℝ)^2 < ((s:ℝ)^6)^2 := by
    calc _ < (2*(s:ℝ))^6 * (V.card:ℝ)^2 := mul_lt_mul_of_pos_right power (sq_pos_of_pos npos)
         _ ≤ (2*(s:ℝ))^6 * ((s:ℝ)^2)^2 := by gcongr
         _ = 64 * (s:ℝ)^10 := by ring
         _ ≤ (s:ℝ)^2 * (s:ℝ)^10 := by
           gcongr
           nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ (s:ℝ)+8 by positivity)]
         _ = _ := by ring
  exact (not_lt_of_ge cost) upper

#print axioms two_label_near_diagonal

/-- The minimum-order source may have arbitrary outgoing degrees above its
floor. Choose exactly `s` outgoing arcs at each label before applying the
pair bound. -/
theorem source_order {q s : ℕ} (X : ShenMinimumOrder.Source q s)
    (hs : 8 ≤ s) (diagonal : s ≤ q+1) (none : BypassRepair.NoHost q (s-1)) :
    q*(s-1)+3 ≤ X.V.card := by
  have first := BypassBankReplay.order_floor none (by omega) X.free X.nonempty X.degree
  obtain ⟨F, sub, reg⟩ := exists_outEq X.degree
  have next := two_label_near_diagonal X.nonempty (qfree_sub sub X.free) reg hs diagonal none
  omega

#print axioms regular_return_bound
#print axioms source_order

end LeanCH.BR.PairCoverMixing

