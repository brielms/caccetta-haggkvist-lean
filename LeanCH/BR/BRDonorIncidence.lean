import LeanCH.BR.BRDonorWalks

/-! Donor absence forces uniform external incidence of strong banks in one
out-neighborhood. The No4 master does not assume saturation. The q=3 route
ports the independently paper-audited original return-middle argument. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem donor_path_no4 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (hno : DonorAbsent D V) {t n : ℕ} (ht : t∈V)
    (hn : 2 ≤ n) (f : ℕ→ℕ) (hm : ∀ i,i≤n→f i∈V)
    (he : ∀ i,i<n→D (f i) (f (i+1))=true)
    (hU : ∀ i,0 < i → i < n → D t (f i)=true)
    (hMt : ¬D t (f n)=true) (hback : D (f n) (f 0)=true)
    (hskip : ∀ i j,i+1 < j → j≤n→¬D (f i) (f j)=true) : False := by
  have edges : ∀ i,i<n→f (i+1)∈V ∧ D (f i) (f (i+1))=true :=
    fun i hi=>⟨hm _ (by omega),he i hi⟩
  by_cases hsmall : n≤3
  · have w := walk_between edges (Nat.zero_le n) le_rfl
    exact hf (f 0) ((n-0)+1) (by omega) (by omega) (w.snoc (hm 0 (by omega)) hback)
  have h4 : 4≤n := by omega
  have hnm : ¬D (f n) (f (n-3))=true := by
    intro e
    have w := walk_between edges (by omega : n-3≤n) le_rfl
    exact hf (f (n-3)) ((n-(n-3))+1) (by omega) (by omega)
      (w.snoc (hm _ (by omega)) e)
  apply hno t (f (n-1)) (f n) (f (n-3))
  apply donor_of_pattern (hf.mono_bound (by decide)) ht (hm _ (by omega)) (hm _ le_rfl) (hm _ (by omega))
    (hU _ (by omega) (by omega)) (hU _ (by omega) (by omega))
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using he (n-1) (by omega)) hMt
    (hskip _ _ (by omega) (by omega)) (hskip _ _ (by omega) le_rfl) hnm

theorem donor_path_return3 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 3) (hno : DonorAbsent D V) {r t x n : ℕ}
    (hr : r∈V) (ht : t∈V) (hx : x∈V) (etx : D t x=true) (exr : D x r=true)
    (hn : 2 ≤ n) (f : ℕ→ℕ) (hm : ∀ i,i≤n→f i∈V)
    (hroot : ∀ i,i≤n→D r (f i)=true)
    (he : ∀ i,i<n→D (f i) (f (i+1))=true)
    (hDt : D (f 0) t=true) (hU : ∀ i,0 < i → i < n → D t (f i)=true)
    (hMt : ¬D t (f n)=true) (hback : D (f n) (f 0)=true)
    (hskip : ∀ i j,i+1 < j → j≤n→¬D (f i) (f j)=true) : False := by
  have hf2 : QFree D V 2 := hf.mono_bound (by decide)
  have hSx : ∀ i,i≤n→¬D (f i) x=true := fun i hi e=>
    donor_no_triangle hf (hm i hi) hx hr e exr (hroot i hi)
  have hxd : ¬D x (f 0)=true := fun e=>
    donor_no_triangle hf (hm 0 (by omega)) ht hx hDt etx e
  have hun : D (f (n-1)) (f n)=true := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using he (n-1) (by omega)
  have hxu : ¬D x (f (n-1))=true := by
    intro exu
    have eDu : D (f 0) (f (n-1))=true := by
      by_contra nDu
      apply hno x r (f 0) (f (n-1))
      exact donor_of_pattern hf2 hx hr (hm 0 (by omega)) (hm _ (by omega)) exr exu
        (hroot 0 (by omega)) hxd
        (fun eur=>digonfree hf2 le_rfl hr (hm _ (by omega)) (hroot _ (by omega)) eur)
        (fun eud=>donor_no_triangle hf ht (hm _ (by omega)) (hm 0 (by omega))
          (hU _ (by omega) (by omega)) eud hDt) nDu
    exact donor_no_triangle hf (hm 0 (by omega)) (hm _ (by omega)) (hm n le_rfl) eDu hun hback
  have exm : D x (f n)=true := by
    by_contra nxm
    exact hno t (f (n-1)) (f n) x (donor_of_pattern hf2 ht (hm _ (by omega))
      (hm n le_rfl) hx (hU _ (by omega) (by omega)) etx hun hMt hxu nxm (hSx n le_rfl))
  by_cases hn2 : n=2
  · subst n
    exact donor_no_triangle hf (hm 0 (by omega)) (hm 1 (by omega)) (hm 2 le_rfl)
      (he 0 (by omega)) (he 1 (by omega)) hback
  have emp : D (f n) (f (n-2))=true := by
    by_contra nmp
    exact hno t x (f n) (f (n-2)) (donor_of_pattern hf2 ht hx (hm n le_rfl)
      (hm _ (by omega)) etx (hU _ (by omega) (by omega)) exm hMt
      (hSx _ (by omega)) (hskip _ _ (by omega) le_rfl) nmp)
  have epu : D (f (n-2)) (f (n-1))=true := by
    have e := he (n-2) (by omega)
    have hidx : n-2+1=n-1 := by omega
    simpa only [hidx] using e
  exact donor_no_triangle hf (hm _ (by omega)) (hm _ (by omega)) (hm n le_rfl) epu hun emp

theorem donor_strong_heads_all {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V 3) (hno : DonorAbsent D V)
    (hcase : Sat 3 D V ∨ QFree D V 4) {r t d : ℕ}
    (hr : r∈V) (ht : t∈V) (hSO : S⊆outN D V r) (hst : StrongBank D S)
    (nrt : ¬D r t=true) (hd : d∈S) (edt : D d t=true) : ∀ m∈S,D m t=true := by
  classical
  have hSV : S⊆V := hSO.trans outN_subset
  have hroot : ∀ s∈S,D r s=true := fun s hs=>(mem_outN.mp (hSO hs)).2
  let A := S.filter (fun s=>D s t=true)
  let B := S.filter (fun s=>¬D s t=true ∧ ¬D t s=true)
  have hA : A⊆S := filter_subset _ _
  have hdA : d∈A := mem_filter.mpr ⟨hd,edt⟩
  have back : ∀ m∈B,∀ d∈A,D m d=true := by
    intro m hm d hd
    obtain ⟨hmS,nmt,ntm⟩ := mem_filter.mp hm
    obtain ⟨hdS,edt⟩ := mem_filter.mp hd
    by_contra nmd
    exact hno r d t m (donor_of_pattern (hf.mono_bound (by decide)) hr (hSV hdS) ht
      (hSV hmS) (hroot d hdS) (hroot m hmS) edt nrt nmd nmt ntm)
  have hBempty : ∀ m∈S,¬(¬D m t=true ∧ ¬D t m=true) := by
    intro m hm hM
    have hmB : m∈B := mem_filter.mpr ⟨hm,hM⟩
    obtain ⟨l,w⟩ := hst d hd m hm
    obtain ⟨n,f,h0,hn,hmf,he,hnotA,hnotB,hskip⟩ :=
      shortest_bank_walk hA ⟨l,d,hdA,m,hmB,w⟩
    have hmem : ∀ i,i≤n→f i∈V := fun i hi=>hSV (hmf i hi)
    have hU : ∀ i,0 < i → i < n → D t (f i)=true := by
      intro i hi hin
      have nAt : ¬D (f i) t=true := fun e=>hnotA i hi hin.le (mem_filter.mpr ⟨hmf i hin.le,e⟩)
      by_contra nt
      exact hnotB i hin (mem_filter.mpr ⟨hmf i hin.le,nAt,nt⟩)
    have hback := back (f n) hn (f 0) h0
    have hDt := (mem_filter.mp h0).2
    have hMt := (mem_filter.mp hn).2.2
    have hn2 : 2≤n := by
      by_contra h
      have hn1 : n≤1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with hn0|hn1
      · subst n; exact (mem_filter.mp hn).2.1 hDt
      · subst n
        exact digonfree hf (by decide) (hmem 0 (by omega)) (hmem 1 le_rfl) (he 0 (by omega)) hback
    rcases hcase with hsat|hf4
    · have ntr : ¬D t r=true := fun e=>
        donor_no_triangle hf hr (hSV hd) ht (hroot d hd) edt e
      have htr : t≠r := by
        rintro rfl
        exact digonfree hf (by decide) hr (hSV hd) (hroot d hd) edt
      obtain ⟨_,l,hl,wr⟩ := mem_ball.mp (hsat t ht r hr nrt)
      have hl2 : l=2 := by
        have hl' : l≤2 := by simpa using hl
        by_contra hne
        have hl1 : l≤1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl1 with h0|h1
        · subst l; cases wr; exact htr rfl
        · subst l; cases wr with
          | step hx e w => cases w; exact ntr e
      subst l
      obtain ⟨x,wx,_,exr⟩ := wr.unsnoc
      cases wx with
      | step hx etx w =>
        cases w
        exact donor_path_return3 hf hno hr ht hx etx exr hn2 f hmem
          (fun i hi=>hroot _ (hmf i hi)) he hDt hU hMt hback hskip
    · exact donor_path_no4 hf4 hno ht hn2 f hmem he hU hMt hback hskip
  let U := S.filter (fun s=>¬D s t=true)
  have hclosed : ClosedBank D S U := by
    intro x hx y hy exy
    obtain ⟨hxS,nxt⟩ := mem_filter.mp hx
    have etx : D t x=true := by by_contra ntx; exact hBempty x hxS ⟨nxt,ntx⟩
    refine mem_filter.mpr ⟨hy,?_⟩
    intro eyt
    exact donor_no_triangle hf ht (hSV hxS) (hSV hy) etx exy eyt
  intro m hm
  by_contra nmt
  obtain ⟨l,w⟩ := hst m hm d hd
  have hdU := (walk_closed_bank hclosed (mem_filter.mpr ⟨hm,nmt⟩) w).1
  exact (mem_filter.mp hdU).2 edt

theorem donor_strong_external_uniform {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V 3) (hno : DonorAbsent D V)
    (hcase : Sat 3 D V ∨ QFree D V 4) {r t : ℕ}
    (hr : r∈V) (ht : t∈V) (hSO : S⊆outN D V r) (hst : StrongBank D S)
    (nrt : ¬D r t=true) : ∀ x∈S,∀ y∈S,D x t=D y t := by
  intro x hx y hy
  by_cases ex : D x t=true
  · rw [ex,donor_strong_heads_all hf hno hcase hr ht hSO hst nrt hx ex y hy]
  · have ey : ¬D y t=true := fun e=>ex (donor_strong_heads_all hf hno hcase hr ht hSO hst nrt hy e x hx)
    exact (Bool.eq_false_iff.mpr ex).trans (Bool.eq_false_iff.mpr ey).symm

theorem donor_strong_external_uniform_no4 {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V 4) (hno : DonorAbsent D V) {r t : ℕ}
    (hr : r∈V) (ht : t∈V) (hSO : S⊆outN D V r) (hst : StrongBank D S)
    (nrt : ¬D r t=true) : ∀ x∈S,∀ y∈S,D x t=D y t :=
  donor_strong_external_uniform (hf.mono_bound (by decide)) hno (Or.inr hf) hr ht hSO hst nrt

end LeanCH.BR.WeightedSD
