theory SubsetSum_DecisionTree
  imports "Complex_Main" "HOL-Real_Asymp.Real_Asymp"
    "Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean"
begin

(* ========================================================================= *)
(* PART 1: Bitvectors and Subset-Sum Setup                                  *)
(* ========================================================================= *)

section ‹0/1 integer vectors and bounded sums›

text ‹
  We represent selections by 0/1 integer vectors of a fixed length.
  For a list @{term "as :: int list"} and a 0/1 vector @{term "xs :: int list"},
  the subset-sum value is the dot product restricted to a set of indices.
›

(* A bitvector of length k is a list of k elements from {0,1} *)
definition bitvec :: "nat ⇒ int list set" where
  "bitvec k = {xs. length xs = k ∧ set xs ⊆ {0::int, 1}}"

(* Basic lemmas about bitvectors: cardinality, finiteness, etc. *)
lemma bitvec_0[simp]: "bitvec 0 = {[]}"
  unfolding bitvec_def by auto

lemma sum_pow2_int: "(∑ i<k. (2::int)^i) = 2^k - 1"
  by (induction k) simp_all

(* Bitvectors of length n+1 are exactly {0::xs} ∪ {1::xs} where xs has length n *)
lemma bitvec_Suc_partition:
  "bitvec (Suc n) =
     {0 # xs | xs. xs ∈ bitvec n} ∪ {1 # xs | xs. xs ∈ bitvec n}"
proof (rule subset_antisym)
  show "bitvec (Suc n) ⊆ {0 # xs | xs. xs ∈ bitvec n} ∪ {1 # xs | xs. xs ∈ bitvec n}"
  proof
    fix x assume x: "x ∈ bitvec (Suc n)"
    then obtain h t where HT: "x = h # t" and len: "length t = n"
      and sub: "set t ⊆ {0,1}"
      by (cases x) (auto simp: bitvec_def)
    from x HT have h01: "h = 0 ∨ h = 1"
      by (auto simp: bitvec_def)
    have t_in: "t ∈ bitvec n" using len sub by (simp add: bitvec_def)
    show "x ∈ {0 # xs | xs. xs ∈ bitvec n} ∪ {1 # xs | xs. xs ∈ bitvec n}"
      using HT h01 t_in by auto
  qed
next
  show "{0 # xs | xs. xs ∈ bitvec n} ∪ {1 # xs | xs. xs ∈ bitvec n} ⊆ bitvec (Suc n)"
  proof
    fix x assume "x ∈ {0 # xs | xs. xs ∈ bitvec n} ∪ {1 # xs | xs. xs ∈ bitvec n}"
    then show "x ∈ bitvec (Suc n)"
      by (auto simp: bitvec_def)
  qed
qed

(* The two halves of the partition are disjoint *)
lemma bitvec_Suc_disjoint:
  "{0 # xs | xs. xs ∈ bitvec n} ∩ {1 # xs | xs. xs ∈ bitvec n} = {}"
  by auto

(* There are exactly 2^n bitvectors of length n *)
lemma finite_bitvec[simp]: "finite (bitvec n)"
proof (induction n)
  case 0
  show ?case by (simp add: bitvec_def)
next
  case (Suc n)
  have part: "bitvec (Suc n) =
        {0 # xs | xs. xs ∈ bitvec n} ∪ {1 # xs | xs. xs ∈ bitvec n}"
    by (rule bitvec_Suc_partition)
  have eq0: "{0 # xs | xs. xs ∈ bitvec n} = (λxs. 0 # xs) ` bitvec n" by auto
  have eq1: "{1 # xs | xs. xs ∈ bitvec n} = (λxs. 1 # xs) ` bitvec n" by auto
  have fin0: "finite {0 # xs | xs. xs ∈ bitvec n}"
    unfolding eq0 by (intro finite_imageI Suc.IH)
  have fin1: "finite {1 # xs | xs. xs ∈ bitvec n}"
    unfolding eq1 by (intro finite_imageI Suc.IH)
  show ?case by (simp add: part fin0 fin1)
qed

lemma card_bitvec: "card (bitvec n) = 2 ^ n"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have part: "bitvec (Suc n) =
        {0 # xs | xs. xs ∈ bitvec n} ∪ {1 # xs | xs. xs ∈ bitvec n}"
    by (rule bitvec_Suc_partition)
  have disj: "{0 # xs | xs. xs ∈ bitvec n} ∩ {1 # xs | xs. xs ∈ bitvec n} = {}"
    by (rule bitvec_Suc_disjoint)
  have eq0: "{0 # xs | xs. xs ∈ bitvec n} = (λxs. 0 # xs) ` bitvec n" by auto
  have eq1: "{1 # xs | xs. xs ∈ bitvec n} = (λxs. 1 # xs) ` bitvec n" by auto
  have "card (bitvec (Suc n))
      = card {0 # xs | xs. xs ∈ bitvec n} + card {1 # xs | xs. xs ∈ bitvec n}"
    by (simp add: part disj card_Un_disjoint)
  also have "… = card ((λxs. 0 # xs) ` bitvec n) + card ((λxs. 1 # xs) ` bitvec n)"
    by (simp add: eq0 eq1)
  also have "… = card (bitvec n) + card (bitvec n)"
    by (simp add: card_image)
  also have "… = 2 ^ n + 2 ^ n" using Suc.IH by simp
  also have "… = 2 ^ Suc n" by simp
  finally show ?case .
qed

(* ========================================================================= *)
(* PART 2: The Split Function e_k and LHS/RHS Sets                          *)
(* ========================================================================= *)

(* Sum of as[i] * xs[i] over index set I *)
definition sum_as_on :: "int list ⇒ nat set ⇒ int list ⇒ int" where
  "sum_as_on as I xs = (∑ i ∈ I. as ! i * xs ! i)"

(* Left-hand side: sum over first k indices *)
definition lhs_of :: "int list ⇒ nat ⇒ int list ⇒ int" where
  "lhs_of as k xs = sum_as_on as {0..<k} xs"

(* Right-hand side: target s minus sum over indices k..n *)
definition rhs_of :: "int list ⇒ nat ⇒ int ⇒ int list ⇒ int" where
  "rhs_of as k s xs = s - sum_as_on as {k..<length as} xs"

(* THE KEY SPLIT FUNCTION:
   e_k maps each bitvector xs to a pair (L, R) where:
   - L is the sum of the first k weights times their selections
   - R is what remains of the target after subtracting the last (n-k) weights
   
   This splits the subset-sum problem into two independent subproblems! *)
definition e_k :: "int list ⇒ int ⇒ nat ⇒ int list ⇒ int × int" where
  "e_k as s k xs = (lhs_of as k xs, rhs_of as k s xs)"

(* LHS: the set of all possible left-hand-side values *)
definition LHS :: "(int list ⇒ int × int) ⇒ nat ⇒ int set" where
  "LHS e n = {fst (e xs) | xs. xs ∈ bitvec n}"

(* RHS: the set of all possible right-hand-side values *)
definition RHS :: "(int list ⇒ int × int) ⇒ nat ⇒ int set" where
  "RHS e n = {snd (e xs) | xs. xs ∈ bitvec n}"

(* ========================================================================= *)
(* PART 3: Distinct Subset Sums Property                                    *)
(* ========================================================================= *)

section ‹Distinct-subset-sums (full length)›

text ‹
  CRITICAL PROPERTY: A weight list has "distinct subset sums" if different
  0/1 selections always produce different total sums. This is key because
  it makes the split function e_k INJECTIVE on both halves.
›

text ‹
  Distinct subset sums: different 0/1 n-vectors yield different total sums.
›
definition distinct_subset_sums :: "int list ⇒ bool" where
  "distinct_subset_sums as ≡
     (∀xs∈bitvec (length as). ∀ys∈bitvec (length as).
        xs ≠ ys ⟶ (∑ i < length as. as ! i * xs ! i) ≠ (∑ i < length as. as ! i * ys ! i))"

(* ========================================================================= *)
(* PART 4: Padding Lemmas (Technical Machinery)                             *)
(* ========================================================================= *)

section ‹Padding lemmas for prefix/suffix reasoning›

(* These lemmas let us extend/restrict bitvectors with zeros while preserving
   the prefix or suffix properties we care about. Used to show that:
   - LHS values come from first k positions (pad with zeros after)
   - RHS values come from last (n-k) positions (pad with zeros before) *)
lemma pad_suffix_zeros_in_bitvec:
  assumes "p ∈ bitvec k" "n ≥ k"
  shows "p @ replicate (n - k) 0 ∈ bitvec n"
  using assms by (auto simp: bitvec_def)

lemma pad_prefix_zeros_in_bitvec:
  assumes "q ∈ bitvec (n - k)" "k ≤ n"
  shows "(replicate k 0) @ q ∈ bitvec n"
  using assms by (auto simp: bitvec_def)

lemma drop_in_bitvec:
  assumes "xs ∈ bitvec n" "k ≤ n"
  shows   "drop k xs ∈ bitvec (n - k)"
proof -
  have len: "length xs = n" and xs01: "set xs ⊆ {0,1}"
    using assms(1) by (auto simp: bitvec_def)
  have "length (drop k xs) = n - k"
    using assms(2) len by simp
  moreover have "set (drop k xs) ⊆ {0,1}"
    using xs01 by (auto dest: in_set_dropD)
  ultimately show ?thesis by (simp add: bitvec_def)
qed

lemma sum_as_on_prefix_pad:
  assumes "xs ∈ bitvec n" "k ≤ n"
  shows "sum_as_on as {0..<k} xs =
         sum_as_on as {0..<k} (take k xs @ replicate (n - k) 0)"
  using assms
  by (simp add: sum_as_on_def bitvec_def atLeast0LessThan less_diff_conv nth_append min_def)

lemma sum_reindex_add:
  fixes k n :: nat
  shows "(∑ i ∈ {k..<n}. g i) = (∑ j ∈ {0..<n - k}. g (k + j))"
proof -
  have inj: "inj_on ((+) k) {0..<n - k}" by auto
  have E: "sum g ((+) k ` {0..<n - k}) = sum (g ∘ ((+) k)) {0..<n - k}"
    by (rule sum.reindex[OF inj])
  have F: "sum (g ∘ ((+) k)) {0..<n - k} = (∑ j = 0..<n - k. g (k + j))"
    by (simp add: o_def)
  from E F show ?thesis by (metis sum.atLeastLessThan_shift_0)
qed

lemma sum_as_on_suffix_pad_shift:
  assumes lenq: "length q = n - k" and kn: "k ≤ n"
  shows
    "sum_as_on as {k..<n} ((replicate k 0) @ q)
     = (∑ j ∈ {0..<n - k}. as ! (k + j) * q ! j)"
proof -
  have A: "⋀i. i ∈ {k..<n} ⟹ ((replicate k 0) @ q) ! i = q ! (i - k)"
    using lenq by (auto simp: nth_append)

  have "sum_as_on as {k..<n} ((replicate k 0) @ q)
        = (∑ i ∈ {k..<n}. as ! i * ((replicate k 0) @ q) ! i)"
    by (simp add: sum_as_on_def)
  also have "… = (∑ i ∈ {k..<n}. as ! i * q ! (i - k))"
    by (simp add: A)
  also have "… = (∑ j ∈ {0..<n - k}. as ! (k + j) * q ! ((k + j) - k))"
    by (subst sum_reindex_add) simp
  also have "… = (∑ j ∈ {0..<n - k}. as ! (k + j) * q ! j)"
    by simp
  finally show ?thesis .
qed

lemma sum_as_on_suffix_drop_shift:
  assumes xs: "xs ∈ bitvec n" and kn: "k ≤ n"
  shows "sum_as_on as {k..<n} xs
       = (∑ j∈{0..<n - k}. as ! (k + j) * (drop k xs) ! j)"
proof -
  have lenxs: "length xs = n" using xs by (simp add: bitvec_def)
  have "sum_as_on as {k..<n} xs = (∑ i∈{k..<n}. as ! i * xs ! i)"
    by (simp add: sum_as_on_def)
  also have "… = (∑ i∈{k..<n}. as ! i * (drop k xs) ! (i - k))"
  proof (rule sum.cong[OF refl])
    fix i assume "i ∈ {k..<n}"
    with lenxs kn show "as ! i * xs ! i = as ! i * (drop k xs) ! (i - k)"
      by simp
  qed
  also have "… = (∑ j∈{0..<n - k}. as ! (k + j) * (drop k xs) ! j)"
    by (subst sum_reindex_add) simp
  finally show ?thesis .
qed

lemma take_in_bitvec:
  assumes "xs ∈ bitvec n" "k ≤ n"
  shows   "take k xs ∈ bitvec k"
proof -
  have "length (take k xs) = k" using assms by (simp add: bitvec_def)
  moreover have "set (take k xs) ⊆ {0,1}"
    using assms by (auto simp: bitvec_def dest!: in_set_takeD)
  ultimately show ?thesis by (simp add: bitvec_def)
qed

(* padded tail entries are 0 for indices i ∈ {k..<n} *)
lemma padded_tail_zero:
  assumes "length p = k" and "i ∈ {k..<n}"
  shows   "(p @ replicate (n - k) (0::int)) ! i = 0"
proof -
  have ik: "k ≤ i" and in_lt: "i < n" using assms(2) by auto
  have "(p @ replicate (n - k) (0::int)) ! i = (replicate (n - k) (0::int)) ! (i - k)"
    using assms(1) ik by (simp add: nth_append)
  moreover have "i - k < n - k" using in_lt ik by arith
  ultimately show ?thesis by simp
qed

(* ========================================================================= *)
(* PART 5: THE MAIN COUNTING THEOREMS (Lemma 2)                            *)
(* ========================================================================= *)

(* THEOREM: If weights have distinct subset sums, then |LHS| = 2^k *)
lemma card_LHS_e_k:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k ≤ n"
      and distinct: "distinct_subset_sums as"
  shows "card (LHS (e_k as s k) n) = 2 ^ k"
proof -
  let ?pref = "bitvec k"
  define f where "f p = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))" for p

  (* Every LHS value arises from some prefix p. *)
  have LHS_subset: "LHS (e_k as s k) n ⊆ f ` ?pref"
  proof
    fix v assume "v ∈ LHS (e_k as s k) n"
    then obtain xs where xs: "xs ∈ bitvec n" and v: "v = fst (e_k as s k xs)"
      by (auto simp: LHS_def)
    define p where "p = take k xs"
    have p_in: "p ∈ ?pref" using xs k_le by (simp add: p_def take_in_bitvec)
    have "v = sum_as_on as {0..<k} xs"
      by (simp add: v e_k_def lhs_of_def sum_as_on_def)
    also have "… = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))"
      using xs k_le by (simp add: p_def sum_as_on_prefix_pad n_def)
    finally have "v = f p" by (simp add: f_def)
    thus "v ∈ f ` ?pref" using p_in by blast
  qed

  (* Every prefix p gives a realizable LHS value. *)
  have subset_LHS: "f ` ?pref ⊆ LHS (e_k as s k) n"
  proof
    fix v assume "v ∈ f ` ?pref"
    then obtain p where p: "p ∈ ?pref" and v: "v = f p" by blast
    have xs_in: "p @ replicate (n - k) (0::int) ∈ bitvec n"
      using p k_le by (rule pad_suffix_zeros_in_bitvec)
    have "v = sum_as_on as {0..<k} (p @ replicate (n - k) (0::int))"
      by (simp add: v f_def)
    hence "v = fst (e_k as s k (p @ replicate (n - k) (0::int)))"
      by (simp add: e_k_def lhs_of_def)
    thus "v ∈ LHS (e_k as s k) n"
      using xs_in by (auto simp: LHS_def)
  qed

  have LHS_eq_img: "LHS (e_k as s k) n = f ` ?pref"
    using LHS_subset subset_LHS by blast

  (* Injectivity on prefixes by padding with zeros and using distinct sums. *)
  have inj_f: "inj_on f ?pref"
  proof (rule inj_onI)
    fix p1 p2 assume p1: "p1 ∈ ?pref" and p2: "p2 ∈ ?pref" and eq: "f p1 = f p2"
    have lenp1: "length p1 = k" using p1 by (simp add: bitvec_def)
    have lenp2: "length p2 = k" using p2 by (simp add: bitvec_def)

    have pref_eq:
      "sum_as_on as {0..<k} (p1 @ replicate (n - k) (0::int))
       = sum_as_on as {0..<k} (p2 @ replicate (n - k) (0::int))"
      using eq by (simp add: f_def)

    (* --- split the big sums and finish the equality --- *)
    let ?x1 = "p1 @ replicate (n - k) (0::int)"
    let ?x2 = "p2 @ replicate (n - k) (0::int)"
    let ?F1 = "(λi. as ! i * ?x1 ! i)"
    let ?F2 = "(λi. as ! i * ?x2 ! i)"

    have fin1: "finite ({0..<k}::nat set)" by simp
    have fin2: "finite ({k..<n}::nat set)" by simp
    have disj: "{0..<k} ∩ {k..<n} = ({}::nat set)" by auto
    have un:   "{0..<k} ∪ {k..<n} = {0..<n}" using k_le by auto

    have split1:
      "(∑i∈{0..<n}. ?F1 i)
      = (∑i∈{0..<k}. ?F1 i) + (∑i∈{k..<n}. ?F1 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

    have split2:
      "(∑i∈{0..<n}. ?F2 i)
        = (∑i∈{0..<k}. ?F2 i) + (∑i∈{k..<n}. ?F2 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

(* tails are zero because padded tail entries are 0 *)
    have tail1:
      "(∑i∈{k..<n}. as ! i * (p1 @ replicate (n - k) (0::int)) ! i) = 0"
      by (rule sum.neutral, intro ballI, simp add: padded_tail_zero[OF lenp1])

    have tail2:
      "(∑i∈{k..<n}. as ! i * (p2 @ replicate (n - k) (0::int)) ! i) = 0"
      by (rule sum.neutral, intro ballI, simp add: padded_tail_zero[OF lenp2])

(* prefixes equal via your pref_eq *)
    have pref1: "(∑i∈{0..<k}. ?F1 i) = sum_as_on as {0..<k} ?x1"
      by (simp add: sum_as_on_def)
    have pref2: "(∑i∈{0..<k}. ?F2 i) = sum_as_on as {0..<k} ?x2"
      by (simp add: sum_as_on_def)

    have full_eq_set:
    "(∑i∈{0..<n}. ?F1 i) = (∑i∈{0..<n}. ?F2 i)"
    using pref_eq tail1 tail2 by (simp add: split1 split2 pref1 pref2)

(* if you need the < n binder form *)
    have full_eq:
    "(∑ i < n. as ! i * ?x1 ! i) = (∑ i < n. as ! i * ?x2 ! i)"
    using full_eq_set by (simp add: atLeast0LessThan)

    have xs1: "?x1 ∈ bitvec n" using p1 k_le by (rule pad_suffix_zeros_in_bitvec)
    have xs2: "?x2 ∈ bitvec n" using p2 k_le by (rule pad_suffix_zeros_in_bitvec)

    from full_eq xs1 xs2 distinct n_def
    have "?x1 = ?x2"
      unfolding distinct_subset_sums_def by auto
    thus "p1 = p2" by simp
  qed

  have "card (LHS (e_k as s k) n) = card (f ` ?pref)"
    by (simp add: LHS_eq_img)
  also have "… = card ?pref" by (rule card_image; use inj_f in auto)
  also have "… = 2 ^ k" by (rule card_bitvec)
  finally show ?thesis .
qed

(* THEOREM: If weights have distinct subset sums, then |RHS| = 2^(n-k) *)
lemma card_RHS_e_k:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k ≤ n"
      and distinct: "distinct_subset_sums as"
  shows "card (RHS (e_k as s k) n) = 2 ^ (n - k)"
proof -
  let ?suf = "bitvec (n - k)"
  define g where "g q = s - sum_as_on as {k..<n} ((replicate k (0::int)) @ q)" for q

  (* Every RHS value arises from some suffix q. *)
  have RHS_subset: "RHS (e_k as s k) n ⊆ g ` ?suf"
  proof
    fix v assume "v ∈ RHS (e_k as s k) n"
    then obtain xs where xs: "xs ∈ bitvec n" and vdef: "v = snd (e_k as s k xs)"
      by (auto simp: RHS_def)

    define q where "q = drop k xs"
    have q_in: "q ∈ bitvec (n - k)"
      by (simp add: q_def drop_in_bitvec[OF xs k_le])
    have q_len: "length q = n - k"
      using q_in by (simp add: bitvec_def)

  (* rewrite the xs-tail and the padded-tail to the same shifted sum *)
    have xs_tail:
      "sum_as_on as {k..<n} xs
      = (∑ j∈{0..<n - k}. as ! (k + j) * q ! j)"
      by (simp add: q_def sum_as_on_suffix_drop_shift[OF xs k_le])
    have pad_tail:
      "sum_as_on as {k..<n} ((replicate k (0::int)) @ q)
      = (∑ j∈{0..<n - k}. as ! (k + j) * q ! j)"
      using sum_as_on_suffix_pad_shift[OF q_len k_le] by simp

    have "v = s - sum_as_on as {k..<n} xs"
      by (simp add: vdef e_k_def rhs_of_def sum_as_on_def n_def)
    also have "... = s - (∑ j∈{0..<n - k}. as ! (k + j) * q ! j)"
      by (simp add: xs_tail)
    also have "... = s - sum_as_on as {k..<n} ((replicate k 0) @ q)"
      by (simp add: pad_tail)
    finally have "v = g q" by (simp add: g_def)

    thus "v ∈ g ` ?suf" using q_in by blast
  qed

  (* Every suffix q gives a realizable RHS value. *)
  have subset_RHS: "g ` ?suf ⊆ RHS (e_k as s k) n"
  proof
    fix v assume "v ∈ g ` ?suf"
    then obtain q where q: "q ∈ ?suf" and v: "v = g q" by blast
    have xs_in: "(replicate k (0::int)) @ q ∈ bitvec n"
      using q k_le by (rule pad_prefix_zeros_in_bitvec)
    have "v = s - sum_as_on as {k..<n} ((replicate k (0::int)) @ q)"
      by (simp add: v g_def)
    hence "v = snd (e_k as s k ((replicate k (0::int)) @ q))"
      by (simp add: e_k_def rhs_of_def sum_as_on_def n_def)
    thus "v ∈ RHS (e_k as s k) n"
      using xs_in by (auto simp: RHS_def)
  qed

  have RHS_eq_img: "RHS (e_k as s k) n = g ` ?suf"
    using RHS_subset subset_RHS by blast

  (* Injectivity on suffixes by padding with zeros and using distinct sums. *)
  have inj_g: "inj_on g ?suf"
  proof (rule inj_onI)
    fix q1 q2 assume q1: "q1 ∈ ?suf" and q2: "q2 ∈ ?suf" and eq: "g q1 = g q2"
    have xs1: "(replicate k (0::int)) @ q1 ∈ bitvec n"
      using q1 k_le by (rule pad_prefix_zeros_in_bitvec)
    have xs2: "(replicate k (0::int)) @ q2 ∈ bitvec n"
      using q2 k_le by (rule pad_prefix_zeros_in_bitvec)

  (* from g q1 = g q2, tails are equal *)
    from eq have tails_eq:
      "sum_as_on as {k..<n} ((replicate k 0) @ q1)
      = sum_as_on as {k..<n} ((replicate k 0) @ q2)"
      by (simp add: g_def)

  (* --- turn tail equality into full-sum equality --- *)
    let ?x1 = "(replicate k (0::int)) @ q1"
    let ?x2 = "(replicate k (0::int)) @ q2"
    let ?F1 = "(λi. as ! i * ?x1 ! i)"
    let ?F2 = "(λi. as ! i * ?x2 ! i)"

    have fin1: "finite ({0..<k}::nat set)" by simp
    have fin2: "finite ({k..<n}::nat set)" by simp
    have disj: "{0..<k} ∩ {k..<n} = ({}::nat set)" by auto
    have un:   "{0..<k} ∪ {k..<n} = {0..<n}" using k_le by auto

    have split1:
      "(∑i∈{0..<n}. ?F1 i)
      = (∑i∈{0..<k}. ?F1 i) + (∑i∈{k..<n}. ?F1 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)
    have split2:
      "(∑i∈{0..<n}. ?F2 i)
      = (∑i∈{0..<k}. ?F2 i) + (∑i∈{k..<n}. ?F2 i)"
      by (subst un[symmetric], rule sum.union_disjoint[OF fin1 fin2], simp_all add: disj)

  (* prefixes are 0: the first k entries are the replicated zeros *)
    have pref1: "(∑i∈{0..<k}. ?F1 i) = 0" by (simp add: nth_append)
    have pref2: "(∑i∈{0..<k}. ?F2 i) = 0" by (simp add: nth_append)

  (* tails equal, rewrite via sum_as_on_def / n_def *)
    have tails_eq_set:
    "(∑i∈{k..<n}. ?F1 i) = (∑i∈{k..<n}. ?F2 i)"
      using tails_eq by (simp add: sum_as_on_def n_def atLeast0LessThan)

    have full_eq_set:
      "(∑i∈{0..<n}. ?F1 i) = (∑i∈{0..<n}. ?F2 i)"
      by (simp add: split1 split2 pref1 pref2 tails_eq_set)

    have full_eq:
      "(∑ i < n. as ! i * ?x1 ! i) = (∑ i < n. as ! i * ?x2 ! i)"
      using full_eq_set by (simp add: atLeast0LessThan)

(* Make the “distinct subset sums” assumption into an injectivity fact *)
    have inj_sum:
      "inj_on (λxs. (∑i < n. as ! i * xs ! i)) (bitvec n)"
      using distinct
      unfolding distinct_subset_sums_def n_def
      by (intro inj_onI) (auto simp: atLeast0LessThan)

(* Apply injectivity to the two padded vectors *)
    have "?x1 = ?x2"
      using inj_sum xs1 xs2 full_eq
      by (force simp: inj_on_def)

(* Cancel the common prefix *)
    then have "q1 = q2" by simp
    thus "q1 = q2" .
  qed

  have "card (RHS (e_k as s k) n) = card (g ` ?suf)"
    by (simp add: RHS_eq_img)
  also have "… = card ?suf" by (rule card_image; use inj_g in auto)
  also have "… = 2 ^ (n - k)" by (simp add: card_bitvec)
  finally show ?thesis .
qed

(* COROLLARY: The product |LHS| × |RHS| = 2^n *)
theorem lemma2_split:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k ≤ n"
      and distinct: "distinct_subset_sums as"
  shows "card (LHS (e_k as s k) n) * card (RHS (e_k as s k) n) = 2 ^ n"
proof -
  have L: "card (LHS (e_k as s k) n) = 2 ^ k"
    by (rule card_LHS_e_k[OF n_def k_le distinct])
  have R: "card (RHS (e_k as s k) n) = 2 ^ (n - k)"
    by (rule card_RHS_e_k[OF n_def k_le distinct])
  have kn: "k + (n - k) = n" using k_le by simp
  from L R show ?thesis
    by (simp add: power_add[symmetric] kn)
qed

(* ========================================================================= *)
(* PART 6: AM-GM Lower Bound (Lemma 3)                                      *)
(* ========================================================================= *)

(* THEOREM: If A × B ≥ 2^n, then A + B ≥ 2√(2^n) by AM-GM inequality *)
lemma lemma3_AFP:
  fixes A B :: real and n :: nat
  assumes A0: "A ≥ 0" and B0: "B ≥ 0"
      and ABge: "A * B ≥ (2::real) ^ n"
  shows "A + B ≥ 2 * sqrt ((2::real) ^ n)"
proof -
  (* AM–GM from AFP/Analysis *)
  have amgm: "2 * sqrt (A * B) ≤ A + B"
    using A0 B0 arithmetic_geometric_mean_binary by force
  (* sqrt is monotone on ℝ≥0 *)
  have "sqrt ((2::real) ^ n) ≤ sqrt (A * B)"
    using ABge A0 B0 by simp
  hence "2 * sqrt ((2::real) ^ n) ≤ 2 * sqrt (A * B)" by simp
  with amgm show ?thesis by linarith
qed

(* COROLLARY: For distinct subset sums, |LHS| + |RHS| ≥ 2√(2^n) *)
corollary lhs_rhs_sum_lower_bound:
  fixes as :: "int list" and s :: int and n k :: nat
  assumes n_def: "n = length as" and k_le: "k ≤ n" and distinct: "distinct_subset_sums as"
  shows "real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))
         ≥ 2 * sqrt ((2::real) ^ n)"
proof -
  have prod_eq_nat:
    "card (LHS (e_k as s k) n) * card (RHS (e_k as s k) n) = 2 ^ n"
    by (rule lemma2_split[OF n_def k_le distinct])

(* same product in ℝ *)
  have prod_eq_real:
    "real (card (LHS (e_k as s k) n)) * real (card (RHS (e_k as s k) n))
    = (2::real) ^ n"
    using prod_eq_nat
    by (metis numeral_power_eq_of_nat_cancel_iff of_nat_mult)

  have prod_ge:
    "(2::real) ^ n ≤ real (card (LHS (e_k as s k) n)) * real (card (RHS (e_k as s k) n))"
    by (simp add: prod_eq_real)

  have A0: "0 ≤ real (card (LHS (e_k as s k) n))" by simp
  have B0: "0 ≤ real (card (RHS (e_k as s k) n))" by simp

  from lemma3_AFP[OF A0 B0 prod_ge]
  show "real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))
      ≥ 2 * sqrt ((2::real) ^ n)"
  by simp
qed

(* ========================================================================= *)
(* PART 7: Decision Tree Model (Lemma 1 Framework)                          *)
(* ========================================================================= *)

section ‹Decision-tree reader model and coverage (Lemma 1)›

(* A decision tree that can query left-oracle at indices iL and 
   right-oracle at indices iR *)
datatype ('iL,'iR) dtr =
    Leaf bool
  | AskL 'iL "('iL,'iR) dtr" "('iL,'iR) dtr"
  | AskR 'iR "('iL,'iR) dtr" "('iL,'iR) dtr"

(* Run the tree with two oracles oL and oR *)
fun run :: "('iL ⇒ bool) ⇒ ('iR ⇒ bool) ⇒ ('iL,'iR) dtr ⇒ bool" where
  "run oL oR (Leaf b) = b"
| "run oL oR (AskL i t0 t1) = run oL oR (if oL i then t1 else t0)"
| "run oL oR (AskR j t0 t1) = run oL oR (if oR j then t1 else t0)"

(* Track which left-indices were queried during the run *)
fun seenL_run :: "('iL ⇒ bool) ⇒ ('iR ⇒ bool) ⇒ ('iL,'iR) dtr ⇒ 'iL set" where
  "seenL_run oL oR (Leaf b) = {}"
| "seenL_run oL oR (AskL i t0 t1) =
     insert i (seenL_run oL oR (if oL i then t1 else t0))"
| "seenL_run oL oR (AskR j t0 t1) =
     seenL_run oL oR (if oR j then t1 else t0)"

(* Track which right-indices were queried *)
fun seenR_run :: "('iL ⇒ bool) ⇒ ('iR ⇒ bool) ⇒ ('iL,'iR) dtr ⇒ 'iR set" where
  "seenR_run oL oR (Leaf b) = {}"
| "seenR_run oL oR (AskL i t0 t1) =
     seenR_run oL oR (if oL i then t1 else t0)"
| "seenR_run oL oR (AskR j t0 t1) =
     insert j (seenR_run oL oR (if oR j then t1 else t0))"

(* Count the number of queries made *)
fun steps_run :: "('iL ⇒ bool) ⇒ ('iR ⇒ bool) ⇒ ('iL,'iR) dtr ⇒ nat" where
  "steps_run oL oR (Leaf b) = 0"
| "steps_run oL oR (AskL i t0 t1) =
     Suc (steps_run oL oR (if oL i then t1 else t0))"
| "steps_run oL oR (AskR j t0 t1) =
     Suc (steps_run oL oR (if oR j then t1 else t0))"

(* Well-formedness: tree only queries from declared index sets *)
text ‹Well-formedness: the tree only queries declared L/R indices.›
inductive wf_dtr :: "'iL set ⇒ 'iR set ⇒ ('iL,'iR) dtr ⇒ bool" where
  Leaf[intro!]:  "wf_dtr L R (Leaf b)"
| AskL[intro!]:  "i ∈ L ⟹ wf_dtr L R t0 ⟹ wf_dtr L R t1 ⟹ wf_dtr L R (AskL i t0 t1)"
| AskR[intro!]:  "j ∈ R ⟹ wf_dtr L R t0 ⟹ wf_dtr L R t1 ⟹ wf_dtr L R (AskR j t0 t1)"

lemma seenL_subset:
  assumes "wf_dtr L R T" shows "seenL_run oL oR T ⊆ L"
  using assms by (induction T) auto

lemma seenR_subset:
  assumes "wf_dtr L R T" shows "seenR_run oL oR T ⊆ R"
  using assms by (induction T) auto

(* tiny helpers for the chosen branch *)
lemma seenL_sub_AskL:
  "seenL_run oL oR (if oL i then t1 else t0) ⊆ seenL_run oL oR (AskL i t0 t1)"
  by (cases "oL i") auto

lemma seenR_eq_AskL:
  "seenR_run oL oR (if oL i then t1 else t0) = seenR_run oL oR (AskL i t0 t1)"
  by (cases "oL i") auto

lemma seenR_sub_AskR:
  "seenR_run oL oR (if oR j then t1 else t0) ⊆ seenR_run oL oR (AskR j t0 t1)"
  by (cases "oR j") auto

lemma seenL_eq_AskR:
  "seenL_run oL oR (if oR j then t1 else t0) = seenL_run oL oR (AskR j t0 t1)"
  by (cases "oR j") auto

(* evaluation/seen simplifiers *)
lemmas run_simps   = run.simps
lemmas seenL_simps = seenL_run.simps
lemmas seenR_simps = seenR_run.simps

lemma run_Leaf[simp]:  "run oL oR (Leaf b) = b" by simp
lemma seenL_Leaf[simp]: "seenL_run oL oR (Leaf b) = {}" by simp
lemma seenR_Leaf[simp]: "seenR_run oL oR (Leaf b) = {}" by simp

lemma run_seen_agree_on_triple:
  assumes L: "⋀i. i ∈ seenL_run oL oR T ⟹ oL' i = oL i"
      and R: "⋀j. j ∈ seenR_run oL oR T ⟹ oR' j = oR j"
  shows "(run oL oR T, seenL_run oL oR T, seenR_run oL oR T)
       = (run oL' oR' T, seenL_run oL' oR' T, seenR_run oL' oR' T)"
  using L R
proof (induction T arbitrary: oL oR oL' oR')
  case (Leaf b)
  show ?case by simp

next
  case (AskL i t0 t1)
  (* agreement on the queried index i *)
  have eq_i: "oL' i = oL i"
    using AskL.prems(1) by simp

  (* IH packaged per subtree, guarded by the actual branch condition *)
  have rec_t1:
    "oL i ⟹ (run oL oR t1, seenL_run oL oR t1, seenR_run oL oR t1)
           = (run oL' oR' t1, seenL_run oL' oR' t1, seenR_run oL' oR' t1)"
  proof -
    assume oi: "oL i"
    have Lb: "⋀x. x ∈ seenL_run oL oR t1 ⟹ oL' x = oL x"
      using AskL.prems(1) seenL_sub_AskL by (simp add: oi)
    have Rb: "⋀x. x ∈ seenR_run oL oR t1 ⟹ oR' x = oR x"
      using AskL.prems(2) seenR_eq_AskL by (simp add: oi)
    from AskL.IH(2)[OF Lb Rb] show ?thesis .
  qed

  have rec_t0:
    "¬ oL i ⟹ (run oL oR t0, seenL_run oL oR t0, seenR_run oL oR t0)
            = (run oL' oR' t0, seenL_run oL' oR' t0, seenR_run oL' oR' t0)"
  proof -
    assume noi: "¬ oL i"
    have Lb: "⋀x. x ∈ seenL_run oL oR t0 ⟹ oL' x = oL x"
      using AskL.prems(1) seenL_sub_AskL by (simp add: noi)
    have Rb: "⋀x. x ∈ seenR_run oL oR t0 ⟹ oR' x = oR x"
      using AskL.prems(2) seenR_eq_AskL by (simp add: noi)
    from AskL.IH(1)[OF Lb Rb] show ?thesis .
  qed

  (* combine the two guarded IHs to get the equality on the chosen branch *)
  have rec_if:
    "(run oL oR (if oL i then t1 else t0),
      seenL_run oL oR (if oL i then t1 else t0),
      seenR_run oL oR (if oL i then t1 else t0))
     =
     (run oL' oR' (if oL i then t1 else t0),
      seenL_run oL' oR' (if oL i then t1 else t0),
      seenR_run oL' oR' (if oL i then t1 else t0))"
    by (cases "oL i") (simp add: rec_t1, simp add: rec_t0)

  (* reduce AskL on both sides and use oL' i = oL i for the condition *)
  have LHS_reduce:
    "(run oL oR (AskL i t0 t1),
      seenL_run oL oR (AskL i t0 t1),
      seenR_run oL oR (AskL i t0 t1))
     =
    (run oL oR (if oL i then t1 else t0),
      insert i (seenL_run oL oR (if oL i then t1 else t0)),
      seenR_run oL oR (if oL i then t1 else t0))" by simp
  have RHS_reduce:
    "(run oL' oR' (AskL i t0 t1),
      seenL_run oL' oR' (AskL i t0 t1),
      seenR_run oL' oR' (AskL i t0 t1))
     =
    (run oL' oR' (if oL i then t1 else t0),
      insert i (seenL_run oL' oR' (if oL i then t1 else t0)),
      seenR_run oL' oR' (if oL i then t1 else t0))"
    by (simp add: eq_i)

  show ?case
    using RHS_reduce rec_if by auto

next
  case (AskR j t0 t1)
  (* agreement on the queried index j *)
  have eq_j: "oR' j = oR j"
    using AskR.prems(2) by simp

  (* IH packaged per subtree, guarded by the actual branch condition *)
  have rec_t1:
    "oR j ⟹ (run oL oR t1, seenL_run oL oR t1, seenR_run oL oR t1)
           = (run oL' oR' t1, seenL_run oL' oR' t1, seenR_run oL' oR' t1)"
  proof -
    assume oj: "oR j"
    have Lb: "⋀x. x ∈ seenL_run oL oR t1 ⟹ oL' x = oL x"
      using AskR.prems(1) seenL_eq_AskR by (simp add: oj)
    have Rb: "⋀x. x ∈ seenR_run oL oR t1 ⟹ oR' x = oR x"
      using AskR.prems(2) seenR_sub_AskR by (simp add: oj)
    from AskR.IH(2)[OF Lb Rb] show ?thesis .
  qed

  have rec_t0:
    "¬ oR j ⟹ (run oL oR t0, seenL_run oL oR t0, seenR_run oL oR t0)
            = (run oL' oR' t0, seenL_run oL' oR' t0, seenR_run oL' oR' t0)"
  proof -
    assume noj: "¬ oR j"
    have Lb: "⋀x. x ∈ seenL_run oL oR t0 ⟹ oL' x = oL x"
      using AskR.prems(1) seenL_eq_AskR by (simp add: noj)
    have Rb: "⋀x. x ∈ seenR_run oL oR t0 ⟹ oR' x = oR x"
      using AskR.prems(2) seenR_sub_AskR by (simp add: noj)
    from AskR.IH(1)[OF Lb Rb] show ?thesis .
  qed

  have rec_if:
    "(run oL oR (if oR j then t1 else t0),
      seenL_run oL oR (if oR j then t1 else t0),
      seenR_run oL oR (if oR j then t1 else t0))
     =
     (run oL' oR' (if oR j then t1 else t0),
      seenL_run oL' oR' (if oR j then t1 else t0),
      seenR_run oL' oR' (if oR j then t1 else t0))"
    by (cases "oR j") (simp add: rec_t1, simp add: rec_t0)

  have LHS_reduce:
    "(run oL oR (AskR j t0 t1),
      seenL_run oL oR (AskR j t0 t1),
      seenR_run oL oR (AskR j t0 t1))
     =
    (run oL oR (if oR j then t1 else t0),
      seenL_run oL oR (if oR j then t1 else t0),
      insert j (seenR_run oL oR (if oR j then t1 else t0)))" by simp
  have RHS_reduce:
    "(run oL' oR' (AskR j t0 t1),
      seenL_run oL' oR' (AskR j t0 t1),
      seenR_run oL' oR' (AskR j t0 t1))
     =
    (run oL' oR' (if oR' j then t1 else t0),
      seenL_run oL' oR' (if oR' j then t1 else t0),
      insert j (seenR_run oL' oR' (if oR' j then t1 else t0)))" by simp
  have cond_swap: "(if oR' j then (X::'a) else Y) = (if oR j then X else Y)" for X Y :: 'a
    by (simp add: eq_j)

  show ?case
    using eq_j rec_if by auto
qed

(* KEY LEMMA: If two oracles agree on all queried indices, they get 
   the same result and query the same indices *)
lemma run_agree_on_seen:
  assumes L: "⋀i. i ∈ seenL_run oL oR T ⟹ oL' i = oL i"
      and R: "⋀j. j ∈ seenR_run oL oR T ⟹ oR' j = oR j"
  shows "run oL oR T = run oL' oR' T"
    and  "seenL_run oL oR T = seenL_run oL' oR' T"
    and  "seenR_run oL oR T = seenR_run oL' oR' T"
proof -
  from run_seen_agree_on_triple[OF L R]
  have "(run oL oR T, seenL_run oL oR T, seenR_run oL oR T)
      = (run oL' oR' T, seenL_run oL' oR' T, seenR_run oL' oR' T)" .
  thus "run oL oR T = run oL' oR' T"
    and "seenL_run oL oR T = seenL_run oL' oR' T"
    and "seenR_run oL oR T = seenR_run oL' oR' T" by auto
qed
 (* This is the "unread-agreement" property! *)

(* single-path seen-sets are finite *)
lemma finite_seenL_run[simp]: "finite (seenL_run oL oR T)"
  by (induction T arbitrary: oL oR) auto
lemma finite_seenR_run[simp]: "finite (seenR_run oL oR T)"
  by (induction T arbitrary: oL oR) auto

(* card(seenL) ≤ steps and symmetrically for R *)
lemma card_seenL_le_steps: "card (seenL_run oL oR T) ≤ steps_run oL oR T"
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  let ?S = "seenL_run oL oR (if oL i then t1 else t0)"
  have IH0: "card (seenL_run oL oR t0) ≤ steps_run oL oR t0" by (rule AskL.IH(1))
  have IH1: "card (seenL_run oL oR t1) ≤ steps_run oL oR t1" by (rule AskL.IH(2))
  have br: "card ?S ≤ steps_run oL oR (if oL i then t1 else t0)"
    by (cases "oL i"; simp add: IH0 IH1)
  have fin: "finite ?S"
    by simp
  have "card (seenL_run oL oR (AskL i t0 t1)) = card (insert i ?S)" by simp
  also have "… ≤ Suc (card ?S)" using fin by (simp add: card_insert_if)
  also have "… ≤ Suc (steps_run oL oR (if oL i then t1 else t0))"
    using br by simp
  also have "… = steps_run oL oR (AskL i t0 t1)" by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  have IH0: "card (seenL_run oL oR t0) ≤ steps_run oL oR t0" by (rule AskR.IH(1))
  have IH1: "card (seenL_run oL oR t1) ≤ steps_run oL oR t1" by (rule AskR.IH(2))
  have br: "card (seenL_run oL oR (if oR j then t1 else t0))
            ≤ steps_run oL oR (if oR j then t1 else t0)"
    by (cases "oR j"; simp add: IH0 IH1)
  have "card (seenL_run oL oR (AskR j t0 t1))
        = card (seenL_run oL oR (if oR j then t1 else t0))" by simp
  also have "… ≤ steps_run oL oR (if oR j then t1 else t0)" using br .
  also have "… ≤ Suc (steps_run oL oR (if oR j then t1 else t0))"
    by (simp add: le_SucI)
  also have "… = steps_run oL oR (AskR j t0 t1)" by simp
  finally show ?case .
qed

lemma card_seenR_le_steps: "card (seenR_run oL oR T) ≤ steps_run oL oR T"
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  have IH0: "card (seenR_run oL oR t0) ≤ steps_run oL oR t0" by (rule AskL.IH(1))
  have IH1: "card (seenR_run oL oR t1) ≤ steps_run oL oR t1" by (rule AskL.IH(2))
  have br: "card (seenR_run oL oR (if oL i then t1 else t0))
            ≤ steps_run oL oR (if oL i then t1 else t0)"
    by (cases "oL i"; simp add: IH0 IH1)
  have "card (seenR_run oL oR (AskL i t0 t1))
        = card (seenR_run oL oR (if oL i then t1 else t0))" by simp
  also have "… ≤ steps_run oL oR (if oL i then t1 else t0)" using br .
  also have "… ≤ Suc (steps_run oL oR (if oL i then t1 else t0))"
    by (simp add: le_SucI)
  also have "… = steps_run oL oR (AskL i t0 t1)" by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  let ?S = "seenR_run oL oR (if oR j then t1 else t0)"
  have IH0: "card (seenR_run oL oR t0) ≤ steps_run oL oR t0" by (rule AskR.IH(1))
  have IH1: "card (seenR_run oL oR t1) ≤ steps_run oL oR t1" by (rule AskR.IH(2))
  have br: "card ?S ≤ steps_run oL oR (if oR j then t1 else t0)"
    by (cases "oR j"; simp add: IH0 IH1)
  have fin: "finite ?S"
    by simp
  have "card (seenR_run oL oR (AskR j t0 t1)) = card (insert j ?S)" by simp
  also have "… ≤ Suc (card ?S)" using fin by (simp add: card_insert_if)
  also have "… ≤ Suc (steps_run oL oR (if oR j then t1 else t0))"
    using br by simp
  also have "… = steps_run oL oR (AskR j t0 t1)" by simp
  finally show ?case .
qed

(* Number of queries bounds the number of distinct indices seen *)
lemma steps_ge_sum_seen:
  "steps_run oL oR T ≥ card (seenL_run oL oR T) + card (seenR_run oL oR T)"
  (* Each query step either queries a new index or re-queries an old one *)

(* ========================================================================= *)
(* PART 8: The Coverage Theorem (Lemma 1)                                   *)
(* ========================================================================= *)

text ‹THE ADVERSARIAL ARGUMENT:
  
  If we have a tree T that computes a boolean function "good(oL, oR)" correctly,
  and flipping ANY unread index would change the answer, then ALL indices must
  have been read.
  
  This is the heart of Lemma 1!
›
proof (induction T arbitrary: oL oR)
  case (Leaf b) show ?case by simp
next
  case (AskL i t0 t1)
  let ?SL = "seenL_run oL oR (if oL i then t1 else t0)"
  let ?SR = "seenR_run oL oR (if oL i then t1 else t0)"
  have IH0: "steps_run oL oR t0 ≥ card (seenL_run oL oR t0) + card (seenR_run oL oR t0)"
    by (rule AskL.IH(1))
  have IH1: "steps_run oL oR t1 ≥ card (seenL_run oL oR t1) + card (seenR_run oL oR t1)"
    by (rule AskL.IH(2))
  have br: "steps_run oL oR (if oL i then t1 else t0) ≥ card ?SL + card ?SR"
    by (cases "oL i") (simp_all add: IH0 IH1)
  have fin: "finite ?SL" "finite ?SR"
    by (cases "oL i"; simp)+
  have "card (seenL_run oL oR (AskL i t0 t1)) + card (seenR_run oL oR (AskL i t0 t1))
        = card (insert i ?SL) + card ?SR" by simp
  also have "… ≤ Suc (card ?SL) + card ?SR"
    using fin(1) by (simp add: card_insert_if add_mono)
  also have "… = Suc (card ?SL + card ?SR)" by simp
  also have "… ≤ steps_run oL oR (AskL i t0 t1)"
    using br by simp
  finally show ?case .
next
  case (AskR j t0 t1)
  let ?SL = "seenL_run oL oR (if oR j then t1 else t0)"
  let ?SR = "seenR_run oL oR (if oR j then t1 else t0)"
  have IH0: "steps_run oL oR t0 ≥ card (seenL_run oL oR t0) + card (seenR_run oL oR t0)"
    by (rule AskR.IH(1))
  have IH1: "steps_run oL oR t1 ≥ card (seenL_run oL oR t1) + card (seenR_run oL oR t1)"
    by (rule AskR.IH(2))
  have br: "steps_run oL oR (if oR j then t1 else t0) ≥ card ?SL + card ?SR"
    by (cases "oR j") (simp_all add: IH0 IH1)
  have fin: "finite ?SL" "finite ?SR"
    by (cases "oR j"; simp)+
  have "card (seenL_run oL oR (AskR j t0 t1)) + card (seenR_run oL oR (AskR j t0 t1))
        = card ?SL + card (insert j ?SR)" by simp
  also have "… ≤ card ?SL + Suc (card ?SR)"
    using fin(2) by (simp add: card_insert_if add_mono)
  also have "… = Suc (card ?SL + card ?SR)" by simp
  also have "… ≤ steps_run oL oR (AskR j t0 t1)"
    using br by simp
  finally show ?case .
qed

(* powers-of-two as ints *)
definition pow2_list :: "nat ⇒ int list" where
  "pow2_list n = map (λi. (2::int)^i) [0..<n]"

(* ========================================================================= *)
(* ABSTRACT FLIP-COMPLETE READER MODEL                                      *)
(* ========================================================================= *)

text ‹
  An abstract model of a machine that:
    • interacts with two oracles oL, oR over index sets Lset, Rset,
    • produces a boolean result good oL oR,
    • reads some sets of indices seenL oL oR, seenR oL oR,
    • takes steps oL oR steps,
    • satisfies:
        – unread-agreement: changing only unread indices does nothing,
        – flip-completeness: every index in Lset/Rset can flip the answer
          if we change only that coordinate,
        – steps ≥ number of distinct indices read.
  This is the abstract front-end we will later instantiate with Turing machines.
›


(* ========================================================================= *)
(* PART 9: Ruling Out Polynomial Time                                       *)
(* ========================================================================= *)

(* The rest of the theory shows that if you could solve subset-sum in 
   polynomial time for the distinct-subset-sums family, you'd violate
   the exponential lower bound 2√(2^n) we just proved. *)

locale SubsetSum_Reader_NoK =
  fixes steps :: "int list ⇒ int ⇒ nat"
    and seenL :: "int list ⇒ int ⇒ nat ⇒ int set"
    and seenR :: "int list ⇒ int ⇒ nat ⇒ int set"
  assumes coverage_ex:
    "⋀as s. distinct_subset_sums as ⟹ ∃k≤length as.
       seenL as s k = LHS (e_k as s k) (length as) ∧
       seenR as s k = RHS (e_k as s k) (length as)"
  assumes steps_lb:
    "⋀as s k. steps as s ≥ card (seenL as s k) + card (seenR as s k)"
begin

lemma lemma1_ex:
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "∃k≤n. card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n) ≤ steps as s"
proof -
  obtain k where k_le: "k ≤ n"
    and covL: "seenL as s k = LHS (e_k as s k) n"
    and covR: "seenR as s k = RHS (e_k as s k) n"
    using coverage_ex[OF distinct] n_def by force
  have "card (seenL as s k) + card (seenR as s k) ≤ steps as s"
    by (rule steps_lb)
  hence "card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n) ≤ steps as s"
    by (simp add: covL covR)
  thus ?thesis using k_le by blast
qed

theorem subset_sum_sqrt_lower_bound:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) ≤ real (steps as s)"
proof -
  obtain k where k_le: "k ≤ n" and base:
    "card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n) ≤ steps as s"
    using lemma1_ex[OF n_def distinct] by blast
  have "2 * sqrt ((2::real) ^ n)
        ≤ real (card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n))"
    using lhs_rhs_sum_lower_bound[OF n_def k_le distinct] .
  also have "… ≤ real (steps as s)" using base by simp
  finally show ?thesis .
qed

end  (* SubsetSum_Reader_NoK *)

locale SubsetSum_To_Polytime_NoK =
  SubsetSum_Reader_NoK +
  fixes enc :: "int list ⇒ int ⇒ bool list"
assumes enc_len_poly:
  "∃(C::real)>0. ∃(D::nat).
      ∀as s. distinct_subset_sums as ⟶
        real (length (enc as s)) ≤ C * (real (length as)) ^ D"
assumes steps_poly_of_enc:
  "∃(c::real)>0. ∃(d::nat).
      ∀as s. steps as s ≤ nat (ceiling (c * (real (length (enc as s))) ^ d))"
begin

lemma steps_poly_in_n_on_distinct:
  shows "∃(c'::real)>0. ∃(d'::nat).
           ∀as s n. n = length as ⟶ distinct_subset_sums as ⟶
                    steps as s ≤ nat (ceiling (c' * (real n) ^ d'))"
proof -
  obtain C :: real and D :: nat
    where Cpos: "C > 0"
      and enc_bd:
        "∀as s. distinct_subset_sums as ⟶
           real (length (enc as s)) ≤ C * (real (length as)) ^ D"
    using enc_len_poly by blast
  obtain c :: real and d :: nat
    where cpos: "c > 0"
      and step_bd:
        "∀as s. steps as s ≤ nat (ceiling (c * (real (length (enc as s))) ^ d))"
    using steps_poly_of_enc by blast
  define c' where "c' = c * C ^ d"
  define d' where "d' = D * d"
  have c'pos: "c' > 0" using cpos Cpos by (simp add: c'_def)

  have main:
    "∀as s n. n = length as ⟶ distinct_subset_sums as ⟶
       steps as s ≤ nat (ceiling (c' * (real n) ^ d'))"
  proof (intro allI impI)
    fix as s n assume n_def: "n = length as" and dist: "distinct_subset_sums as"
    have step0: "steps as s ≤ nat (ceiling (c * (real (length (enc as s))) ^ d))"
      using step_bd by blast
    have enc_real: "real (length (enc as s)) ≤ C * (real n) ^ D"
      using enc_bd dist n_def by simp
    have nonneg_x: "0 ≤ real (length (enc as s))" by simp
    have nonneg_y: "0 ≤ C * (real n) ^ D"
      using Cpos by (intro mult_nonneg_nonneg) simp_all
    have pow_mono:
      "(real (length (enc as s))) ^ d ≤ (C * (real n) ^ D) ^ d"
      by (rule power_mono) (use enc_real nonneg_x nonneg_y in auto)
    have mult_mono:
      "c * (real (length (enc as s))) ^ d ≤ c * (C * (real n) ^ D) ^ d"
      using pow_mono cpos by (simp add: mult_left_mono)
    have step1:
      "nat (ceiling (c * (real (length (enc as s))) ^ d))
       ≤ nat (ceiling (c * (C * (real n) ^ D) ^ d))"
      using mult_mono by (intro nat_mono ceiling_mono) simp_all
    from step0 step1
    have "steps as s ≤ nat (ceiling (c * (C * (real n) ^ D) ^ d))" by linarith
    also have "… = nat (ceiling ((c * C ^ d) * (real n) ^ (D * d)))"
      by (simp add: power_mult_distrib mult_ac power_mult)
    finally show "steps as s ≤ nat (ceiling (c' * (real n) ^ d'))"
      by (simp add: c'_def d'_def)
  qed
  show ?thesis using c'pos main by blast
qed

lemma exp_beats_poly_ceiling_strict:
  fixes c :: real and d :: nat
  assumes cpos: "c > 0"
  shows "∃N::nat. ∀n≥N.
           of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
proof -
  (* Eventually: c * n^d ≤ (√2)^n *)
  have ev: "eventually (λn. c * (real n) ^ d ≤ (sqrt 2) ^ n) at_top"
    by real_asymp
  then obtain N1 where N1: "∀n≥N1. c * (real n) ^ d ≤ (sqrt 2) ^ n"
    by (auto simp: eventually_at_top_linorder)
  define N where "N = max N1 1"

  have ceil_le: "of_int (ceiling y) ≤ y + 1" for y :: real by linarith
  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n ≥ N"
    hence nN1: "n ≥ N1" and n_ge1: "n ≥ 1" by (auto simp: N_def)
    from N1 nN1 have bound: "c * (real n) ^ d ≤ (sqrt 2) ^ n" by simp
    have up: "of_int (ceiling (c * (real n) ^ d)) ≤ (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith
    have step: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using n_ge1 by auto
    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    from up step have L: "of_int (ceiling (c * (real n) ^ d)) < 2 * (sqrt 2) ^ n"
      by linarith
    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    with L show "of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)" by simp
  qed
qed

lemma nth_pow2_list:
  assumes "i < n"
  shows "pow2_list n ! i = (2::int)^i"
  using assms by (simp add: pow2_list_def nth_map_upt)

lemma sum_prefix_pow2_list:
  assumes "k ≤ n"
  shows "(∑ i<k. pow2_list n ! i) = (∑ i<k. (2::int)^i)"
  using assms by (simp add: nth_pow2_list)

lemma pow2_gt_sum_prev_int:
  fixes k :: nat
  shows "(∑ i<k. (2::int)^i) < 2^k"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have "(∑ i<Suc k. (2::int)^i) = (∑ i<k. 2^i) + 2^k" by simp
  also have "… < 2^k + 2^k"
    using Suc.IH by (intro add_strict_right_mono)   (* int version *)
  also have "… = 2^(Suc k)" by simp
  finally show ?case .
qed

(* split a {..<n} sum at index k *)
lemma sum_split_at:
  fixes f :: "nat ⇒ 'a::comm_monoid_add"
  assumes "k < n"
  shows "sum f {..<n} = sum f {..<k} + f k + sum f {k+1..<n}"
proof -
(* split {..<n} into {..<k} ⪯ {k..<n} *)
  have part: "{..<n} = {..<k} ∪ {k..<n}"
    using ‹k < n› by auto
  have step1: "sum f {..<n} = sum f {..<k} + sum f {k..<n}"
    by (metis Un_upper1 lessThan_atLeast0 lessThan_subset_iff less_eq_nat.simps(1) 
        part sum.atLeastLessThan_concat)

(* peel k from {k..<n} *)
  have step2set: "{k..<n} = insert k {Suc k..<n}"
    by (metis Suc_leD assms atLeastLessThan_empty atLeastLessThan_empty_iff 
        atLeastLessThan_singleton insert_is_Un ivl_disj_un_two(3) not_less_eq_eq)
  have step2: "sum f {k..<n} = f k + sum f {Suc k..<n}"
    by (subst step2set) simp

(* combine *)
  have "sum f {..<n} = sum f {..<k} + f k + sum f {k+1..<n}"
    using step1 step2 by (metis Suc_eq_plus1 add.assoc)
  show ?thesis
    using ‹sum f {..<n} = sum f {..<k} + f k + sum f {k + 1..<n}› by blast
qed

(* triangle inequality for sums over {..<k} *)
lemma abs_sum_le_sum_abs_upto:
  shows "abs (∑ i<k. (f i::int)) ≤ (∑ i<k. abs (f i))"
  by (rule sum_abs)

(* handy nth fact over a mapped [0..<n] *)
lemma nth_map_upt:
  assumes "k < n"
  shows "(map f [0..<n]) ! k = f k"
  using assms by simp

lemma pow2_list_nth:
  assumes "k < n"
  shows "pow2_list n ! k = (2::int)^k"
  using assms by (simp add: pow2_list_def nth_map_upt)

(* the superincreasing property you want *)
lemma pow2_superincreasing:
  assumes "k < n"
  shows "pow2_list n ! k > (∑ i<k. pow2_list n ! i)"
proof -
  have A: "pow2_list n ! k = (2::int)^k"
    using assms by (simp add: pow2_list_def nth_map_upt)
  have B: "(∑ i<k. pow2_list n ! i) = (∑ i<k. (2::int)^i)"
    using assms by (simp add: sum_prefix_pow2_list)
  show ?thesis
    by (simp add: A B pow2_gt_sum_prev_int)
qed

lemma diff_of_bits:
  fixes x y :: int
  assumes "x ∈ {0,1}" "y ∈ {0,1}" "x ≠ y"
  shows "x - y = 1 ∨ x - y = -1"
  using assms by auto

end

section ‹Cook–Levin: conclude SUBSET-SUM ∉ P (conditional on the bridge)›

lemma sum_lessThan_split_at:
  fixes f :: "nat ⇒ 'a::comm_monoid_add"
  assumes "k < n"
  shows "(∑ i<n. f i) =
         (∑ i<k. f i) + f k + (∑ i = Suc k..<n. f i)"
proof -
  have "{..<n} = {..<k} ∪ {k} ∪ {Suc k..<n}"
    using assms by auto
  moreover have "finite ({..<k}::nat set)" and "finite {k}" and "finite {Suc k..<n}" by simp_all
  moreover have "{..<k} ∩ {k} = {}" and "({..<k} ∪ {k}) ∩ {Suc k..<n} = {}" by auto
  ultimately show ?thesis
    by (metis Un_insert_right add.commute boolean_algebra.disj_zero_right 
        disjoint_insert(1) finite_UnI sum.insert sum_Un_eq)
qed

lemma distinct_subset_sums_pow2_list:
  fixes n :: nat
  shows "distinct_subset_sums (pow2_list n)"
proof -
  let ?as = "pow2_list n"

  have uniq:
    "⋀xs ys. xs ∈ bitvec n ⟹ ys ∈ bitvec n ⟹
             (∑ i<n. ?as!i * xs!i) = (∑ i<n. ?as!i * ys!i) ⟹ xs = ys"
  proof -
    fix xs ys assume xsB: "xs ∈ bitvec n" and ysB: "ys ∈ bitvec n"
      and EQ: "(∑ i<n. ?as!i * xs!i) = (∑ i<n. ?as!i * ys!i)"
    show "xs = ys"
    proof (rule ccontr)
      assume "xs ≠ ys"
      let ?D = "{i. i < n ∧ xs!i ≠ ys!i}"
      have finD: "finite ?D" by simp

      from xsB have xs_len: "length xs = n" and xs01_set: "set xs ⊆ {0,1}"
        by (auto simp: bitvec_def)
      from ysB have ys_len: "length ys = n" and ys01_set: "set ys ⊆ {0,1}"
        by (auto simp: bitvec_def)
      have xs01_i: "⋀i. i < n ⟹ xs!i ∈ {0,1}"
        using xs_len xs01_set by (metis in_mono nth_mem)
      have ys01_i: "⋀i. i < n ⟹ ys!i ∈ {0,1}"
        using ys_len ys01_set by (metis in_mono nth_mem)

      have D_ne: "?D ≠ {}" 
      proof 
        assume "?D = {}" 
        hence "∀i<n. xs!i = ys!i" 
          by auto with xs_len ys_len 
        have "xs = ys" 
          by (intro nth_equalityI) auto with ‹xs ≠ ys› 
        show False by contradiction 
      qed 
      define k where "k = Max ?D" 
      have k_in: "k ∈ ?D" 
        using D_ne Max_in finD k_def by blast 
      hence k_lt: "k < n" and k_diff: "xs!k ≠ ys!k" by auto 
      have agree_after: "⋀i. k < i ⟹ i < n ⟹ xs!i = ys!i" 
        using Max_less_iff finD k_def by blast

      (* Tail after k cancels. *)
      have tail0: "(∑ i∈{k+1..<n}. ?as!i * (xs!i - ys!i)) = 0"
        by (rule sum.neutral) (use agree_after in auto)

      (* Turn EQ into 0 = sum of differences and split at k. *)
      have zero_sum: "0 = (∑ i<n. ?as!i * (xs!i - ys!i))"
        using EQ by (simp add: sum_subtractf algebra_simps)
      have split_k:
        "(∑ i<n. ?as!i * (xs!i - ys!i)) =
           (∑ i<k. ?as!i * (xs!i - ys!i)) + ?as!k * (xs!k - ys!k)
           + (∑ i = Suc k..<n. ?as!i * (xs!i - ys!i))"
        using k_lt by (rule sum_lessThan_split_at)

      from zero_sum split_k tail0
      have eq_abs:
        "abs (?as!k * (xs!k - ys!k))
         = abs (∑ i<k. ?as!i * (xs!i - ys!i))" by simp

      (* Triangle inequality and |xs!i - ys!i| ≤ 1. *)
      have abs_sum_le:
        "abs (∑ i<k. ?as!i * (xs!i - ys!i)) ≤ (∑ i<k. abs (?as!i))"
      proof -
        have "abs (∑ i<k. ?as!i * (xs!i - ys!i))
              ≤ (∑ i<k. abs (?as!i * (xs!i - ys!i)))" by (rule sum_abs)
        also have "… ≤ (∑ i<k. abs (?as!i))"
        proof (rule sum_mono, simp)
          fix i assume ik: "i < k"
          with k_lt have in_n: "i < n" by simp
          have "abs (?as!i * (xs!i - ys!i)) = abs (?as!i) * abs (xs!i - ys!i)"
            by (simp add: abs_mult)
          also have "… ≤ abs (?as!i) * 1"
            using xs01_i[OF in_n] ys01_i[OF in_n] by (intro mult_left_mono) auto
          finally show "abs (?as!i * (xs!i - ys!i)) ≤ abs (?as!i)" by simp
        qed
        finally show ?thesis .
      qed

      (* Drop abs on the prefix because weights are ≥ 0. *)
      have prefix_nonneg: "⋀i. i<k ⟹ 0 ≤ ?as!i"
        using k_lt by (simp add: pow2_list_def)
      have abs_drop: "(∑ i<k. abs (?as!i)) = (∑ i<k. ?as!i)"
        by (rule sum.cong[OF refl]) (use prefix_nonneg in ‹simp›)

      (* Also |xs!k - ys!k| = 1 and weights are ≥ 0. *)
      have abs1: "abs (xs ! k - ys ! k) = 1"
        using xs01_i[OF k_lt] ys01_i[OF k_lt] k_diff by auto
      have nonneg_k: "0 ≤ ?as ! k"
        using k_lt by (simp add: pow2_list_def)
      have abs_prod: "abs (?as!k * (xs ! k - ys ! k)) = ?as!k"
        by (simp add: abs_mult abs1 nonneg_k)

      (* pointwise bound: for every i<k, |a_i * (xs_i - ys_i)| ≤ |a_i| *)
      have term_le:
        "⋀i. i < k ⟹ abs (?as!i * (xs ! i - ys ! i)) ≤ abs (?as!i)"
      proof -
        fix i assume ik: "i < k"
        then have in_n: "i < n" using k_lt by simp
        have diff_le1: "abs (xs ! i - ys ! i) ≤ (1::int)"
          using xs01_i[OF in_n] ys01_i[OF in_n] by auto
        have "abs (?as!i * (xs ! i - ys ! i))
          = abs (?as!i) * abs (xs ! i - ys ! i)" by (simp add: abs_mult)
        also have "… ≤ abs (?as!i) * 1"
          using diff_le1 by (intro mult_left_mono) simp_all
        finally show "abs (?as!i * (xs ! i - ys ! i)) ≤ abs (?as!i)" by simp
      qed

(* now the chain for main_le goes through *)
      have main_le: "?as!k ≤ (∑ i<k. ?as!i)"
      proof -
        have "?as!k = abs (?as!k * (xs ! k - ys ! k))" by (simp add: abs_prod)
        also have "… = abs (∑ i<k. ?as!i * (xs ! i - ys ! i))" using eq_abs by simp
        also have "… ≤ (∑ i<k. abs (?as!i * (xs ! i - ys ! i)))" by (rule sum_abs)
        also have "… ≤ (∑ i<k. abs (?as!i))"
          by (intro sum_mono term_le) simp
        also have "… = (∑ i<k. ?as!i)" by (simp add: abs_drop)
        finally show ?thesis .
      qed

      (* Rewrite both sides as powers of 2. *)
      have lhs_pow: "?as!k = (2::int)^k"
        using k_lt by (simp add: pow2_list_def)
      have rhs_pow: "(∑ i<k. ?as!i) = (∑ i<k. (2::int)^i)"
      proof (rule sum.cong[OF refl])
        fix i assume "i ∈ {..<k}"
        with k_lt have "i < n" by auto
        thus "?as!i = (2::int)^i" by (simp add: pow2_list_def)
      qed

      have "(2::int)^k ≤ (∑ i<k. (2::int)^i)"
        using main_le by (simp add: lhs_pow rhs_pow)

      (* Final contradiction via closed form. *)
      hence "(2::int)^k ≤ (2::int)^k - 1"
        by (simp add: sum_pow2_int)
      thus False by linarith
    qed
  qed

(* length of the weight list is n, so the binders match *)
  have len_as[simp]: "length ?as = n" by (simp add: pow2_list_def)

  show ?thesis
    unfolding distinct_subset_sums_def
    by (simp; metis uniq)
qed

end
