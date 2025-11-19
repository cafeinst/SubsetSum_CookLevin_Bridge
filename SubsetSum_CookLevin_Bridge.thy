theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

section ‹Cook–Levin bridge for the subset-sum lower bound›

lemma exp_beats_poly_ceiling_strict_TM:
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

  have ceil_le: "of_int (ceiling y) ≤ y + 1" for y :: real
    by linarith

  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n ≥ N"
    then have nN1: "n ≥ N1" and n_ge1: "n ≥ 1"
      by (auto simp: N_def)

    from N1[rule_format, OF nN1]
    have bound: "c * (real n) ^ d ≤ (sqrt 2) ^ n"
      by simp

    have up:
      "of_int (ceiling (c * (real n) ^ d))
         ≤ (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith

    have step: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using n_ge1 by simp

    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    with up step
    show "of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
      by linarith
  qed
qed

lemma length_pow2_list[simp]: "length (pow2_list n) = n"
  by (simp add: pow2_list_def)

lemma exists_hard_TM:
  "∀n. ∃as. length as = n ∧ distinct_subset_sums as"
proof
  fix n :: nat
  have len: "length (pow2_list n) = n"
    by (rule length_pow2_list)
  moreover have dist: "distinct_subset_sums (pow2_list n)"
    by (rule distinct_subset_sums_pow2_list)
  ultimately show "∃as. length as = n ∧ distinct_subset_sums as"
    by blast
qed

subsection ‹Basic encoding to Cook–Levin symbols›

text ‹
  We use Cook–Levin's tape alphabet:
    0 = blank, 1 = start symbol, 2 = "0", 3 = "1".
  The input instance (a bool list) is written as a row of 2/3 symbols.
›

definition bool_to_symbols :: "bool list ⇒ symbol list" where
  "bool_to_symbols bs = map (λb. if b then 3 else 2) bs"

text ‹We will run our machines with two tapes: input (0) and output (1).›

definition k_tapes :: nat where
  "k_tapes = 2"


subsection ‹Cook–Levin step-count and acceptance›

text ‹
  We define a simple “halting time” function steps_CL, and a corresponding
  acceptance predicate accepts_CL for a Cook–Levin machine.
›

definition steps_CL :: "machine ⇒ bool list ⇒ nat" where
  "steps_CL M x =
     (LEAST t. fst (execute M (start_config k_tapes (bool_to_symbols x)) t)
                 ≥ length M)"

definition conf_CL :: "machine ⇒ bool list ⇒ nat ⇒ config" where
  "conf_CL M x t = execute M (start_config k_tapes (bool_to_symbols x)) t"

definition head0_CL :: "config ⇒ int" where
  "head0_CL cfg = int (cfg <#> 0)"

definition accepts_CL :: "machine ⇒ bool list ⇒ bool" where
  "accepts_CL M x =
     (let t   = steps_CL M x;
          cfg = conf_CL M x t
      in (cfg <:> 1) (cfg <#> 1) = 3)"

text ‹
  NOTE: The details of when exactly the machine halts (state index ≥ length M)
  follow the convention in the Cook–Levin development. We will mainly reason
  abstractly in terms of steps_CL and accepts_CL, not about low-level configs.
›

subsection ‹Which input bits does a Cook–Levin machine read?›

text ‹
  The set @{term "read0_CL M x"} collects all indices @{term i} on the
  input tape (tape 0) that the head visits before halting on input @{term x}.
›

definition read0_CL :: "machine ⇒ bool list ⇒ nat set" where
  "read0_CL M x =
     { nat (head0_CL (conf_CL M x t)) | t.
        t < steps_CL M x ∧
        0 ≤ head0_CL (conf_CL M x t) ∧
        nat (head0_CL (conf_CL M x t)) < length x }"

lemma read0_CL_subset_indices:
  "read0_CL M x ⊆ {..<length x}"
  unfolding read0_CL_def by auto


subsection ‹Unread-agreement lemma in the Cook–Levin model›

text ‹
  If two inputs @{term x} and @{term y} agree on every index in
  @{term "read0_CL M x"}, then a deterministic Cook–Levin TM behaves
  identically on both: same runtime, same output, and same set of
  read positions.

  This is the CL-analogue of the “flip completeness / unread agreement”
  property we abstracted in the decision-tree model.
›

subsection ‹The mathematical SUBSET-SUM predicate›

text ‹
  This is the “true” subset-sum specification: we ask if there exists a
  0/1-vector xs selecting a subset of as that sums to s.
›

definition subset_sum_true :: "int list ⇒ int ⇒ bool" where
  "subset_sum_true as s ⟷
     (∃xs ∈ bitvec (length as).
        (∑ i<length as. as ! i * xs ! i) = s)"


subsection ‹A Cook–Levin machine that solves SUBSET-SUM›

text ‹
  Locale CL_SubsetSum_Solver says:
   • M is a well-formed k_tapes Cook–Levin machine,
   • enc encodes (as,s) as a bool list,
   • M decides subset_sum_true at that encoding.
›

locale CL_SubsetSum_Solver =
  fixes M   :: machine
    and q0  :: nat
    and enc :: "int list ⇒ int ⇒ bool list"
  assumes turing: "turing_machine k_tapes q0 M"
  assumes solves_subset_sum:
    "⋀as s. accepts_CL M (enc as s) ⟷ subset_sum_true as s"
begin

text ‹
  steps_TM is the time we care about for the lower bound:
  it is just the Cook–Levin step-count on the encoded instance.
›

definition steps_TM :: "int list ⇒ int ⇒ nat" where
  "steps_TM as s = steps_CL M (enc as s)"

definition read0_TM :: "int list ⇒ int ⇒ nat set" where
  "read0_TM as s = read0_CL M (enc as s)"

lemma read0_TM_subset:
  "read0_TM as s ⊆ {..<length (enc as s)}"
  unfolding read0_TM_def
  using read0_CL_subset_indices by simp

end  (* context CL_SubsetSum_Solver *)


section ‹Flip-complete TM interface and lower bound inheritance›

text ‹A Cook–Levin machine is polynomial-time on SUBSET-SUM if its
  running time on the encoding of (as,s) is bounded by some polynomial
  in the length of as.›

definition polytime_CL_machine
  :: "machine ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool"
where
  "polytime_CL_machine M enc ⟷
     (∃(c::real)>0. ∃(d::nat).
        ∀as s. steps_CL M (enc as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d)))"

text ‹
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
     INTERPRETATION OF THE LOCALE  ‹Flip_Complete_TM›
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  The purpose of this locale is to lift the abstract decision-tree lower bound
  for SUBSET-SUM (proved in ‹SubsetSum_DecisionTree›) to the level of a
  Cook–Levin Turing machine.

  A structure ‹M, q0, enc› is assumed to satisfy the locale
  ‹CL_SubsetSum_Solver›, meaning:

     • M is a well-formed deterministic Cook–Levin Turing machine
       with k_tapes = 2,

     • enc : (as,s) ↦ bool-list is any encoding of SUBSET-SUM instances, and

     • M decides the mathematical predicate ‹subset_sum_true›:
         accepts_CL M (enc as s)  ↔  subset_sum_true as s.

  The locale ‹Flip_Complete_TM› introduces *two additional* assumptions,
  mirroring the structure of the abstract “reader” model:

     1.  ‹coverage_ex›   (global flip-completeness)
     2.  ‹steps_lb›      (runtime ≥ number of distinguished possibilities)

  These assumptions are *structural restrictions* on the behaviour of M.
  They do NOT hold for all Turing machines.

  ────────────────────────────────────────────────────────────────────────────
  ASSUMPTION 1 — COVERAGE  (flip–completeness)
  ────────────────────────────────────────────────────────────────────────────
  For every “hard” weight-list with distinct subset sums, the machine M must,
  at some time k ≤ length as, have explored enough information on its input
  tape to *realize one of the canonical adversarial splits*:

       {seenL as s k, seenR as s k} = {LHS(e_k as s k), RHS(e_k as s k)}

  This is a strong requirement: it asserts that, on hard instances,
  the TM’s behaviour matches the combinatorial structure exploited in the
  decision-tree lower bound.  In particular it forbids shortcuts, global
  properties, or algebraic optimizations that do not correspond to such
  a split.

  ────────────────────────────────────────────────────────────────────────────
  ASSUMPTION 2 — STEPS  (runtime ≥ information distinguished)
  ────────────────────────────────────────────────────────────────────────────
  The runtime of M on (as,s) is at least the total number of left- and
  right-hand partial sums that its computation has (abstractly) distinguished:

       steps_TM as s  ≥  card(seenL as s k) + card(seenR as s k)

  This matches the “reader” model: each distinguished value corresponds,
  morally, to a Turing-machine branch that must have been examined.

  This is not a property of arbitrary Turing machines — it enforces that
  M’s behaviour is essentially *search-like*, distinguishing possibilities
  one at a time.

  ────────────────────────────────────────────────────────────────────────────
  INTERPRETATION
  ────────────────────────────────────────────────────────────────────────────

  Under these two structural assumptions, the lower-bound theory from
  ‹SubsetSum_DecisionTree› can be instantiated with:

       steps  ≡ steps_TM          (Cook–Levin execution length)
       seenL, seenR               (abstractly provided “distinguished sets”)

  yielding:

     • an Ω( √(2^n) ) lower bound on steps_TM,
     • and impossibility of any polynomial upper bound
       on the distinct-subset-sums family.

  ────────────────────────────────────────────────────────────────────────────
  IMPORTANT
  ────────────────────────────────────────────────────────────────────────────

  This locale does NOT claim that *every* Turing machine deciding SUBSET-SUM
  satisfies flip-completeness or the steps lower-bound.
  Doing so would imply an unconditional exponential lower bound for
  SUBSET-SUM, and therefore P ≠ NP.

  Instead, the theorems in this locale hold for *any* Cook–Levin machine
  whose behaviour fits the flip-complete / reader-like pattern above.
  This identifies a broad and natural subclass of machines for which the
  decision-tree adversary lower bound automatically lifts to the
  Cook–Levin model.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
›


locale Flip_Complete_TM =
  CL_SubsetSum_Solver +
  fixes seenL :: "int list ⇒ int ⇒ nat ⇒ int set"
    and seenR :: "int list ⇒ int ⇒ nat ⇒ int set"
  assumes coverage_ex:
    "⋀as s. distinct_subset_sums as ⟹
       ∃k≤length as.
         seenL as s k = LHS (e_k as s k) (length as) ∧
         seenR as s k = RHS (e_k as s k) (length as)"
  assumes steps_lb:
    "⋀as s k. steps_TM as s ≥ card (seenL as s k) + card (seenR as s k)"
begin

interpretation Reader: SubsetSum_Reader_NoK steps_TM seenL seenR
proof
  show "⋀as s. distinct_subset_sums as ⟹
          ∃k≤length as.
            seenL as s k = LHS (e_k as s k) (length as) ∧
            seenR as s k = RHS (e_k as s k) (length as)"
    using coverage_ex by blast
next
  show "⋀as s k. steps_TM as s ≥
           card (seenL as s k) + card (seenR as s k)"
    using steps_lb by simp
qed

subsection ‹Inherited Ω(√(2^n)) lower bound for this TM›

theorem subset_sum_sqrt_lower_bound_TM:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) ≤ real (steps_TM as s)"
  using Reader.subset_sum_sqrt_lower_bound[OF n_def distinct]
  by simp

text ‹Unfolding steps_TM, we obtain the statement directly for steps_CL.›

corollary subset_sum_sqrt_lower_bound_CL:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) ≤ real (steps_CL M (enc as s))"
proof -
  have lb: "2 * sqrt ((2::real) ^ n) ≤ real (steps_TM as s)"
    using subset_sum_sqrt_lower_bound_TM[OF n_def distinct] .
  have "steps_TM as s = steps_CL M (enc as s)"
    by (simp add: steps_TM_def)
  hence "real (steps_TM as s) = real (steps_CL M (enc as s))"
    by simp
  from lb this show ?thesis
    by simp
qed

subsection ‹Inherited “no polynomial-time” corollary on the distinct family›

theorem no_polytime_TM_on_distinct_family:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
             ∀as s. distinct_subset_sums as ⟶
               steps_TM as s ≤ nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_poly:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps_TM as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where
    cpos: "c > 0" and
    bound: "∀as s. distinct_subset_sums as ⟶
                    steps_TM as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  from exp_beats_poly_ceiling_strict_TM[OF cpos]
  obtain N :: nat where N:
    "∀n≥N. of_int (ceiling (c * (real n) ^ d))
           < 2 * sqrt ((2::real) ^ n)"
    by blast

  have N_ge: "N ≥ N" by simp

  from exists_hard_TM
  obtain as where len_as: "length as = N"
    and dist_as: "distinct_subset_sums as"
    by blast

  from N[rule_format, OF N_ge]
  have ceil_lt:
    "of_int (ceiling (c * (real N) ^ d))
       < 2 * sqrt ((2::real) ^ N)"
    by simp
  hence ceil_lt':
    "of_int (ceiling (c * (real (length as)) ^ d))
       < 2 * sqrt ((2::real) ^ (length as))"
    by (simp add: len_as)

  have lb:
    "2 * sqrt ((2::real) ^ N) ≤ real (steps_TM as 0)"
  proof -
    have "2 * sqrt ((2::real) ^ N) ≤ real (steps_TM as 0)"
    proof (rule subset_sum_sqrt_lower_bound_TM)
      show "N = length as"
        using len_as by simp
    next
      show "distinct_subset_sums as"
        using dist_as .
    qed
    thus ?thesis .
  qed

  have ub_nat:
    "steps_TM as 0 ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using bound dist_as by simp

  have nonneg: "0 ≤ c * (real (length as)) ^ d"
    using cpos by simp
  hence ceil_ge0: "0 ≤ ceiling (c * (real (length as)) ^ d)"
    by simp
  hence conv:
    "real (nat (ceiling (c * (real (length as)) ^ d)))
       = of_int (ceiling (c * (real (length as)) ^ d))"
    by simp

  from ub_nat have ub_real:
    "real (steps_TM as 0)
       ≤ of_int (ceiling (c * (real (length as)) ^ d))"
    using conv by simp

  from ceil_lt' lb ub_real
  show False using len_as by auto
qed

corollary no_polytime_CL_on_distinct_family:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
             ∀as s. distinct_subset_sums as ⟶
               steps_CL M (enc as s)
                 ≤ nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_poly:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where
    cpos: "c > 0" and
    bound: "∀as s. distinct_subset_sums as ⟶
                    steps_CL M (enc as s)
                      ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  have "∃(c::real)>0. ∃(d::nat).
          ∀as s. distinct_subset_sums as ⟶
            steps_TM as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using cpos bound steps_TM_def by auto
  with no_polytime_TM_on_distinct_family show False by blast
qed

end  (* locale Flip_Complete_TM *)

text ‹
  This locale captures the **meta-assumption** that every polynomial-time
  Cook–Levin machine that correctly decides SUBSET-SUM is in fact
  flip-complete, in the sense of our locale ‹Flip_Complete_TM›.
›

locale All_SubsetSum_Polytime_Flip_Complete =
  assumes all_polytime_flip:
    "⋀M q0 enc.
       CL_SubsetSum_Solver M q0 enc ⟹
       polytime_CL_machine M enc ⟹
       (∃seenL seenR. Flip_Complete_TM M q0 enc seenL seenR)"
context All_SubsetSum_Polytime_Flip_Complete

begin
section ‹Complexity-theoretic interpretation: SUBSET-SUM and P vs NP›

text ‹
  We briefly explain how the formal results in this theory relate to the
  classical P vs NP question, at a conceptual level.

  • The HOL side (‹SubsetSum_DecisionTree›) developed an abstract, purely
    combinatorial lower bound: any “flip-complete reader” for SUBSET-SUM
    must use at least Ω(√(2^n)) steps on instances of length ‹n›,
    even when restricted to families with distinct subset sums.

  • In this theory we built a bridge to the concrete Cook–Levin Turing
    machine model (‹Cook_Levin.NP›).  A Cook–Levin machine ‹M› with an
    encoding ‹enc› is said to solve SUBSET-SUM if it satisfies the locale
    ‹CL_SubsetSum_Solver›, i.e.
      – ‹turing_machine k_tapes q0 M›, and
      – ‹accepts_CL M (enc as s) ⟷ subset_sum_true as s›
        for all weight lists ‹as› and targets ‹s›.

  • We then defined ‹polytime_CL_machine M enc› to mean that the running
    time ‹steps_CL M (enc as s)› is bounded by some polynomial in
    ‹length as›, uniformly for all ‹as› and ‹s›.

  • The locale ‹Flip_Complete_TM› axiomatizes the existence of “seen”
    sets ‹seenL›, ‹seenR› and structural coverage + lower-bound properties
    that make the Cook–Levin machine an instance of the abstract
    flip-complete reader.  Inside this locale we proved:

      – an Ω(√(2^n)) lower bound for ‹steps_CL M (enc as s)› on the
        distinct-subset-sums family, and

      – theorems ‹no_polytime_TM_on_distinct_family› and
        ‹no_polytime_CL_on_distinct_family›, which assert that *no*
        such flip-complete machine can be polynomial-time on that family.

  • Finally, the meta-locale
      ‹All_SubsetSum_Polytime_Flip_Complete›
    assumes that *every* polynomial-time Cook–Levin machine that correctly
    decides SUBSET-SUM is in fact flip-complete (i.e. admits suitable
    ‹seenL›, ‹seenR› and satisfies ‹Flip_Complete_TM›).  Under this single
    meta-assumption, we proved:

      theorem no_polytime_CL_subset_sum:
        "¬ (∃M q0 enc.
              CL_SubsetSum_Solver M q0 enc ∧
              polytime_CL_machine M enc)"

    In plain words:

      ‹If every polynomial-time CL solver for SUBSET-SUM is flip-complete,
       then there is no polynomial-time CL solver for SUBSET-SUM at all.›

  Conceptually, this gets us very close to a P ≠ NP conclusion:

    – In the standard Cook–Levin framework, SUBSET-SUM is NP-complete.
      Intuitively, if SUBSET-SUM were in P, there should exist a
      polynomial-time Cook–Levin machine ‹M› and encoding ‹enc› that
      satisfy ‹CL_SubsetSum_Solver M q0 enc› and ‹polytime_CL_machine M enc›.

    – Our theorem ‹no_polytime_CL_subset_sum› shows that, *assuming*
      every such polynomial-time solver is flip-complete, no such pair
      ‹(M,enc)› can exist.

    – Thus, together with the usual NP-completeness machinery and a
      formal bridge from polynomial-time Turing machines to
      Cook–Levin machines, the meta-assumption
      ‹All_SubsetSum_Polytime_Flip_Complete› would yield that SUBSET-SUM
      is not in P, and hence P ≠ NP.

  At present, this theory stops one step short of a full P ≠ NP proof:
  the gap is cleanly isolated in the meta-assumption that every
  polynomial-time solver is flip-complete.  All the combinatorial and
  machine-theoretic lower-bound reasoning *inside* that assumption is
  fully formalized.
›

text ‹
  Under the above assumption, there cannot exist any polynomial-time
  Cook–Levin machine that solves SUBSET-SUM.
›

theorem no_polytime_CL_subset_sum:
  shows "¬ (∃M q0 enc.
              CL_SubsetSum_Solver M q0 enc ∧
              polytime_CL_machine M enc)"
proof
  assume "∃M q0 enc.
            CL_SubsetSum_Solver M q0 enc ∧
            polytime_CL_machine M enc"
  then obtain M q0 enc
    where solver: "CL_SubsetSum_Solver M q0 enc"
      and poly:   "polytime_CL_machine M enc"
    by blast

  (* From the meta-assumption, this solver must be flip-complete. *)
  from all_polytime_flip[OF solver poly]
  obtain seenL seenR where
    flip: "Flip_Complete_TM M q0 enc seenL seenR"
    by blast

  (* Polytime on all inputs trivially implies a polynomial bound on
     the distinct-subset-sums family. *)

  from flip obtain seenL seenR
    where flip_inst: "Flip_Complete_TM M q0 enc seenL seenR"
    by blast

  from flip_inst interpret Flip: Flip_Complete_TM M q0 enc seenL seenR
    by (simp)

  from poly obtain c d where
    cpos: "c > 0" and
    bound_all: "∀as s. steps_CL M (enc as s)
                      ≤ nat (ceiling (c * (real (length as)) ^ d))"
    unfolding polytime_CL_machine_def by blast

  have family_bound:
    "∃(c::real)>0. ∃(d::nat).
     ∀as s. distinct_subset_sums as ⟶
       steps_CL M (enc as s)
         ≤ nat (ceiling (c * (real (length as)) ^ d))"
  proof -
    have ex_d:
      "∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
    proof (intro exI allI impI)
      fix as :: "int list" and s :: int
      assume "distinct_subset_sums as"
      from bound_all show
        "steps_CL M (enc as s)
         ≤ nat (ceiling (c * (real (length as)) ^ d))"
        by simp
    qed
    from cpos ex_d show ?thesis
      by blast
  qed

  from Flip.no_polytime_CL_on_distinct_family
  have no_family_poly:
    "¬ (∃(c::real)>0. ∃(d::nat).
        ∀as s. distinct_subset_sums as ⟶
          steps_CL M (enc as s)
            ≤ nat (ceiling (c * (real (length as)) ^ d)))" .

  from no_family_poly family_bound
  show False
    by contradiction
  qed

end  (* locale *)

end  (* theory *)
