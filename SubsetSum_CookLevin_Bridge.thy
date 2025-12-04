theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

section ‹Cook–Levin bridge for the subset-sum lower bound›

text ‹
  This theory connects the abstract decision-tree lower bound from
  SubsetSum_DecisionTree to the concrete Cook–Levin Turing-machine model
  of Cook_Levin.NP.

  On the decision-tree side, the locale SubsetSum_Lemma1 assumes only:

    • coverage: on every “hard” instance with distinct subset sums there is
      a split index k where the solver’s information flow matches the
      canonical partial-sum sets LHS (e_k as s k) and RHS (e_k as s k);

    • cost: each distinguishable L- or R-value costs at least one unit of work,
      i.e. steps ≥ card (seenL as s k) + card (seenR as s k).

  From these assumptions, SubsetSum_Lemma1 derives the abstract lower bound

      2 * sqrt ((2::real) ^ n) ≤ real (steps as s)

  for all hard instances (as,s) of length n = length as.

  The aim of the present file is to transport this combinatorial result into
  the Cook–Levin world:

    • we define a step-count steps_CL and an acceptance predicate
      accepts_CL for Cook–Levin machines;

    • we specify the mathematical SUBSET-SUM predicate subset_sum_true and
      an abstract verifier locale SS_Verifier_NP, which allows us to show
      SUBSETSUM_lang enc0 ∈ 𝒩𝒫 for suitable encodings enc0;

    • we introduce the locale CL_SubsetSum_Solver for Cook–Levin machines
      that decide SUBSET-SUM via some encoding enc;

    • we finally define a Cook–Levin side interface LR_Read_TM, which adds
      the “read-all-values” assumptions needed to instantiate the abstract
      lower-bound locale SubsetSum_Lemma1 with the concrete step-count
      steps_TM as s = steps_CL M (enc as s).

  Inside LR_Read_TM we inherit the abstract √(2ⁿ) lower bound and obtain
  “no polynomial-time bound on the hard family” corollaries for any machine
  satisfying the LR-read assumptions.
›

text ‹
  As a preparatory step, we state an elementary analytic fact in the exact
  numerical form needed later: ceiling-bounded polynomials are eventually
  dominated by the function n ↦ 2 * sqrt (2^n).
›
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

  (* Simple ceiling bound: ⌈y⌉ ≤ y + 1 *)
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

text ‹
  For each length n we choose a canonical “hard” weight list, namely
  pow2_list n.  These lists have distinct subset sums and mirror the hard
  family used in the decision-tree lower bound.
›
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

    • 0 = blank,
    • 1 = start symbol,
    • 2 = symbol for bit 0,
    • 3 = symbol for bit 1.

  An input bitstring is written as a row of 2/3 symbols on tape 0.
›

definition bool_to_symbols :: "bool list ⇒ symbol list" where
  "bool_to_symbols bs = map (λb. if b then 3 else 2) bs"

text ‹We fix two tapes: input (0) and output (1).›

definition k_tapes :: nat where
  "k_tapes = 2"


subsection ‹Cook–Levin step-count and acceptance›

text ‹
  We define a simple halting-time function steps_CL and an acceptance
  predicate accepts_CL for Cook–Levin machines:

    • steps_CL M x is the least step t where the control state index
      is at least length M (the halting convention of Cook_Levin.NP);

    • conf_CL M x t is the configuration after t steps;

    • accepts_CL M x says that at time steps_CL M x, the symbol under
      the head on tape 1 is 3, i.e. the machine outputs “1”.
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
  We will reason about Cook–Levin machines mainly via steps_CL and
  accepts_CL, without unfolding the low-level configuration details.
›


subsection ‹Which input bits does a Cook–Levin machine read?›

text ‹
  The set read0_CL M x collects all indices on the input tape (tape 0)
  that the head visits before halting on input x.  This abstracts away
  from the timing of visits and just records which input positions the
  machine has actually inspected.
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


subsection ‹The mathematical SUBSET-SUM predicate›

text ‹
  We now introduce the “true” SUBSET-SUM predicate, independent of any
  machine or encoding.  It asks whether there exists a 0/1-vector xs
  selecting a subset of as that sums to the target s.
›

definition subset_sum_true :: "int list ⇒ int ⇒ bool" where
  "subset_sum_true as s ⟷
     (∃xs ∈ bitvec (length as).
        (∑ i<length as. as ! i * xs ! i) = s)"


subsection ‹Certificate-based view of SUBSET-SUM›

text ‹
  A natural certificate for SUBSET-SUM is a 0/1-vector xs of length
  length as indicating which elements are chosen.  The predicate
  ss_cert_ok as s xs states that:

    • xs has the right length;
    • all entries are 0 or 1;
    • the weighted sum equals s.

  We show that this certificate notion is equivalent to subset_sum_true.
›

definition ss_cert_ok :: "int list ⇒ int ⇒ int list ⇒ bool" where
  "ss_cert_ok as s xs ⟷
     length xs = length as ∧
     set xs ⊆ {0,1} ∧
     (∑ i<length as. as ! i * xs ! i) = s"

lemma subset_sum_true_iff_cert:
  "subset_sum_true as s ⟷ (∃xs. ss_cert_ok as s xs)"
proof
  assume "subset_sum_true as s"
  then obtain xs where
    xs_bitvec: "xs ∈ bitvec (length as)" and
    sum_eq:     "(∑ i<length as. as ! i * xs ! i) = s"
    unfolding subset_sum_true_def by blast
  hence len: "length xs = length as"
    and vals: "set xs ⊆ {0,1}"
    unfolding bitvec_def by auto
  hence "ss_cert_ok as s xs"
    unfolding ss_cert_ok_def using sum_eq by simp
  thus "∃xs. ss_cert_ok as s xs"
    by blast
next
  assume "∃xs. ss_cert_ok as s xs"
  then obtain xs where
    ok: "ss_cert_ok as s xs"
    by blast
  from ok have len: "length xs = length as"
    and vals: "set xs ⊆ {0,1}"
    and sum_eq: "(∑ i<length as. as ! i * xs ! i) = s"
    unfolding ss_cert_ok_def by auto
  hence "xs ∈ bitvec (length as)"
    unfolding bitvec_def by auto
  thus "subset_sum_true as s"
    unfolding subset_sum_true_def
    using sum_eq by blast
qed

subsection ‹SUBSET-SUM is in NP (via an abstract verifier)›

text ‹
  We now introduce an abstract verifier locale that matches the
  Cook_Levin.NP characterization of NP.

  A verifier instance consists of:

    • an instance encoding enc0 :: int list ⇒ int ⇒ string,
    • a certificate encoding enc_cert :: int list ⇒ int ⇒ int list ⇒ string,
    • a Turing machine V computing a function fverify,
    • a polynomial bound p on certificate length as a function of
      instance length, and
    • a time bound T.

  The locale assumptions express that V is a correct NP-style verifier
  for SUBSET-SUM with respect to enc0 and enc_cert: any true instance has a
  certificate that leads to acceptance, and any accepting computation
  corresponds to a correct certificate.
›

locale SS_Verifier_NP =
  fixes k G V p T fverify enc0 enc_cert
  assumes V_tm:
    "turing_machine k G V"
  assumes p_poly:
    "polynomial p"
  assumes T_poly:
    "big_oh_poly T"
  assumes V_time:
    "computes_in_time k V fverify T"
  assumes V_outlen:
    "⋀y. length (fverify y) = 1"
  assumes V_complete:
    "⋀as s. subset_sum_true as s ⟹
       ∃xs.
         ss_cert_ok as s xs ∧
         length (enc_cert as s xs) = p (length (enc0 as s)) ∧
         fverify ⟨enc0 as s, enc_cert as s xs⟩ = [𝕀]"
  assumes V_sound:
    "⋀as s u.
       fverify ⟨enc0 as s, u⟩ = [𝕀] ⟹
       length u = p (length (enc0 as s)) ⟹
       ∃xs. ss_cert_ok as s xs ∧ u = enc_cert as s xs"
  assumes V_wf:
    "⋀x u. fverify ⟨x, u⟩ = [𝕀] ⟹ ∃as s. x = enc0 as s"


section ‹SUBSET-SUM as a language›

text ‹
  From an instance encoding function enc0 we obtain the language

      SUBSETSUM_lang enc0

  consisting of all strings that encode a true SUBSET-SUM instance.
›

definition SUBSETSUM_lang :: "(int list ⇒ int ⇒ string) ⇒ language" where
  "SUBSETSUM_lang enc0 ≡
     {x. ∃as s. x = enc0 as s ∧ subset_sum_true as s}"

subsection ‹SUBSET-SUM is in NP (relative to enc0)›

text ‹
  The next lemma packages the ‹SS_Verifier_NP› locale into the
  alternative NP characterization ‹NP_output_len_1› from ‹Cook_Levin.NP›.
  It shows that any suitable verifier induces a language
  ‹SUBSETSUM_lang enc0› in ‹𝒩𝒫›.
›
lemma SUBSETSUM_in_NP_from_verifier:
  fixes k G V p T fverify enc0 enc_cert
  assumes verif: "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
proof -
  interpret V: SS_Verifier_NP k G V p T fverify enc0 enc_cert
    using verif .

  have witness:
    "∃k G M p T fver.
       turing_machine k G M ∧
       polynomial p ∧
       big_oh_poly T ∧
       computes_in_time k M fver T ∧
       (∀y. length (fver y) = 1) ∧
       (∀x. x ∈ SUBSETSUM_lang enc0 ⟷
              (∃u. length u = p (length x) ∧ fver ⟨x, u⟩ = [𝕀]))"
  proof (intro exI conjI)
    show "turing_machine k G V"
      by (rule V.V_tm)
    show "polynomial p"
      by (rule V.p_poly)
    show "big_oh_poly T"
      by (rule V.T_poly)
    show "computes_in_time k V fverify T"
      by (rule V.V_time)
    show "∀y. length (fverify y) = 1"
      using V.V_outlen by simp

    show "∀x. x ∈ SUBSETSUM_lang enc0 ⟷
              (∃u. length u = p (length x) ∧ fverify ⟨x, u⟩ = [𝕀])"
    proof
      fix x :: string
      show "x ∈ SUBSETSUM_lang enc0 ⟷
              (∃u. length u = p (length x) ∧ fverify ⟨x, u⟩ = [𝕀])"
      proof
        (* (⇒) completeness: from x ∈ language to a suitable witness u *)
        assume "x ∈ SUBSETSUM_lang enc0"
        then obtain as s where
          x_def: "x = enc0 as s" and
          sat:   "subset_sum_true as s"
          unfolding SUBSETSUM_lang_def by blast

        from V.V_complete[OF sat] obtain xs where
          xs_ok: "ss_cert_ok as s xs" and
          len_u: "length (enc_cert as s xs) = p (length (enc0 as s))" and
          acc:   "fverify ⟨enc0 as s, enc_cert as s xs⟩ = [𝕀]"
          by blast

        have "∃u. length u = p (length x) ∧ fverify ⟨x, u⟩ = [𝕀]"
          using x_def len_u acc by blast
        thus "∃u. length u = p (length x) ∧ fverify ⟨x, u⟩ = [𝕀]" .
      next
        (* (⇐) soundness: from a witness u back to x ∈ language *)
        assume RHS: "∃u. length u = p (length x) ∧ fverify ⟨x, u⟩ = [𝕀]"
        then obtain u where
          len_u: "length u = p (length x)" and
          acc:   "fverify ⟨x, u⟩ = [𝕀]"
          by blast

        from V.V_wf[OF acc] obtain as s where
          x_def: "x = enc0 as s"
          by blast

        from acc x_def have acc_enc:
          "fverify ⟨enc0 as s, u⟩ = [𝕀]"
          by simp
        from len_u x_def have len_u_enc:
          "length u = p (length (enc0 as s))"
          by simp

        from V.V_sound[OF acc_enc len_u_enc]
        obtain xs where xs_ok: "ss_cert_ok as s xs" and u_enc: "u = enc_cert as s xs"
          by blast

        from xs_ok have "subset_sum_true as s"
          using subset_sum_true_iff_cert by blast
        hence "x ∈ SUBSETSUM_lang enc0"
          unfolding SUBSETSUM_lang_def using x_def by blast
        thus "x ∈ SUBSETSUM_lang enc0" .
      qed
    qed
  qed

  from witness
  obtain k G M p T fver where
    tm:      "turing_machine k G M" and
    poly_p:  "polynomial p" and
    T_poly:  "big_oh_poly T" and
    time:    "computes_in_time k M fver T" and
    outlen:  "∀y. length (fver y) = 1" and
    corr:    "∀x. x ∈ SUBSETSUM_lang enc0 ⟷
                   (∃u. length u = p (length x) ∧ fver ⟨x, u⟩ = [𝕀])"
    by blast

  have witness':
    "∃k G M.
       turing_machine k G M ∧
       (∃p. polynomial p ∧
        (∃T. big_oh_poly T ∧
         (∃fver.
            computes_in_time k M fver T ∧
            (∀y. length (fver y) = 1) ∧
            (∀x. x ∈ SUBSETSUM_lang enc0 ⟷
                   (∃u. length u = p (length x) ∧ fver ⟨x, u⟩ = [𝕀])))))"
    using tm poly_p T_poly time outlen corr by blast

  show "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
    unfolding NP_output_len_1
    using witness' by blast
qed


subsection ‹A Cook–Levin machine that solves SUBSET-SUM›

text ‹
  The locale CL_SubsetSum_Solver packages the basic assumptions for a
  Cook–Levin machine that decides SUBSET-SUM:

    • M is a well-formed k_tapes machine with start state q0;
    • enc is a total encoding of instances (as,s) as boolean lists;
    • M accepts exactly the encodings of true instances.

  Inside the locale we define shorthand versions steps_TM and read0_TM
  of steps_CL and read0_CL on encoded inputs.
›

locale CL_SubsetSum_Solver =
  fixes M   :: machine
    and q0  :: nat
    and enc :: "int list ⇒ int ⇒ bool list"
  assumes turing: "turing_machine k_tapes q0 M"
  assumes solves_subset_sum:
    "⋀as s. accepts_CL M (enc as s) ⟷ subset_sum_true as s"
begin

definition steps_TM :: "int list ⇒ int ⇒ nat" where
  "steps_TM as s = steps_CL M (enc as s)"

definition read0_TM :: "int list ⇒ int ⇒ nat set" where
  "read0_TM as s = read0_CL M (enc as s)"

lemma read0_TM_subset:
  "read0_TM as s ⊆ {..<length (enc as s)}"
  unfolding read0_TM_def
  using read0_CL_subset_indices by simp

end  (* context CL_SubsetSum_Solver *)


section ‹LR-read TM interface and lower bound inheritance›

text ‹
  We now introduce the Cook–Levin side LR-read interface and import the
  abstract lower bound from SubsetSum_Lemma1.

  A Cook–Levin machine is considered polynomial-time on SUBSET-SUM if its
  step-count on an instance (as,s) is bounded by some polynomial in
  length as (we take length as as the size parameter and ignore the
  bit-length of enc as s).
›

definition polytime_CL_machine
  :: "machine ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool"
where
  "polytime_CL_machine M enc ⟷
     (∃(c::real)>0. ∃(d::nat).
        ∀as s. steps_CL M (enc as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d)))"

text ‹
  The locale LR_Read_TM is the Cook–Levin analogue of SubsetSum_Lemma1.
  It assumes that:

    • M, q0, enc form a SUBSET-SUM solver in the sense of
      CL_SubsetSum_Solver;

    • for each hard instance (as,s) with distinct subset sums there exists
      a split index k at which the abstract “seen” sets seenL_TM and
      seenR_TM coincide with the canonical sets
      LHS (e_k as s k) (length as) and
      RHS (e_k as s k) (length as);

    • for all as, s, k, the step-count is bounded below by
      card (seenL_TM as s k) + card (seenR_TM as s k).

  These assumptions match the abstract axioms of SubsetSum_Lemma1 with
  steps = steps_TM and seenL = seenL_TM, seenR = seenR_TM.  Once the
  interpretation succeeds, we obtain the √(2ⁿ) lower bound specialised to
  the Cook–Levin step-count of M.
›

locale LR_Read_TM =
  CL_SubsetSum_Solver M q0 enc
  for M :: machine and q0 :: nat
      and enc :: "int list ⇒ int ⇒ bool list" +
  fixes seenL_TM :: "int list ⇒ int ⇒ nat ⇒ int set"
    and seenR_TM :: "int list ⇒ int ⇒ nat ⇒ int set"
  assumes coverage_TM:
    "⋀as s. distinct_subset_sums as ⟹
       ∃k≤length as.
         seenL_TM as s k = LHS (e_k as s k) (length as) ∧
         seenR_TM as s k = RHS (e_k as s k) (length as)"
  assumes steps_lb_TM:
    "⋀as s k. steps_TM as s ≥
                card (seenL_TM as s k) + card (seenR_TM as s k)"
begin

text ‹
  We instantiate the abstract lower-bound locale SubsetSum_Lemma1 with
  steps_TM, seenL_TM and seenR_TM.  All theorems of
  SubsetSum_Lemma1 then become available under the prefix Reader.
›

interpretation Reader:
  SubsetSum_Lemma1 steps_TM seenL_TM seenR_TM
proof
  show "⋀as s. distinct_subset_sums as ⟹
           ∃k≤length as.
             seenL_TM as s k = LHS (e_k as s k) (length as) ∧
             seenR_TM as s k = RHS (e_k as s k) (length as)"
    by (rule coverage_TM)
next
  show "⋀as s k.
           steps_TM as s ≥
             card (seenL_TM as s k) + card (seenR_TM as s k)"
    by (rule steps_lb_TM)
qed

text ‹
  Specialising Reader.subset_sum_sqrt_lower_bound yields the concrete
  lower bound for steps_TM.
›

theorem subset_sum_sqrt_lower_bound_TM:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as"
      and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) ≤ real (steps_TM as s)"
  using Reader.subset_sum_sqrt_lower_bound[OF n_def distinct]
  by simp

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

text ‹
  We now show that no machine satisfying the LR-read assumptions can have
  its step-count bounded by a single polynomial on all hard instances.
  The proof combines the analytic lemma exp_beats_poly_ceiling_strict_TM
  with the √(2ⁿ) lower bound and the hard family from exists_hard_TM.
›
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
                    steps_TM as s
                      ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  from exp_beats_poly_ceiling_strict_TM[OF cpos]
  obtain N :: nat where N:
    "∀n≥N. of_int (ceiling (c * (real n) ^ d))
           < 2 * sqrt ((2::real) ^ n)"
    by blast

  have N_ge: "N ≥ N" by simp

  (* Choose a hard instance of length N. *)
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

  (* Lower bound from the imported √(2^n) theorem, instantiated at s = 0. *)
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

  (* Polynomial upper bound assumption, instantiated to as, s = 0. *)
  have ub_nat:
    "steps_TM as 0 ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using bound dist_as by simp

  (* Relate ‹nat ⌈…⌉› and ‹of_int ⌈…⌉›. *)
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

  (* Lower bound, upper bound, and strict separation contradict each other. *)
  from ceil_lt' lb ub_real
  show False using len_as by auto
qed

text ‹
  The same impossibility result can be restated directly in terms of the
  underlying Cook–Levin step-count steps_CL on encoded instances.
›
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

end  (* locale LR_Read_TM *)

end  (* theory *)
