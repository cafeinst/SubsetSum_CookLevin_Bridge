theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

section ‹Cook–Levin bridge for the subset-sum lower bound›

text ‹
  STRUCTURE OF THIS THEORY

  This theory imports the abstract decision-tree lower bound from
  SubsetSum_DecisionTree and connects it to the concrete Cook–Levin
  Turing-machine model of Cook_Levin.NP.

  • On the decision-tree side, the theory SubsetSum_DecisionTree establishes
    a lower bound of Ω(√(2ⁿ)) under the abstract assumptions encoded in the
    locale SubsetSum_Lemma1.

    Although the locale does not use the phrase “flip-complete reader,” its two
    axioms—canonical LHS/RHS coverage and a cost equal to the number of
    remaining possible values—are exactly the structural properties that define
    a flip-complete reader model of SUBSET-SUM.

    In other words, SubsetSum_Lemma1 is a formal, implementation-independent
    version of the flip-complete reader model, and the lower bound is proved
    solely from these properties.

    Consequently, the concrete decision-tree model satisfies the locale
    assumptions and therefore inherits the √(2ⁿ) lower bound.

    Thus, the decision-tree model instantiates SubsetSum_Lemma1 and inherits
    the √(2ⁿ) lower bound.

  • In the present file, we build the bridge to Cook–Levin machines in
    several layers:

      – CL_SubsetSum_Solver:
          A k_tapes Cook–Levin machine M with encoding enc that correctly
          decides the mathematical predicate subset_sum_true.

      – Eq_ReadLR_SubsetSum_Solver:
          Strengthens CL_SubsetSum_Solver by assuming that M decides
          SUBSET-SUM via an equality of two “sides” (lhs, rhs), and that
          on distinct-subset-sums instances it must read at least one bit
          from the zone encoding the left side and at least one bit from the
          zone encoding the right side. This captures an adversary-style
          “must look at L and R” requirement, but does not yet align with
          the canonical LHS/RHS splits.

      – LR_Read_TM:
          A more structured assumption on M, still in the Cook–Levin model,
          which directly instantiates the abstract lower-bound locale
          SubsetSum_Lemma1. Concretely, it assumes that on any hard
          instance of length n, there exists a canonical split index
          k ≤ n such that

              steps_TM as s ≥
                card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n).

          Inside this locale we import the Ω(√(2^n)) lower bound and the 
          corresponding “no polynomial-time solver on hard instances” 
          corollaries.

      – P_neq_NP_LR_Model (in a later theory):
          A locale that packages the global LR–read meta-assumptions.
          These assumptions state that:

          • SUBSET-SUM ∈ NP using the chosen encoding enc0;
          • if SUBSET-SUM ∈ P, then there exists a polynomial-time
            Cook–Levin solver expressed in the Eq_ReadLR_SubsetSum_Solver
            interface;
          • every such equation-based polynomial-time solver must satisfy
            the LR_Read_TM axiom.

        Under these three meta-assumptions, one proves that there is
        no polynomial-time Cook–Levin machine deciding SUBSET-SUM.
        Combined with P = NP ⇒ SUBSET-SUM ∈ P, this yields the
        conditional theorem “P ≠ NP”.

  The key point is that all combinatorial lower-bound reasoning lives in the
  reader-style locales (SubsetSum_Lemma1 on the abstract side and
  LR_Read_TM on the Cook–Levin side).  The remaining gap to a full
  P ≠ NP statement is precisely the meta-assumption that every polynomial-time
  solver lies in this LR-read class.
›

text ‹
  First, we re-prove the elementary analytic fact that exponentials beat
  polynomials, but packaged in exactly the numerical form we later need
  for step-count bounds of Cook–Levin machines.
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

    (* Turn this into a bound on the ceiling. *)
    have up:
      "of_int (ceiling (c * (real n) ^ d))
         ≤ (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith

    (* For n ≥ 1, we have (√2)^n + 1 < 2·(√2)^n. *)
    have step: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using n_ge1 by simp

    (* Rewrite 2·√(2^n) as 2·(√2)^n to match the bound. *)
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
  For every length n, we can choose a “hard” weight list as of that
  length, namely the powers of 2; these have distinct subset sums.
  This is the TM-side analogue of the hard family used in the
  decision-tree theory.
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
    0 = blank, 1 = start symbol, 2 = "0", 3 = "1".
  The input instance (a bool list) is written as a row of 2/3 symbols.

  We keep this as lightweight as possible: we only need a simple
  mapping from booleans to tape symbols and a fixed tape count k_tapes.
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

  • steps_CL M x is the least t at which the control state index
    is ≥ length M (Cook–Levin’s halting convention).

  • conf_CL M x t is the configuration after t steps.

  • accepts_CL M x says that after steps_CL M x steps, the symbol under
    the head on tape 1 (the output tape) is 3, i.e. “1”.
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
  The set read0_CL M x collects all indices i on the
  input tape (tape 0) that the head visits before halting on input x.

  This abstracts away from the exact timing of visits and keeps only the
  set of input positions whose contents the machine has “inspected”.
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


subsection ‹Configuration agreement and unread positions›

text ‹
  Two configurations agree except possibly at position i on tape 0.

  This is a convenient concept if one wants to reason about how a single
  unread bit on the input tape can be flipped without affecting the
  rest of the machine's behaviour.

  In this theory we will *not* prove a general unread-flip lemma for all
  Cook–Levin machines; instead, we package the desired unread-agreement
  property as locale axioms for the particular machines we care about
  (see below).
›

definition configs_agree_except_at :: "nat ⇒ config ⇒ config ⇒ bool" where
  "configs_agree_except_at i c1 c2 ⟷
     fst c1 = fst c2 ∧
     ||c1|| = ||c2|| ∧
     (∀t. 0 < t ⟶ t < ||c1|| ⟶
         c1 <:> t = c2 <:> t ∧
         c1 <#> t = c2 <#> t) ∧
     c1 <#> 0 = c2 <#> 0 ∧
     (∀pos. pos ≠ i ⟶ (c1 <:> 0) pos = (c2 <:> 0) pos)"

text ‹Flipping a bit in a bool list›

definition flip_bool_list :: "bool list ⇒ nat ⇒ bool list" where
  "flip_bool_list xs i =
     (if i < length xs then xs[i := (¬ xs!i)] else xs)"

lemma bool_to_symbols_flip_outside:
  assumes "j < length x" "j ≠ i"
  shows "bool_to_symbols (flip_bool_list x i) ! j
       = bool_to_symbols x ! j"
  using assms
  unfolding bool_to_symbols_def flip_bool_list_def
  by (auto simp: nth_list_update)

lemma flip_bool_list_length[simp]:
  "length (flip_bool_list xs i) = length xs"
  by (simp add: flip_bool_list_def)

lemma flip_bool_list_eq_outside:
  assumes "j < length xs" "j ≠ i"
  shows "flip_bool_list xs i ! j = xs ! j"
  using assms
  by (simp add: flip_bool_list_def)

lemma head0_bounded:
  assumes "turing_machine k_tapes q0 M"
  assumes "t < steps_CL M x"
  shows   "head0_CL (conf_CL M x t) ≥ 0"
  unfolding head0_CL_def conf_CL_def
  by simp


subsection ‹Unread-agreement property as a locale axiom›

text ‹
  We now *axiomatize* the unread-flip agreement property for a given
  Cook–Levin machine.  Intuitively, this says:

    • if bit i of x is never read on tape 0 in the run of M on input x,
      then flipping that bit does not change whether M accepts.

  This is the Cook–Levin analogue of the “unread bits do not matter”
  property used on the decision-tree side. It is *not* derivable for
  arbitrary machines from the raw Cook–Levin semantics, so we expose it
  as a separate locale that can be assumed for the particular solvers
  we care about.
›

locale Flip_Agreement_CL =
  fixes M :: machine and q0 :: nat
  assumes TM: "turing_machine k_tapes q0 M"
  assumes unread_agreement:
    "⋀x i. i < length x ⟹ i ∉ read0_CL M x
          ⟹ accepts_CL M x = accepts_CL M (flip_bool_list x i)"


subsection ‹The mathematical SUBSET-SUM predicate›

text ‹
  This is the “true” subset-sum specification: we ask if there exists a
  0/1-vector xs selecting a subset of as that sums to s.

  It is intentionally independent of Turing machines or encodings;
  later we connect it to NP-style verifiers and Cook–Levin machines.
›

definition subset_sum_true :: "int list ⇒ int ⇒ bool" where
  "subset_sum_true as s ⟷
     (∃xs ∈ bitvec (length as).
        (∑ i<length as. as ! i * xs ! i) = s)"


subsection ‹Certificate-based view of SUBSET-SUM›

text ‹
  A natural NP-style certificate for SUBSET-SUM is a 0/1-vector xs
  of the same length as as, indicating which elements are chosen.
  The verifier checks:
    • length xs = length as
    • each entry is 0 or 1
    • the weighted sum equals s.

  We package this as ss_cert_ok and then show the obvious equivalence with
  subset_sum_true.
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
  We now define an abstract verifier locale that matches the NP definition
  in theory NP.  It assumes that we have:

    • an instance encoding enc0 :: "int list ⇒ int ⇒ string",
    • a certificate encoding enc_cert :: "int list ⇒ int ⇒ int list ⇒ string",
    • a Turing machine V computing a verifier function fverify,
    • a polynomial bound p on the certificate length as a function of
      the instance length.

  The correctness condition ties everything back to ss_cert_ok and
  hence to subset_sum_true.

  This locale is deliberately generic in k, G, V, p, T, and fverify; later
  we will instantiate it with Cook–Levin style encodings when needed.
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


subsection ‹Encoding of instance–certificate pairs›

text ‹
  For the NP view, we want a single input bitstring that encodes both
  the instance (as,s) and a certificate xs.  We keep the instance
  encoding enc0 abstract, and assume a separate certificate encoding
  enc_cert.  The combined encoding just concatenates them with a fixed
  separator.

  This is the standard “instance || separator || certificate” trick.
›

definition sep :: "bool list" where
  "sep = [True, False, True]"  (* any fixed non-empty pattern *)

definition enc_pair ::
  "(int list ⇒ int ⇒ bool list) ⇒
   (int list ⇒ int ⇒ int list ⇒ bool list) ⇒
   int list ⇒ int ⇒ int list ⇒ bool list" where
  "enc_pair enc0 enc_cert as s xs =
     enc0 as s @ sep @ enc_cert as s xs"


subsection ‹A Cook–Levin verifier for SUBSET-SUM›

text ‹
  Locale SS_Verifier_CL specialises the abstract SS_Verifier_NP idea to
  the Cook–Levin world:

   • V is a k_tapes Cook–Levin machine.

   • On input enc_pair enc0 enc_cert as s xs, if length xs = length as,
     V accepts exactly when xs is a correct subset-sum witness
     (ss_cert_ok as s xs).

   • The running time of V is bounded by a polynomial in the instance
     size |enc0 as s|, uniformly over all certificates xs of matching
     length.
›

locale SS_Verifier_CL =
  fixes V        :: machine
    and q0       :: nat
    and enc0     :: "int list ⇒ int ⇒ bool list"
    and enc_cert :: "int list ⇒ int ⇒ int list ⇒ bool list"
  assumes V_tm:
    "turing_machine k_tapes q0 V"
  assumes V_polytime:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s xs.
         length xs = length as ⟶
         steps_CL V (enc_pair enc0 enc_cert as s xs)
           ≤ nat (ceiling (c * (real (length (enc0 as s)) ^ d)))"
  assumes V_correct:
    "⋀as s xs.
       length xs = length as ⟶
       accepts_CL V (enc_pair enc0 enc_cert as s xs)
         ⟷ ss_cert_ok as s xs"

text ‹
  Intuitively:

   • V is a k_tape Cook–Levin machine.

   • On input enc_pair enc0 enc_cert as s xs, if length xs = length as,
     V accepts exactly when xs is a correct subset-sum witness
     (ss_cert_ok as s xs).

   • The running time of V is bounded by a polynomial in the instance
     size |enc0 as s|, uniformly over all certificates xs of matching
     length.
›


section ‹SUBSET-SUM as a language›

text ‹
  Given an instance encoding function enc0 which maps a pair
  (as,s) to a bitstring, we define the SUBSET-SUM language as the set
  of all strings that encode a true SUBSET-SUM instance.

  This is the standard “language view” of the decision problem.
›

definition SUBSETSUM_lang :: "(int list ⇒ int ⇒ string) ⇒ language" where
  "SUBSETSUM_lang enc0 ≡
     {x. ∃as s. x = enc0 as s ∧ subset_sum_true as s}"

subsection ‹SUBSET-SUM is in NP (relative to enc0)›

text ‹
  The next lemma packages the SS_Verifier_NP locale into the
  NP_output_len_1 characterization of NP from Cook_Levin.NP.
  It says: if there is a suitable NP-style verifier for SUBSET-SUM
  w.r.t. enc0, then the language SUBSETSUM_lang enc0 is in 𝒩𝒫.
›
lemma SUBSETSUM_in_NP_from_verifier:
  fixes k G V p T fverify enc0 enc_cert
  assumes verif: "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 ∈ 𝒩𝒫"
proof -
  interpret V: SS_Verifier_NP k G V p T fverify enc0 enc_cert
    using verif .

  text ‹Use the alternative NP characterization @{thm NP_output_len_1}.›

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
    (* choose k,G,M,p,T,fver as the ones from the verifier *)
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
        (* (⇒) completeness direction: from language membership to a witness u *)
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
        (* (⇐) soundness direction: from a witness u to language membership *)
        assume RHS: "∃u. length u = p (length x) ∧ fverify ⟨x, u⟩ = [𝕀]"
        then obtain u where
          len_u: "length u = p (length x)" and
          acc:   "fverify ⟨x, u⟩ = [𝕀]"
          by blast

        (* Use the WELL-FORMEDNESS axiom: accepting ⇒ x is some enc0 as s *)
        from V.V_wf[OF acc] obtain as s where
          x_def: "x = enc0 as s"
          by blast

        (* Rewrite premises into the shape V_sound expects *)
        from acc x_def have acc_enc:
          "fverify ⟨enc0 as s, u⟩ = [𝕀]"
          by simp
        from len_u x_def have len_u_enc:
          "length u = p (length (enc0 as s))"
          by simp

        (* Important: argument order matches V_sound: acc_enc THEN len_u_enc *)
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

  (* We now package the verifier data into the exact shape
     required by NP_output_len_1. *)
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
  Locale CL_SubsetSum_Solver says:
   • M is a well-formed k_tapes Cook–Levin machine,
   • enc encodes (as,s) as a bool list,
   • M decides subset_sum_true at that encoding.

  Inside the locale, steps_TM and read0_TM are just convenient
  aliases of steps_CL and read0_CL on enc as s.
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


subsection ‹Equation-based read requirement›

text ‹
  This locale expresses the idea that the machine decides SUBSET-SUM
  by checking equality of two “sides” of an equation.  Conceptually,
  there is some base equation

      l(as, s) = r(as, s)

  such that (as,s) is in the language iff this equation holds.  We allow
  the machine to work with any *equivalent* equation, e.g. of the form

      f(l(as,s)) = f(r(as,s))

  for some injective function f; all of this is abstracted into the
  two functions lhs and rhs, and the correctness assumption

      subset_sum_true as s ⟷ lhs as s = rhs as s.

  The sets L_zone as s and R_zone as s describe the input positions
  (in enc as s) that encode the left- and right-hand sides of this
  deciding equation.  The assumption must_read_LR then says:

      – on every distinct-subset-sums instance (as,s),
        the machine’s read set read0_TM as s intersects L_zone as s, and
      – it also intersects R_zone as s.

  In other words: on “hard” instances, the machine must read at least one
  bit from the part of the input encoding the left side and at least one
  bit from the part encoding the right side of some deciding equation
  equivalent to l = r.
›

locale Eq_ReadLR_SubsetSum_Solver =
  CL_SubsetSum_Solver M q0 enc
  for M :: machine and q0 :: nat
      and enc :: "int list ⇒ int ⇒ bool list" +
  fixes lhs rhs :: "int list ⇒ int ⇒ int"
    and L_zone R_zone :: "int list ⇒ int ⇒ nat set"
  assumes equation_correct:
    "⋀as s. subset_sum_true as s ⟷ (lhs as s = rhs as s)"
  assumes zones_wf:
    "⋀as s. L_zone as s ⊆ {..< length (enc as s)}"
    "⋀as s. R_zone as s ⊆ {..< length (enc as s)}"
    "⋀as s. L_zone as s ∩ R_zone as s = {}"
  assumes must_read_LR:
    "⋀as s. distinct_subset_sums as ⟹
       read0_TM as s ∩ L_zone as s ≠ {} ∧
       read0_TM as s ∩ R_zone as s ≠ {}"

text ‹
  RELATION TO THE ABSTRACT LOWER-BOUND AXIOM LR_Read_TM

  The locale Eq_ReadLR_SubsetSum_Solver isolates a concrete,
  adversary-style requirement:

    • SUBSET-SUM is decided via some equation
        lhs as s = rhs as s
      (up to injective re-encoding, e.g. f (lhs as s) = f (rhs as s)),

    • and on distinct-subset-sums instances the machine must read at
      least one bit from the part of the input encoding the “left side”
      and at least one bit from the part encoding the “right side”
      (L_zone as s and R_zone as s).

  The locale LR_Read_TM below is a more structured, but still abstract,
  interface to the decision-tree lower bound.  Instead of talking about
  particular input zones, it assumes directly that for some canonical
  split index k, the runtime is at least

      card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)

  on any distinct-subset-sums instance of length n.  This matches the
  combinatorial structure exploited in SubsetSum_DecisionTree and is
  exactly what is needed to instantiate the abstract reader model.

  Intuitively, any machine satisfying the concrete “must read from L and
  R” condition of Eq_ReadLR_SubsetSum_Solver *and* aligning with the
  canonical LHS/RHS partial-sum splits should give rise to an instance of
  LR_Read_TM.  In this theory we keep that connection as a meta-level
  assumption (see the locale P_neq_NP_LR_Model in SubsetSum_PneqNP,
  which packages the global LR–read meta-assumptions needed to transport 
  the abstract √(2ⁿ) lower bound into a conditional P ≠ NP result.)
  All formal lower-bound proofs are phrased inside LR_Read_TM, which 
  is the Cook–Levin side of the flip-complete/reader-style model.
›

section ‹LR-read TM interface and lower bound inheritance›

text ‹
  A Cook–Levin machine is polynomial-time on SUBSET-SUM if its
  running time on the encoding of (as,s) is bounded by some polynomial
  in the length of the weight list as (≃ input size). The bit-length of
  the encoding enc as s may itself be a fixed polynomial in length as;
  we deliberately take length as as the complexity parameter here.
›

definition polytime_CL_machine
  :: "machine ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool"
where
  "polytime_CL_machine M enc ⟷
     (∃(c::real)>0. ∃(d::nat).
        ∀as s. steps_CL M (enc as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d)))"

text ‹
  We inherit the abstract Ω(√(2^n)) lower bound from SubsetSum_Lemma1.

  The abstract reader-model locale SubsetSum_Lemma1 (defined in the theory
  SubsetSum_DecisionTree) packages the combinatorial lower bound we are
  importing here.

  Its parameters are:
    • steps :: int list ⇒ int ⇒ nat
    • seenL, seenR :: int list ⇒ int ⇒ nat ⇒ int set

  and its assumptions say informally:

    (coverage_ex)
      On every hard instance (as,s) with distinct subset sums, there exists
      a split index k ≤ length as such that

        seenL as s k = LHS (e_k as s k) (length as)
        seenR as s k = RHS (e_k as s k) (length as).

    (steps_lb)
      For all as, s, k,
        steps as s ≥ card (seenL as s k) + card (seenR as s k).

  From these, SubsetSum_Lemma1 proves the abstract lower bound

      2 * sqrt (2^n) ≤ real (steps as s)

  on all hard instances with n = length as.  In the LR_Read_TM locale
  below, we simply instantiate SubsetSum_Lemma1 with the Cook–Levin
  step function steps_TM and TM-specific seenL_TM / seenR_TM.

  ------------------------------------------------------------------------------
  ■ The LR_Read_TM locale: importing the abstract lower bound into the
    Cook–Levin Turing-machine model
  ------------------------------------------------------------------------------

  The locale LR_Read_TM is the Cook–Levin analogue of SubsetSum_Lemma1.  It
  specialises the abstract “read-all-values” principle to a concrete Turing
  machine M with encoding enc that already solves SUBSET-SUM in the sense of
  CL_SubsetSum_Solver.

  Inside the locale, the function

      steps_TM as s = steps_CL M (enc as s)

  is simply the Cook–Levin step-count of M on the encoded instance.  The sets

      seenL_TM as s k
      seenR_TM as s k

  are abstract descriptions of which left-hand and right-hand values the
  machine depends on (or is considered to have “seen”) when splitting the
  variables at index k.

  The assumptions are direct analogues of those in SubsetSum_Lemma1:

    (coverage_TM)
        On every hard instance (as, s) with distinct subset sums, there exists
        a split index k such that

            seenL_TM as s k = LHS (e_k as s k) (length as)
            seenR_TM as s k = RHS (e_k as s k) (length as).

        Thus M’s behaviour can be aligned with the canonical LHS/RHS sets.

    (steps_lb_TM)
        For all instances and all k,
            steps_TM as s ≥
              card(seenL_TM as s k) + card(seenR_TM as s k).

        Each LHS or RHS value the machine depends on must contribute cost.

  Once these are assumed, the locale immediately inherits the full lower bound

        steps_TM as s ≥ 2 * sqrt(2^n)

  on all hard instances (via reinterpretation of SubsetSum_Lemma1).  It also
  inherits the corollary that no polynomial upper bound on steps_TM can exist
  over the powers-of-two family.

  Thus LR_Read_TM is the formal point where the abstract lower bound is
  transferred into the concrete Cook–Levin world.
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
  We now instantiate the abstract reader-model locale SubsetSum_Lemma1 with
  the TM-specific functions steps_TM, seenL_TM and seenR_TM.

  The command

    interpretation Reader: SubsetSum_Lemma1 steps_TM seenL_TM seenR_TM

  checks that the assumptions of SubsetSum_Lemma1 are satisfied, using the
  locale axioms coverage_TM and steps_lb_TM.  Once this succeeds, *all*
  theorems of SubsetSum_Lemma1 become available in the current context,
  prefixed by Reader.  In particular, we obtain the lower-bound theorem

    Reader.subset_sum_sqrt_lower_bound

  which states that, on any hard instance with n = length as,

    2 * sqrt ((2::real) ^ n) ≤ real (steps_TM as s).

  The rest of this locale simply rephrases that abstract bound in the concrete
  Cook–Levin step-count steps_CL M (enc as s) and derives the “no polynomial”
  corollaries for machines satisfying LR_Read_TM.
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

text ‹We inherit the abstract Ω(√(2^n)) lower bound from SubsetSum_Lemma1.›

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
  Now we replay the “exponential beats polynomial” argument in the TM
  setting: if steps_TM were polynomially bounded over all distinct
  subset-sum families, we would contradict the inherited Ω(√(2^n))
  lower bound using the hard family from exists_hard_TM.
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

  (* Use the analytic lemma in the TM-friendly form. *)
  from exp_beats_poly_ceiling_strict_TM[OF cpos]
  obtain N :: nat where N:
    "∀n≥N. of_int (ceiling (c * (real n) ^ d))
           < 2 * sqrt ((2::real) ^ n)"
    by blast

  have N_ge: "N ≥ N" by simp

  (* Instantiate a hard instance as of length N. *)
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

  (* Lower bound from Lemma 1 / Reader locale. *)
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

  (* Polynomial upper bound assumption, instantiated to as, s=0. *)
  have ub_nat:
    "steps_TM as 0 ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using bound dist_as by simp

  (* Relate nat ⌈…⌉ and of_int ⌈…⌉. *)
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
  The same argument phrased in terms of the underlying Cook–Levin
  step function steps_CL and encoding enc.
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
