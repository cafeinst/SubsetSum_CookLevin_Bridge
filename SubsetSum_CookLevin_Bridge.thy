theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

(* -------------------------------------------------------------------------- *)
(* Input encoding: bool list -> Cook-Levin symbols                            *)
(* -------------------------------------------------------------------------- *)

text ‹We use a very simple encoding of bits as Cook-Levin tape symbols:
  - false ↦ 2 (zero_symbol)
  - true  ↦ 3 (one_symbol).
  We only ever read/write on tape 0 / tape 1 via the library primitives.›

definition bool_to_symbols :: "bool list ⇒ symbol list" where
  "bool_to_symbols bs = map (λb. if b then 3 else 2) bs"

definition k_tapes :: nat where
  "k_tapes = 2"

(* -------------------------------------------------------------------------- *)
(* Cook-Levin style step-count and acceptance for a given machine M          *)
(* -------------------------------------------------------------------------- *)

text ‹Given a Cook-Levin machine M, we define its running time on an input
  bitstring x as the least t such that the control state is ≥ length M (a
  standard halting condition in this development).›

definition steps_CL :: "machine ⇒ bool list ⇒ nat" where
  "steps_CL M x =
     (LEAST t. fst (execute M (start_config k_tapes (bool_to_symbols x)) t)
                ≥ length M)"

definition conf_CL :: "machine ⇒ bool list ⇒ nat ⇒ config" where
  "conf_CL M x t =
     execute M (start_config k_tapes (bool_to_symbols x)) t"

text ‹Acceptance: after halting, we look at tape 1 (the output tape) and
  check that the symbol under head 1 is 3 (one_symbol).›

definition accepts_CL :: "machine ⇒ bool list ⇒ bool" where
  "accepts_CL M x =
     (let t   = steps_CL M x;
          cfg = conf_CL M x t
      in (cfg <:> 1) (cfg <#> 1) = 3)"

(* -------------------------------------------------------------------------- *)
(* Abstract TM+encoder locale for Subset-Sum                                  *)
(* -------------------------------------------------------------------------- *)

text ‹We now connect a Cook-Levin machine with your abstract decision-tree
  lower bound.  The idea is:

  • M :: machine is any deterministic Cook-Levin Turing machine.
  • enc as s :: bool list is its input encoding for the Subset-Sum instance (as,s).
  • steps as s is just steps_CL M on the encoded input.
  • seenL / seenR are abstract “left/right” index-sets of the split reader
    that you know how to construct in your decision-tree theory.

  The assumptions say:
    (1) M + enc correctly decides distinct-subset-sum instances;
    (2) seenL/seenR satisfy the ‘coverage’ and ‘steps ≥ |seenL|+|seenR|’ axioms
        of SubsetSum_Reader_NoK;
    (3) enc is polynomially bounded in n = length as;
    (4) the running time is polynomial in the encoding length.

  From this we inherit your sqrt(2^n) lower bound and the “no polynomial
  time” theorem, but now phrased for a Cook-Levin machine.›

locale SubsetSum_TM_Reader =
  fixes M     :: machine
    and enc   :: "int list ⇒ int ⇒ bool list"
    and steps :: "int list ⇒ int ⇒ nat"
    and seenL :: "int list ⇒ int ⇒ nat ⇒ int set"
    and seenR :: "int list ⇒ int ⇒ nat ⇒ int set"
  assumes steps_def:
    "⋀as s. steps as s = steps_CL M (enc as s)"
  assumes solves_subset_sum:
    "⋀as s. distinct_subset_sums as ⟹
       accepts_CL M (enc as s) ⟷
       (∃xs∈bitvec (length as). (∑ i<length as. as ! i * xs ! i) = s)"
  assumes coverage_ex:
    "⋀as s. distinct_subset_sums as ⟹
       ∃k≤length as.
         seenL as s k = LHS (e_k as s k) (length as) ∧
         seenR as s k = RHS (e_k as s k) (length as)"
  assumes steps_lb:
    "⋀as s k. steps as s ≥ card (seenL as s k) + card (seenR as s k)"
  assumes enc_len_poly:
    "∃(C::real)>0. ∃(D::nat).
       ∀as s. distinct_subset_sums as ⟶
         real (length (enc as s)) ≤ C * (real (length as)) ^ D"
  assumes steps_poly_of_enc:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. steps as s ≤ nat (ceiling (c * (real (length (enc as s))) ^ d))"
begin

text ‹First we instantiate your abstract reader lower-bound locale with
  these TM-based notions of steps/seenL/seenR.›

sublocale SubsetSum_Reader_NoK steps seenL seenR
proof
  show "⋀as s. distinct_subset_sums as ⟹
          ∃k≤length as.
            seenL as s k = LHS (e_k as s k) (length as) ∧
            seenR as s k = RHS (e_k as s k) (length as)"
    by (rule coverage_ex)
  show "⋀as s k. steps as s ≥ card (seenL as s k) + card (seenR as s k)"
    by (rule steps_lb)
qed

text ‹Next we instantiate your polynomial-time wrapper locale, which lifts
  a polynomial bound in the encoding length to one in n = length as.›

sublocale SubsetSum_To_Polytime_NoK steps seenL seenR enc
proof
  show "∃(C::real)>0. ∃(D::nat).
          ∀as s. distinct_subset_sums as ⟶
            real (length (enc as s)) ≤ C * (real (length as)) ^ D"
    by (rule enc_len_poly)
  show "∃(c::real)>0. ∃(d::nat).
          ∀as s. steps as s ≤ nat (ceiling (c * (real (length (enc as s))) ^ d))"
    by (rule steps_poly_of_enc)
qed

text ‹Now we can simply reuse your abstract theorem
  no_polytime_decider_on_distinct_family, specialised to this TM+encoder.›

theorem no_polytime_TM_on_distinct_family:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
            ∀as s. distinct_subset_sums as ⟶
              steps as s ≤ nat (ceiling (c * (real (length as)) ^ d)))"
  using no_polytime_decider_on_distinct_family by simp

corollary no_polytime_TM_on_all_inputs:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
             ∀as s. steps as s ≤ nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_all:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. steps as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where cpos: "c > 0"
    and bound_all: "∀as s. steps as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  (* If it's polytime on all inputs, it's polytime on the distinct family *)
  hence ex_distinct:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  from no_polytime_TM_on_distinct_family and ex_distinct
  show False by contradiction
qed

text ‹Combining with steps_def, this says: there is no way to choose a
  Cook–Levin machine M and encoder enc that solve the distinct-subset-sum
  family, have the coverage properties (coverage_ex/steps_lb), and run in
  time polynomial in n = length as.›

theorem no_polytime_CL_machine_on_distinct_family:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
            ∀as s. distinct_subset_sums as ⟶
              steps_CL M (enc as s)
                ≤ nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume "∃(c::real)>0. ∃(d::nat).
            ∀as s. distinct_subset_sums as ⟶
              steps_CL M (enc as s)
                ≤ nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where cpos: "c>0"
    and poly: "∀as s. distinct_subset_sums as ⟶
                steps_CL M (enc as s)
                  ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast
  have "∀as s. distinct_subset_sums as ⟶
          steps as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using poly by (simp add: steps_def)
  hence "∃c>0. ∃d. ∀as s. distinct_subset_sums as ⟶
           steps as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using cpos by blast
  thus False
    using no_polytime_TM_on_distinct_family by blast
qed

corollary no_polytime_CL_machine_on_all_inputs:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
             ∀as s. steps_CL M (enc as s)
                     ≤ nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_all:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. steps_CL M (enc as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where cpos: "c > 0"
    and bound_all:
      "∀as s. steps_CL M (enc as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  (* Again: polytime on all inputs ⇒ polytime on distinct subset-sum family *)
  hence ex_distinct:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  from no_polytime_CL_machine_on_distinct_family and ex_distinct
  show False by contradiction
qed


end  (* locale SubsetSum_TM_Reader *)

end
