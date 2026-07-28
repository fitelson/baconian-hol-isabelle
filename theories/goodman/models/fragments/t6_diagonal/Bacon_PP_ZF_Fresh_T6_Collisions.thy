theory Bacon_PP_ZF_Fresh_T6_Collisions
  imports Bacon_PP_ZF_Fresh_T6_Diagonal_Fragment_Model
begin

section \<open>A recurrent proposition for the necessary-falsity collision\<close>

fun pp_t_initial_true_parity :: "bool list \<Rightarrow> bool" where
  "pp_t_initial_true_parity [] = False"
| "pp_t_initial_true_parity (False # xs) = False"
| "pp_t_initial_true_parity (True # xs) =
    (\<not> pp_t_initial_true_parity xs)"

lemma pp_t_initial_true_parity_replicate:
  "pp_t_initial_true_parity (replicate n True) = odd n"
  by (induction n) simp_all

lemma pp_t_initial_true_parity_off_spine:
  "pp_t_initial_true_parity
      (replicate n True @ False # xs) = odd n"
  by (induction n) simp_all

lemma pp_t_replicate_true_snoc:
  "replicate n True @ [True] = replicate (Suc n) True"
  by (induction n) simp_all

lemma pp_t_replicate_true_snoc_false:
  "replicate n True @ [True, False] =
    replicate (Suc n) True @ [False]"
  by (induction n) simp_all

lemma pp_t_bool_list_spine_or_off_spine:
  obtains
    (spine) n where "xs = replicate n True"
  | (off_spine) n ys where
      "xs = replicate n True @ False # ys"
proof (induction xs arbitrary: thesis)
  case Nil
  show ?case
    by (rule Nil.prems(1)[of 0]) simp
next
  case (Cons b xs)
  show ?case
  proof (cases b)
    case False
    show ?thesis
      by (rule Cons.prems(2)[of 0 xs]) (simp add: False)
  next
    case True
    from Cons.IH consider
        (spine) n where "xs = replicate n True"
      | (off_spine) n ys where
          "xs = replicate n True @ False # ys"
      by blast
    then show ?thesis
    proof cases
      case spine
      show ?thesis
        by (rule Cons.prems(1)[of "Suc n"])
          (simp add: True spine)
    next
      case off_spine
      show ?thesis
        by (rule Cons.prems(2)[of "Suc n" ys])
          (simp add: True off_spine)
    qed
  qed
qed

definition pp_t_recurrent_fun_prime :: ZF where
  "pp_t_recurrent_fun_prime =
    pp_t_prop pp_t_initial_true_parity"

lemma pp_t_recurrent_fun_prime_in_domain:
  "Elem pp_t_recurrent_fun_prime (pp_t_domain Prop)"
  unfolding pp_t_recurrent_fun_prime_def
  by (rule pp_t_prop_in_domain)

lemma pp_t_recurrent_fun_prime_holds[simp]:
  "pp_t_holds pp_t_recurrent_fun_prime w
    \<longleftrightarrow> pp_t_initial_true_parity w"
  by (simp add: pp_t_recurrent_fun_prime_def)

lemma pp_t_recurrent_fun_prime_spine_values:
  "pp_t_holds pp_t_recurrent_fun_prime (replicate n True)
    = odd n"
  "pp_t_holds pp_t_recurrent_fun_prime
      (replicate n True @ [False])
    = odd n"
  "pp_t_holds pp_t_recurrent_fun_prime
      (replicate n True @ [True])
    = even n"
  "pp_t_holds pp_t_recurrent_fun_prime
      (replicate n True @ [True, False])
    = even n"
  by (simp_all add: pp_t_replicate_true_snoc
      pp_t_replicate_true_snoc_false
      pp_t_initial_true_parity_replicate
      pp_t_initial_true_parity_off_spine)

lemma pp_t_recurrent_fun_prime_off_spine_settled:
  "pp_t_eqv Prop (replicate n True @ False # xs)
    pp_t_recurrent_fun_prime (pp_zf_truth (odd n))"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix v
  assume future:
    "prefix (replicate n True @ False # xs) v"
  then obtain ys where
    v: "v = (replicate n True @ False # xs) @ ys"
    unfolding prefix_def by blast
  show "pp_t_holds pp_t_recurrent_fun_prime v =
      pp_t_holds (pp_zf_truth (odd n)) v"
    unfolding v
    by (simp add: append_assoc
        pp_t_initial_true_parity_off_spine)
qed

lemma pp_t_recurrent_fun_prime_spine_not_settled:
  "\<not> pp_t_eqv Prop (replicate n True)
    pp_t_recurrent_fun_prime (pp_zf_truth b)"
proof
  assume settled:
    "pp_t_eqv Prop (replicate n True)
      pp_t_recurrent_fun_prime (pp_zf_truth b)"
  have here:
      "pp_t_holds pp_t_recurrent_fun_prime
          (replicate n True) = b"
    using pp_t_prop_eqv_at[OF settled, of "replicate n True"]
    by simp
  have next_value:
      "pp_t_holds pp_t_recurrent_fun_prime
          (replicate n True @ [True]) = b"
    using pp_t_prop_eqv_at[
      OF settled, of "replicate n True @ [True]"]
    by simp
  show False
    using here next_value
      pp_t_recurrent_fun_prime_spine_values(1,3)[of n]
    by simp
qed

definition pp_t_recurrent_signature ::
    "nat \<Rightarrow> ZF \<Rightarrow> bool list"
where
  "pp_t_recurrent_signature n F = [
    pp_t_holds (F \<acute> pp_t_recurrent_fun_prime)
      (replicate n True),
    pp_t_holds (F \<acute> pp_t_recurrent_fun_prime)
      (replicate n True @ [False]),
    pp_t_holds (F \<acute> pp_t_recurrent_fun_prime)
      (replicate n True @ [True]),
    pp_t_holds (F \<acute> pp_t_recurrent_fun_prime)
      (replicate n True @ [True, False])]"

lemma pp_t_recurrent_modal_values:
  "\<not> pp_t_holds
    (pp_t_necessity_operator \<acute> pp_t_recurrent_fun_prime)
      (replicate n True)"
  "pp_t_holds
    (pp_t_possibility_operator \<acute> pp_t_recurrent_fun_prime)
      (replicate n True)"
  "\<not> pp_t_holds
    (pp_t_necessary_falsity_operator \<acute>
      pp_t_recurrent_fun_prime) (replicate n True)"
  "pp_t_holds
    (pp_t_possible_falsity_operator \<acute>
      pp_t_recurrent_fun_prime) (replicate n True)"
proof -
  let ?s = "replicate n True"
  let ?p = "pp_t_recurrent_fun_prime"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_recurrent_fun_prime_in_domain)
  have not_true:
      "\<not> pp_t_eqv Prop ?s ?p (pp_zf_truth True)"
    by (rule pp_t_recurrent_fun_prime_spine_not_settled)
  have not_false:
      "\<not> pp_t_eqv Prop ?s ?p (pp_zf_truth False)"
    by (rule pp_t_recurrent_fun_prime_spine_not_settled)
  show "\<not> pp_t_holds
      (pp_t_necessity_operator \<acute> ?p) ?s"
    using pp_t_necessity_operator_holds[OF p, of ?s]
      not_true by blast
  show "pp_t_holds
      (pp_t_possibility_operator \<acute> ?p) ?s"
    unfolding pp_t_possibility_operator_holds[OF p]
  proof (cases "odd n")
    case True
    show "\<exists>v. prefix ?s v \<and> pp_t_holds ?p v"
      using pp_t_recurrent_fun_prime_spine_values(1)[of n] True
      by (intro exI[of _ ?s]) simp
  next
    case False
    show "\<exists>v. prefix ?s v \<and> pp_t_holds ?p v"
      using pp_t_recurrent_fun_prime_spine_values(3)[of n] False
      by (intro exI[of _ "?s @ [True]"]) simp
  qed
  show "\<not> pp_t_holds
      (pp_t_necessary_falsity_operator \<acute> ?p) ?s"
    using pp_t_necessary_falsity_operator_holds[OF p, of ?s]
      not_false by blast
  show "pp_t_holds
      (pp_t_possible_falsity_operator \<acute> ?p) ?s"
    using pp_t_possible_falsity_operator_holds[OF p, of ?s]
      not_true by blast
qed

lemma pp_t_settled_operator_values:
  assumes p: "Elem p (pp_t_domain Prop)"
    and settled:
      "pp_t_eqv Prop w p (pp_zf_truth b)"
  shows
    "pp_t_holds
      (pp_t_necessity_operator \<acute> p) w = b"
    "pp_t_holds
      (pp_t_possibility_operator \<acute> p) w = b"
    "pp_t_holds
      (pp_t_necessary_falsity_operator \<acute> p) w =
        (\<not> b)"
    "pp_t_holds
      (pp_t_possible_falsity_operator \<acute> p) w =
        (\<not> b)"
proof -
  have at_w: "pp_t_holds p w = b"
    using pp_t_prop_eqv_at[OF settled, of w] by simp
  have all_future:
      "\<And>v. prefix w v \<Longrightarrow> pp_t_holds p v = b"
    using pp_t_prop_eqv_at[OF settled] by simp
  show "pp_t_holds
      (pp_t_necessity_operator \<acute> p) w = b"
    using pp_t_necessity_operator_holds[OF p, of w]
      settled by (cases b) auto
  show "pp_t_holds
      (pp_t_possibility_operator \<acute> p) w = b"
    unfolding pp_t_possibility_operator_holds[OF p]
    using at_w all_future by (cases b) auto
  show "pp_t_holds
      (pp_t_necessary_falsity_operator \<acute> p) w =
        (\<not> b)"
    using pp_t_necessary_falsity_operator_holds[OF p, of w]
      settled by (cases b) auto
  show "pp_t_holds
      (pp_t_possible_falsity_operator \<acute> p) w =
        (\<not> b)"
    using pp_t_possible_falsity_operator_holds[OF p, of w]
      settled by (cases b) auto
qed

lemma pp_t_recurrent_signatures:
  assumes even: "\<not> odd n"
  shows
    "pp_t_recurrent_signature n pp_t_identity_operator =
      [False, False, True, True]"
    "pp_t_recurrent_signature n pp_t_negation_operator =
      [True, True, False, False]"
    "pp_t_recurrent_signature n (pp_t_constant_operator True) =
      [True, True, True, True]"
    "pp_t_recurrent_signature n (pp_t_constant_operator False) =
      [False, False, False, False]"
    "pp_t_recurrent_signature n pp_t_necessity_operator =
      [False, False, False, True]"
    "pp_t_recurrent_signature n pp_t_possibility_operator =
      [True, False, True, True]"
    "pp_t_recurrent_signature n pp_t_necessary_falsity_operator =
      [False, True, False, False]"
    "pp_t_recurrent_signature n pp_t_possible_falsity_operator =
      [True, True, True, False]"
proof -
  let ?p = pp_t_recurrent_fun_prime
  let ?s0 = "replicate n True"
  let ?s1 = "?s0 @ [False]"
  let ?s2 = "?s0 @ [True]"
  let ?s3 = "?s0 @ [True, False]"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_recurrent_fun_prime_in_domain)
  have points:
      "\<not> pp_t_holds ?p ?s0"
      "\<not> pp_t_holds ?p ?s1"
      "pp_t_holds ?p ?s2"
      "pp_t_holds ?p ?s3"
    using pp_t_recurrent_fun_prime_spine_values[of n] even
    by simp_all
  have modal0:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?p) ?s0"
      "pp_t_holds (pp_t_possibility_operator \<acute> ?p) ?s0"
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?p) ?s0"
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) ?s0"
    by (rule pp_t_recurrent_modal_values)+
  have settled1:
      "pp_t_eqv Prop ?s1 ?p (pp_zf_truth False)"
    using pp_t_recurrent_fun_prime_off_spine_settled[
      of n "[]"] even by simp
  have modal1:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?p) ?s1"
      "\<not> pp_t_holds (pp_t_possibility_operator \<acute> ?p) ?s1"
      "pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?p) ?s1"
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) ?s1"
    using pp_t_settled_operator_values[
      OF p settled1] by simp_all
  have modal2:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?p) ?s2"
      "pp_t_holds (pp_t_possibility_operator \<acute> ?p) ?s2"
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?p) ?s2"
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) ?s2"
    using pp_t_recurrent_modal_values[of "Suc n"]
    by (simp_all add: pp_t_replicate_true_snoc)
  have settled3:
      "pp_t_eqv Prop ?s3 ?p (pp_zf_truth True)"
    using pp_t_recurrent_fun_prime_off_spine_settled[
      of "Suc n" "[]"] even
    by (simp add: pp_t_replicate_true_snoc_false)
  have modal3:
      "pp_t_holds (pp_t_necessity_operator \<acute> ?p) ?s3"
      "pp_t_holds (pp_t_possibility_operator \<acute> ?p) ?s3"
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?p) ?s3"
      "\<not> pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) ?s3"
    using pp_t_settled_operator_values[
      OF p settled3] by simp_all
  show "pp_t_recurrent_signature n pp_t_identity_operator =
      [False, False, True, True]"
    unfolding pp_t_recurrent_signature_def
    using points p
    by (simp add: pp_t_identity_operator_def Lambda_app)
  show "pp_t_recurrent_signature n pp_t_negation_operator =
      [True, True, False, False]"
    unfolding pp_t_recurrent_signature_def
    using points pp_t_negation_operator_holds[OF p]
    by blast
  show "pp_t_recurrent_signature n
      (pp_t_constant_operator True) =
      [True, True, True, True]"
    unfolding pp_t_recurrent_signature_def
    using pp_t_constant_operator_holds[OF p, of True]
    by simp
  show "pp_t_recurrent_signature n
      (pp_t_constant_operator False) =
      [False, False, False, False]"
    unfolding pp_t_recurrent_signature_def
    using pp_t_constant_operator_holds[OF p, of False]
    by simp
  show "pp_t_recurrent_signature n pp_t_necessity_operator =
      [False, False, False, True]"
    unfolding pp_t_recurrent_signature_def
    using modal0 modal1 modal2 modal3 by simp
  show "pp_t_recurrent_signature n pp_t_possibility_operator =
      [True, False, True, True]"
    unfolding pp_t_recurrent_signature_def
    using modal0 modal1 modal2 modal3 by simp
  show "pp_t_recurrent_signature n
      pp_t_necessary_falsity_operator =
      [False, True, False, False]"
    unfolding pp_t_recurrent_signature_def
    using modal0 modal1 modal2 modal3 by simp
  show "pp_t_recurrent_signature n
      pp_t_possible_falsity_operator =
      [True, True, True, False]"
    unfolding pp_t_recurrent_signature_def
    using modal0 modal1 modal2 modal3 by simp
qed

lemma pp_t_recurrent_signatures_odd:
  assumes odd: "odd n"
  shows
    "pp_t_recurrent_signature n pp_t_identity_operator =
      [True, True, False, False]"
    "pp_t_recurrent_signature n pp_t_negation_operator =
      [False, False, True, True]"
    "pp_t_recurrent_signature n (pp_t_constant_operator True) =
      [True, True, True, True]"
    "pp_t_recurrent_signature n (pp_t_constant_operator False) =
      [False, False, False, False]"
    "pp_t_recurrent_signature n pp_t_necessity_operator =
      [False, True, False, False]"
    "pp_t_recurrent_signature n pp_t_possibility_operator =
      [True, True, True, False]"
    "pp_t_recurrent_signature n pp_t_necessary_falsity_operator =
      [False, False, False, True]"
    "pp_t_recurrent_signature n pp_t_possible_falsity_operator =
      [True, False, True, True]"
proof -
  let ?p = pp_t_recurrent_fun_prime
  let ?s0 = "replicate n True"
  let ?s1 = "?s0 @ [False]"
  let ?s2 = "?s0 @ [True]"
  let ?s3 = "?s0 @ [True, False]"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_recurrent_fun_prime_in_domain)
  have points:
      "pp_t_holds ?p ?s0"
      "pp_t_holds ?p ?s1"
      "\<not> pp_t_holds ?p ?s2"
      "\<not> pp_t_holds ?p ?s3"
    using pp_t_recurrent_fun_prime_spine_values[of n] odd
    by simp_all
  have modal0:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?p) ?s0"
      "pp_t_holds (pp_t_possibility_operator \<acute> ?p) ?s0"
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?p) ?s0"
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) ?s0"
    by (rule pp_t_recurrent_modal_values)+
  have settled1:
      "pp_t_eqv Prop ?s1 ?p (pp_zf_truth True)"
    using pp_t_recurrent_fun_prime_off_spine_settled[
      of n "[]"] odd by simp
  have modal1:
      "pp_t_holds (pp_t_necessity_operator \<acute> ?p) ?s1"
      "pp_t_holds (pp_t_possibility_operator \<acute> ?p) ?s1"
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?p) ?s1"
      "\<not> pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) ?s1"
    using pp_t_settled_operator_values[
      OF p settled1] by simp_all
  have modal2:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?p) ?s2"
      "pp_t_holds (pp_t_possibility_operator \<acute> ?p) ?s2"
      "\<not> pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?p) ?s2"
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) ?s2"
    using pp_t_recurrent_modal_values[of "Suc n"]
    by (simp_all add: pp_t_replicate_true_snoc)
  have settled3:
      "pp_t_eqv Prop ?s3 ?p (pp_zf_truth False)"
    using pp_t_recurrent_fun_prime_off_spine_settled[
      of "Suc n" "[]"] odd
    by (simp add: pp_t_replicate_true_snoc_false)
  have modal3:
      "\<not> pp_t_holds (pp_t_necessity_operator \<acute> ?p) ?s3"
      "\<not> pp_t_holds (pp_t_possibility_operator \<acute> ?p) ?s3"
      "pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> ?p) ?s3"
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> ?p) ?s3"
    using pp_t_settled_operator_values[
      OF p settled3] by simp_all
  show "pp_t_recurrent_signature n pp_t_identity_operator =
      [True, True, False, False]"
    unfolding pp_t_recurrent_signature_def
    using points p
    by (simp add: pp_t_identity_operator_def Lambda_app)
  show "pp_t_recurrent_signature n pp_t_negation_operator =
      [False, False, True, True]"
    unfolding pp_t_recurrent_signature_def
    using points pp_t_negation_operator_holds[OF p]
    by blast
  show "pp_t_recurrent_signature n
      (pp_t_constant_operator True) =
      [True, True, True, True]"
    unfolding pp_t_recurrent_signature_def
    using pp_t_constant_operator_holds[OF p, of True]
    by simp
  show "pp_t_recurrent_signature n
      (pp_t_constant_operator False) =
      [False, False, False, False]"
    unfolding pp_t_recurrent_signature_def
    using pp_t_constant_operator_holds[OF p, of False]
    by simp
  show "pp_t_recurrent_signature n pp_t_necessity_operator =
      [False, True, False, False]"
    unfolding pp_t_recurrent_signature_def
    using modal0 modal1 modal2 modal3 by simp
  show "pp_t_recurrent_signature n pp_t_possibility_operator =
      [True, True, True, False]"
    unfolding pp_t_recurrent_signature_def
    using modal0 modal1 modal2 modal3 by simp
  show "pp_t_recurrent_signature n
      pp_t_necessary_falsity_operator =
      [False, False, False, True]"
    unfolding pp_t_recurrent_signature_def
    using modal0 modal1 modal2 modal3 by simp
  show "pp_t_recurrent_signature n
      pp_t_possible_falsity_operator =
      [True, False, True, True]"
    unfolding pp_t_recurrent_signature_def
    using modal0 modal1 modal2 modal3 by simp
qed

lemma pp_t_recurrent_representatives_separated:
  assumes A: "A \<in> pp_t_fun_prime_probe_representatives"
    and B: "B \<in> pp_t_fun_prime_probe_representatives"
    and agreement:
      "pp_t_eqv Prop (replicate n True)
        (A \<acute> pp_t_recurrent_fun_prime)
        (B \<acute> pp_t_recurrent_fun_prime)"
  shows "A = B"
proof -
  let ?s = "replicate n True"
  have signature_equality:
      "pp_t_recurrent_signature n A =
       pp_t_recurrent_signature n B"
  proof -
    have root:
        "pp_t_holds (A \<acute> pp_t_recurrent_fun_prime) ?s =
         pp_t_holds (B \<acute> pp_t_recurrent_fun_prime) ?s"
      using pp_t_prop_eqv_at[OF agreement, of ?s] by simp
    have left:
        "pp_t_holds (A \<acute> pp_t_recurrent_fun_prime)
            (?s @ [False]) =
         pp_t_holds (B \<acute> pp_t_recurrent_fun_prime)
            (?s @ [False])"
      using pp_t_prop_eqv_at[OF agreement, of "?s @ [False]"]
      by simp
    have right:
        "pp_t_holds (A \<acute> pp_t_recurrent_fun_prime)
            (?s @ [True]) =
         pp_t_holds (B \<acute> pp_t_recurrent_fun_prime)
            (?s @ [True])"
      using pp_t_prop_eqv_at[OF agreement, of "?s @ [True]"]
      by simp
    have right_left:
        "pp_t_holds (A \<acute> pp_t_recurrent_fun_prime)
            (?s @ [True, False]) =
         pp_t_holds (B \<acute> pp_t_recurrent_fun_prime)
            (?s @ [True, False])"
      using pp_t_prop_eqv_at[
        OF agreement, of "?s @ [True, False]"]
      by simp
    show ?thesis
      unfolding pp_t_recurrent_signature_def
      using root left right right_left by simp
  qed
  show ?thesis
  proof (cases "odd n")
    case True
    show ?thesis
      using A B signature_equality
        pp_t_recurrent_signatures_odd[OF True]
      unfolding pp_t_fun_prime_probe_representatives_def
      by auto
  next
    case False
    show ?thesis
      using A B signature_equality
        pp_t_recurrent_signatures[OF False]
      unfolding pp_t_fun_prime_probe_representatives_def
      by auto
  qed
qed

lemma pp_t_recurrent_is_base_fun_prime:
  "pp_t_fun_prime_predicate pp_t_quantified_unary_pure
    (replicate n True) pp_t_recurrent_fun_prime"
proof (unfold pp_t_fun_prime_predicate_def, intro allI impI)
  fix X Y
  let ?w = "replicate n True"
  assume X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and pure:
      "pp_t_quantified_unary_pure ?w X
        \<and> pp_t_quantified_unary_pure ?w Y"
    and agreement:
      "pp_t_eqv Prop ?w
        (X \<acute> pp_t_recurrent_fun_prime)
        (Y \<acute> pp_t_recurrent_fun_prime)"
  obtain A where A_rep:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type ?w A X"
    using pp_t_fun_prime_probe_representative[
      OF pure[THEN conjunct1]] by blast
  obtain B where B_rep:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and BY:
      "pp_t_eqv pp_t_constants_unary_type ?w B Y"
    using pp_t_fun_prime_probe_representative[
      OF pure[THEN conjunct2]] by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[
      OF A_rep])
  have B_domain:
      "Elem B (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[
      OF B_rep])
  have p: "Elem pp_t_recurrent_fun_prime (pp_t_domain Prop)"
    by (rule pp_t_recurrent_fun_prime_in_domain)
  have A_X:
      "pp_t_eqv Prop ?w
        (A \<acute> pp_t_recurrent_fun_prime)
        (X \<acute> pp_t_recurrent_fun_prime)"
    by (rule pp_t_app_respects[
      OF AX p p pp_t_eqv_reflexive[OF p]])
  have B_Y:
      "pp_t_eqv Prop ?w
        (B \<acute> pp_t_recurrent_fun_prime)
        (Y \<acute> pp_t_recurrent_fun_prime)"
    by (rule pp_t_app_respects[
      OF BY p p pp_t_eqv_reflexive[OF p]])
  have AB_outputs:
      "pp_t_eqv Prop ?w
        (A \<acute> pp_t_recurrent_fun_prime)
        (B \<acute> pp_t_recurrent_fun_prime)"
    using pp_t_app_closed[OF A_domain p]
      pp_t_app_closed[OF X p]
      pp_t_app_closed[OF Y p]
      pp_t_app_closed[OF B_domain p]
      A_X agreement B_Y
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have AB: "A = B"
    by (rule pp_t_recurrent_representatives_separated[
      OF A_rep B_rep AB_outputs])
  have XB:
      "pp_t_eqv pp_t_constants_unary_type ?w X B"
    by (rule pp_t_eqv_symmetric[
      OF A_domain X AX, unfolded AB])
  show "pp_t_eqv pp_t_constants_unary_type ?w X Y"
    using pp_t_eqv_transitive[
      OF X B_domain Y XB BY] .
qed

theorem pp_t_recurrent_is_fun_prime:
  "pp_t_fun_prime_predicate pp_t_fun_prime_unary_pure
    (replicate n True) pp_t_recurrent_fun_prime"
  using pp_t_fun_prime_stabilizes[
    OF pp_t_recurrent_fun_prime_in_domain,
      of "replicate n True"]
    pp_t_recurrent_is_base_fun_prime[of n]
  by blast

theorem pp_t_recurrent_J_holds:
  "pp_t_holds
    (pp_t_quantified_fun_prime_operator \<acute>
      pp_t_recurrent_fun_prime) (replicate n True)"
  using pp_t_fun_prime_stock_J_holds_iff[
      OF pp_t_recurrent_fun_prime_in_domain,
        of "replicate n True"]
    pp_t_recurrent_is_fun_prime[of n]
  by blast

section \<open>Negation preserves the recurrent fun-prime witness\<close>

definition pp_t_recurrent_negation :: ZF where
  "pp_t_recurrent_negation =
    pp_t_negation_operator \<acute> pp_t_recurrent_fun_prime"

lemma pp_t_recurrent_negation_in_domain:
  "Elem pp_t_recurrent_negation (pp_t_domain Prop)"
  unfolding pp_t_recurrent_negation_def
  by (rule pp_t_app_closed[
    OF pp_t_negation_operator_in_domain
      pp_t_recurrent_fun_prime_in_domain])

lemma pp_t_modal_negation_dualities:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows
    "pp_t_holds
      (pp_t_necessity_operator \<acute>
        (pp_t_negation_operator \<acute> p)) w
      \<longleftrightarrow>
     pp_t_holds
      (pp_t_necessary_falsity_operator \<acute> p) w"
    "pp_t_holds
      (pp_t_possibility_operator \<acute>
        (pp_t_negation_operator \<acute> p)) w
      \<longleftrightarrow>
     pp_t_holds
      (pp_t_possible_falsity_operator \<acute> p) w"
    "pp_t_holds
      (pp_t_necessary_falsity_operator \<acute>
        (pp_t_negation_operator \<acute> p)) w
      \<longleftrightarrow>
     pp_t_holds
      (pp_t_necessity_operator \<acute> p) w"
    "pp_t_holds
      (pp_t_possible_falsity_operator \<acute>
        (pp_t_negation_operator \<acute> p)) w
      \<longleftrightarrow>
     pp_t_holds
      (pp_t_possibility_operator \<acute> p) w"
proof -
  have np:
      "Elem (pp_t_negation_operator \<acute> p)
        (pp_t_domain Prop)"
    by (rule pp_t_app_closed[
      OF pp_t_negation_operator_in_domain p])
  show "pp_t_holds
      (pp_t_necessity_operator \<acute>
        (pp_t_negation_operator \<acute> p)) w
      \<longleftrightarrow>
     pp_t_holds
      (pp_t_necessary_falsity_operator \<acute> p) w"
    unfolding pp_t_necessity_operator_holds[OF np]
      pp_t_necessary_falsity_operator_holds[OF p]
      pp_t_eqv.simps
    using pp_t_negation_operator_holds[OF p]
    by simp
  show "pp_t_holds
      (pp_t_possibility_operator \<acute>
        (pp_t_negation_operator \<acute> p)) w
      \<longleftrightarrow>
     pp_t_holds
      (pp_t_possible_falsity_operator \<acute> p) w"
    unfolding pp_t_possibility_operator_holds[OF np]
      pp_t_possible_falsity_operator_holds[OF p]
      pp_t_eqv.simps
    using pp_t_negation_operator_holds[OF p]
    by auto
  show "pp_t_holds
      (pp_t_necessary_falsity_operator \<acute>
        (pp_t_negation_operator \<acute> p)) w
      \<longleftrightarrow>
     pp_t_holds
      (pp_t_necessity_operator \<acute> p) w"
    unfolding pp_t_necessary_falsity_operator_holds[OF np]
      pp_t_necessity_operator_holds[OF p]
      pp_t_eqv.simps
    using pp_t_negation_operator_holds[OF p]
    by simp
  show "pp_t_holds
      (pp_t_possible_falsity_operator \<acute>
        (pp_t_negation_operator \<acute> p)) w
      \<longleftrightarrow>
     pp_t_holds
      (pp_t_possibility_operator \<acute> p) w"
    unfolding pp_t_possible_falsity_operator_holds[OF np]
      pp_t_possibility_operator_holds[OF p]
      pp_t_eqv.simps
    using pp_t_negation_operator_holds[OF p]
    by auto
qed

definition pp_t_recurrent_negation_signature ::
    "nat \<Rightarrow> ZF \<Rightarrow> bool list"
where
  "pp_t_recurrent_negation_signature n F = [
    pp_t_holds (F \<acute> pp_t_recurrent_negation)
      (replicate n True),
    pp_t_holds (F \<acute> pp_t_recurrent_negation)
      (replicate n True @ [False]),
    pp_t_holds (F \<acute> pp_t_recurrent_negation)
      (replicate n True @ [True]),
    pp_t_holds (F \<acute> pp_t_recurrent_negation)
      (replicate n True @ [True, False])]"

lemma pp_t_recurrent_negation_signature_permutation:
  "pp_t_recurrent_negation_signature n pp_t_identity_operator =
    pp_t_recurrent_signature n pp_t_negation_operator"
  "pp_t_recurrent_negation_signature n pp_t_negation_operator =
    pp_t_recurrent_signature n pp_t_identity_operator"
  "pp_t_recurrent_negation_signature n
      (pp_t_constant_operator True) =
    pp_t_recurrent_signature n (pp_t_constant_operator True)"
  "pp_t_recurrent_negation_signature n
      (pp_t_constant_operator False) =
    pp_t_recurrent_signature n (pp_t_constant_operator False)"
  "pp_t_recurrent_negation_signature n pp_t_necessity_operator =
    pp_t_recurrent_signature n pp_t_necessary_falsity_operator"
  "pp_t_recurrent_negation_signature n pp_t_possibility_operator =
    pp_t_recurrent_signature n pp_t_possible_falsity_operator"
  "pp_t_recurrent_negation_signature n
      pp_t_necessary_falsity_operator =
    pp_t_recurrent_signature n pp_t_necessity_operator"
  "pp_t_recurrent_negation_signature n
      pp_t_possible_falsity_operator =
    pp_t_recurrent_signature n pp_t_possibility_operator"
proof -
  have p: "Elem pp_t_recurrent_fun_prime (pp_t_domain Prop)"
    by (rule pp_t_recurrent_fun_prime_in_domain)
  have np:
      "Elem pp_t_recurrent_negation (pp_t_domain Prop)"
    by (rule pp_t_recurrent_negation_in_domain)
  have identity_p:
      "pp_t_identity_operator \<acute> pp_t_recurrent_fun_prime =
        pp_t_recurrent_fun_prime"
    using p by (simp add: pp_t_identity_operator_def Lambda_app)
  have identity_np:
      "pp_t_identity_operator \<acute> pp_t_recurrent_negation =
        pp_t_recurrent_negation"
    using np by (simp add: pp_t_identity_operator_def Lambda_app)
  show "pp_t_recurrent_negation_signature n
        pp_t_identity_operator =
      pp_t_recurrent_signature n pp_t_negation_operator"
    unfolding pp_t_recurrent_negation_signature_def
      pp_t_recurrent_signature_def
    using identity_np
    by (simp add: pp_t_recurrent_negation_def)
  show "pp_t_recurrent_negation_signature n
        pp_t_negation_operator =
      pp_t_recurrent_signature n pp_t_identity_operator"
    unfolding pp_t_recurrent_negation_signature_def
      pp_t_recurrent_signature_def pp_t_recurrent_negation_def
    using pp_t_negation_operator_holds[OF p]
      pp_t_negation_operator_holds[
        OF pp_t_app_closed[
          OF pp_t_negation_operator_in_domain p]]
      identity_p
    by simp
  show "pp_t_recurrent_negation_signature n
        (pp_t_constant_operator True) =
      pp_t_recurrent_signature n (pp_t_constant_operator True)"
    unfolding pp_t_recurrent_negation_signature_def
      pp_t_recurrent_signature_def
    using pp_t_constant_operator_holds[OF np, of True]
      pp_t_constant_operator_holds[OF p, of True]
    by simp
  show "pp_t_recurrent_negation_signature n
        (pp_t_constant_operator False) =
      pp_t_recurrent_signature n (pp_t_constant_operator False)"
    unfolding pp_t_recurrent_negation_signature_def
      pp_t_recurrent_signature_def
    using pp_t_constant_operator_holds[OF np, of False]
      pp_t_constant_operator_holds[OF p, of False]
    by simp
  show "pp_t_recurrent_negation_signature n
        pp_t_necessity_operator =
      pp_t_recurrent_signature n pp_t_necessary_falsity_operator"
    unfolding pp_t_recurrent_negation_signature_def
      pp_t_recurrent_signature_def pp_t_recurrent_negation_def
    using pp_t_modal_negation_dualities(1)[OF p] by simp
  show "pp_t_recurrent_negation_signature n
        pp_t_possibility_operator =
      pp_t_recurrent_signature n pp_t_possible_falsity_operator"
    unfolding pp_t_recurrent_negation_signature_def
      pp_t_recurrent_signature_def pp_t_recurrent_negation_def
    using pp_t_modal_negation_dualities(2)[OF p] by simp
  show "pp_t_recurrent_negation_signature n
        pp_t_necessary_falsity_operator =
      pp_t_recurrent_signature n pp_t_necessity_operator"
    unfolding pp_t_recurrent_negation_signature_def
      pp_t_recurrent_signature_def pp_t_recurrent_negation_def
    using pp_t_modal_negation_dualities(3)[OF p] by simp
  show "pp_t_recurrent_negation_signature n
        pp_t_possible_falsity_operator =
      pp_t_recurrent_signature n pp_t_possibility_operator"
    unfolding pp_t_recurrent_negation_signature_def
      pp_t_recurrent_signature_def pp_t_recurrent_negation_def
    using pp_t_modal_negation_dualities(4)[OF p] by simp
qed

lemma pp_t_representatives_separated_implies_base_fun_prime:
  assumes p: "Elem p (pp_t_domain Prop)"
    and separated:
      "\<And>A B.
        A \<in> pp_t_fun_prime_probe_representatives \<Longrightarrow>
        B \<in> pp_t_fun_prime_probe_representatives \<Longrightarrow>
        pp_t_eqv Prop w (A \<acute> p) (B \<acute> p) \<Longrightarrow>
        A = B"
  shows "pp_t_fun_prime_predicate
    pp_t_quantified_unary_pure w p"
proof (unfold pp_t_fun_prime_predicate_def, intro allI impI)
  fix X Y
  assume X: "Elem X (pp_t_domain pp_t_constants_unary_type)"
    and Y: "Elem Y (pp_t_domain pp_t_constants_unary_type)"
    and pure:
      "pp_t_quantified_unary_pure w X
        \<and> pp_t_quantified_unary_pure w Y"
    and agreement:
      "pp_t_eqv Prop w (X \<acute> p) (Y \<acute> p)"
  obtain A where A_rep:
      "A \<in> pp_t_fun_prime_probe_representatives"
    and AX:
      "pp_t_eqv pp_t_constants_unary_type w A X"
    using pp_t_fun_prime_probe_representative[
      OF pure[THEN conjunct1]] by blast
  obtain B where B_rep:
      "B \<in> pp_t_fun_prime_probe_representatives"
    and BY:
      "pp_t_eqv pp_t_constants_unary_type w B Y"
    using pp_t_fun_prime_probe_representative[
      OF pure[THEN conjunct2]] by blast
  have A_domain:
      "Elem A (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[
      OF A_rep])
  have B_domain:
      "Elem B (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_fun_prime_probe_representative_in_domain[
      OF B_rep])
  have A_X:
      "pp_t_eqv Prop w (A \<acute> p) (X \<acute> p)"
    by (rule pp_t_app_respects[
      OF AX p p pp_t_eqv_reflexive[OF p]])
  have B_Y:
      "pp_t_eqv Prop w (B \<acute> p) (Y \<acute> p)"
    by (rule pp_t_app_respects[
      OF BY p p pp_t_eqv_reflexive[OF p]])
  have AB_outputs:
      "pp_t_eqv Prop w (A \<acute> p) (B \<acute> p)"
    using pp_t_app_closed[OF A_domain p]
      pp_t_app_closed[OF X p]
      pp_t_app_closed[OF Y p]
      pp_t_app_closed[OF B_domain p]
      A_X agreement B_Y
    by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
  have AB: "A = B"
    by (rule separated[OF A_rep B_rep AB_outputs])
  have XB:
      "pp_t_eqv pp_t_constants_unary_type w X B"
    by (rule pp_t_eqv_symmetric[
      OF A_domain X AX, unfolded AB])
  show "pp_t_eqv pp_t_constants_unary_type w X Y"
    using pp_t_eqv_transitive[
      OF X B_domain Y XB BY] .
qed

lemma pp_t_recurrent_negation_representatives_separated:
  assumes A: "A \<in> pp_t_fun_prime_probe_representatives"
    and B: "B \<in> pp_t_fun_prime_probe_representatives"
    and agreement:
      "pp_t_eqv Prop (replicate n True)
        (A \<acute> pp_t_recurrent_negation)
        (B \<acute> pp_t_recurrent_negation)"
  shows "A = B"
proof -
  let ?s = "replicate n True"
  have signature_equality:
      "pp_t_recurrent_negation_signature n A =
       pp_t_recurrent_negation_signature n B"
  proof -
    have root:
        "pp_t_holds (A \<acute> pp_t_recurrent_negation) ?s =
         pp_t_holds (B \<acute> pp_t_recurrent_negation) ?s"
      using pp_t_prop_eqv_at[OF agreement, of ?s] by simp
    have left:
        "pp_t_holds (A \<acute> pp_t_recurrent_negation)
            (?s @ [False]) =
         pp_t_holds (B \<acute> pp_t_recurrent_negation)
            (?s @ [False])"
      using pp_t_prop_eqv_at[OF agreement, of "?s @ [False]"]
      by simp
    have right:
        "pp_t_holds (A \<acute> pp_t_recurrent_negation)
            (?s @ [True]) =
         pp_t_holds (B \<acute> pp_t_recurrent_negation)
            (?s @ [True])"
      using pp_t_prop_eqv_at[OF agreement, of "?s @ [True]"]
      by simp
    have right_left:
        "pp_t_holds (A \<acute> pp_t_recurrent_negation)
            (?s @ [True, False]) =
         pp_t_holds (B \<acute> pp_t_recurrent_negation)
            (?s @ [True, False])"
      using pp_t_prop_eqv_at[
        OF agreement, of "?s @ [True, False]"]
      by simp
    show ?thesis
      unfolding pp_t_recurrent_negation_signature_def
      using root left right right_left by simp
  qed
  show ?thesis
  proof (cases "odd n")
    case True
    show ?thesis
      using A B signature_equality
        pp_t_recurrent_negation_signature_permutation[of n]
        pp_t_recurrent_signatures_odd[OF True]
      unfolding pp_t_fun_prime_probe_representatives_def
      by auto
  next
    case False
    show ?thesis
      using A B signature_equality
        pp_t_recurrent_negation_signature_permutation[of n]
        pp_t_recurrent_signatures[OF False]
      unfolding pp_t_fun_prime_probe_representatives_def
      by auto
  qed
qed

lemma pp_t_recurrent_negation_is_base_fun_prime:
  "pp_t_fun_prime_predicate pp_t_quantified_unary_pure
    (replicate n True) pp_t_recurrent_negation"
  by (rule pp_t_representatives_separated_implies_base_fun_prime[
      OF pp_t_recurrent_negation_in_domain])
    (rule pp_t_recurrent_negation_representatives_separated)

theorem pp_t_recurrent_negation_is_fun_prime:
  "pp_t_fun_prime_predicate pp_t_fun_prime_unary_pure
    (replicate n True) pp_t_recurrent_negation"
  using pp_t_fun_prime_stabilizes[
    OF pp_t_recurrent_negation_in_domain,
      of "replicate n True"]
    pp_t_recurrent_negation_is_base_fun_prime[of n]
  by blast

theorem pp_t_recurrent_negation_J_holds:
  "pp_t_holds
    (pp_t_quantified_fun_prime_operator \<acute>
      pp_t_recurrent_negation) (replicate n True)"
  using pp_t_fun_prime_stock_J_holds_iff[
      OF pp_t_recurrent_negation_in_domain,
        of "replicate n True"]
    pp_t_recurrent_negation_is_fun_prime[of n]
  by blast

section \<open>The necessary-falsity collision\<close>

lemma pp_t_fun_prime_identity_is_pure:
  "pp_t_fun_prime_unary_pure w pp_t_identity_operator"
  unfolding pp_t_fun_prime_unary_pure_def
    pp_t_quantified_unary_pure_classes
  using pp_t_eqv_reflexive[
    OF pp_t_identity_operator_in_domain]
  by blast

lemma pp_t_fun_prime_negation_is_pure:
  "pp_t_fun_prime_unary_pure w pp_t_negation_operator"
  unfolding pp_t_fun_prime_unary_pure_def
    pp_t_quantified_unary_pure_classes
  using pp_t_eqv_reflexive[
    OF pp_t_negation_operator_in_domain]
  by blast

lemma pp_t_recurrent_double_negation:
  "pp_t_eqv Prop w pp_t_recurrent_fun_prime
    (pp_t_negation_operator \<acute> pp_t_recurrent_negation)"
  unfolding pp_t_eqv.simps pp_t_recurrent_negation_def
  using pp_t_negation_operator_holds[
      OF pp_t_recurrent_fun_prime_in_domain]
    pp_t_negation_operator_holds[
      OF pp_t_app_closed[
        OF pp_t_negation_operator_in_domain
          pp_t_recurrent_fun_prime_in_domain]]
  by simp

lemma pp_t_recurrent_T6_false_on_spine:
  "\<not> pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute>
      pp_t_recurrent_fun_prime) (replicate n True)"
proof
  let ?p = pp_t_recurrent_fun_prime
  let ?w = "replicate n True"
  assume Dp:
      "pp_t_holds (pp_t_fun_prime_T6_operator \<acute> ?p) ?w"
  have p: "Elem ?p (pp_t_domain Prop)"
    by (rule pp_t_recurrent_fun_prime_in_domain)
  have semantic:
      "\<forall>X.
        Elem X (pp_t_domain pp_t_constants_unary_type)
        \<longrightarrow>
        (\<forall>q.
          Elem q (pp_t_domain Prop)
          \<longrightarrow>
          (pp_t_fun_prime_unary_pure ?w X
            \<and> pp_t_holds
              (pp_t_quantified_fun_prime_operator \<acute> q) ?w
            \<and> pp_t_eqv Prop ?w ?p (X \<acute> q))
          \<longrightarrow> \<not> pp_t_holds (X \<acute> ?p) ?w)"
    using pp_t_fun_prime_T6_operator_holds[OF p, of ?w]
      Dp by blast
  show False
  proof (cases "odd n")
    case True
    have identity_p:
        "pp_t_identity_operator \<acute> ?p = ?p"
      using p by (simp add: pp_t_identity_operator_def Lambda_app)
    have antecedent:
        "pp_t_fun_prime_unary_pure ?w pp_t_identity_operator
          \<and> pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> ?p) ?w
          \<and> pp_t_eqv Prop ?w ?p
            (pp_t_identity_operator \<acute> ?p)"
      using pp_t_fun_prime_identity_is_pure[of ?w]
        pp_t_recurrent_J_holds[of n]
        pp_t_eqv_reflexive[OF p, of ?w]
      unfolding identity_p by blast
    have not_identity_p:
        "\<not> pp_t_holds
          (pp_t_identity_operator \<acute> ?p) ?w"
      using semantic pp_t_identity_operator_in_domain p
        antecedent by blast
    show False
      using not_identity_p
        pp_t_recurrent_fun_prime_spine_values(1)[of n]
        True unfolding identity_p by simp
  next
    case False
    let ?q = pp_t_recurrent_negation
    have q: "Elem ?q (pp_t_domain Prop)"
      by (rule pp_t_recurrent_negation_in_domain)
    have representation:
        "pp_t_eqv Prop ?w ?p
          (pp_t_negation_operator \<acute> ?q)"
      by (rule pp_t_recurrent_double_negation)
    have antecedent:
        "pp_t_fun_prime_unary_pure ?w pp_t_negation_operator
          \<and> pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> ?q) ?w
          \<and> pp_t_eqv Prop ?w ?p
            (pp_t_negation_operator \<acute> ?q)"
      using pp_t_fun_prime_negation_is_pure[of ?w]
        pp_t_recurrent_negation_J_holds[of n]
        representation by blast
    have not_neg_p:
        "\<not> pp_t_holds
          (pp_t_negation_operator \<acute> ?p) ?w"
      using semantic pp_t_negation_operator_in_domain q
        antecedent by blast
    show False
      using not_neg_p
        pp_t_negation_operator_holds[OF p, of ?w]
        pp_t_recurrent_fun_prime_spine_values(1)[of n]
        False by simp
  qed
qed

theorem pp_t_recurrent_T6_necessary_falsity_collision:
  "pp_t_eqv Prop []
    (pp_t_fun_prime_T6_operator \<acute>
      pp_t_recurrent_fun_prime)
    (pp_t_necessary_falsity_operator \<acute>
      pp_t_recurrent_fun_prime)"
  unfolding pp_t_eqv.simps
proof (intro allI impI)
  fix v :: "bool list"
  assume "prefix [] v"
  from pp_t_bool_list_spine_or_off_spine[
    of v] consider
      (spine) n where "v = replicate n True"
    | (off_spine) n ys where
        "v = replicate n True @ False # ys"
    by blast
  then show "pp_t_holds
      (pp_t_fun_prime_T6_operator \<acute>
        pp_t_recurrent_fun_prime) v =
    pp_t_holds
      (pp_t_necessary_falsity_operator \<acute>
        pp_t_recurrent_fun_prime) v"
  proof cases
    case spine
    have not_D:
        "\<not> pp_t_holds
          (pp_t_fun_prime_T6_operator \<acute>
            pp_t_recurrent_fun_prime) v"
      using pp_t_recurrent_T6_false_on_spine[of n]
      unfolding spine .
    have not_NF:
        "\<not> pp_t_holds
          (pp_t_necessary_falsity_operator \<acute>
            pp_t_recurrent_fun_prime) v"
      using pp_t_recurrent_modal_values(3)[of n]
      unfolding spine .
    show ?thesis using not_D not_NF by simp
  next
    case off_spine
    let ?b = "odd n"
    have settled:
        "pp_t_eqv Prop v pp_t_recurrent_fun_prime
          (pp_zf_truth ?b)"
      using pp_t_recurrent_fun_prime_off_spine_settled[
        of n ys] unfolding off_spine .
    have D_settled:
        "pp_t_eqv Prop v
          (pp_t_fun_prime_T6_operator \<acute>
            pp_t_recurrent_fun_prime)
          (pp_zf_truth (\<not> ?b))"
      by (rule pp_t_fun_prime_T6_on_settled[
        OF pp_t_recurrent_fun_prime_in_domain settled
          pp_t_fun_prime_has_witness_everywhere])
    have D_value:
        "pp_t_holds
          (pp_t_fun_prime_T6_operator \<acute>
            pp_t_recurrent_fun_prime) v = (\<not> ?b)"
      using pp_t_prop_eqv_at[OF D_settled, of v] by simp
    have NF_value:
        "pp_t_holds
          (pp_t_necessary_falsity_operator \<acute>
            pp_t_recurrent_fun_prime) v = (\<not> ?b)"
      using pp_t_settled_operator_values(3)[
        OF pp_t_recurrent_fun_prime_in_domain settled] .
    show ?thesis using D_value NF_value by simp
  qed
qed

section \<open>The collision is harmful\<close>

definition pp_t_right_tip :: ZF where
  "pp_t_right_tip = pp_t_fun_prime_probe []"

lemma pp_t_right_tip_in_domain:
  "Elem pp_t_right_tip (pp_t_domain Prop)"
  unfolding pp_t_right_tip_def
  by (rule pp_t_fun_prime_probe_in_domain)

lemma pp_t_right_tip_on_right_cone:
  assumes future: "prefix [True] v"
  shows "pp_t_holds pp_t_right_tip v \<longleftrightarrow> v = [True]"
  using future
  unfolding pp_t_right_tip_def
  by (auto simp: prefix_def)

lemma pp_t_right_tip_false_below:
  assumes future: "prefix [True] v"
  shows "\<not> pp_t_holds pp_t_right_tip (v @ [False])"
proof -
  have child_future: "prefix [True] (v @ [False])"
    using future by (auto simp: prefix_def append_assoc)
  have different: "v @ [False] \<noteq> [True]"
    by auto
  show ?thesis
    using pp_t_right_tip_on_right_cone[
      OF child_future] different by blast
qed

lemma pp_t_right_tip_not_identity_image_of_J:
  assumes q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
    and image:
      "pp_t_eqv Prop [True] pp_t_right_tip
        (pp_t_identity_operator \<acute> q)"
  shows False
proof -
  have fun_prime:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure [True] q"
    using pp_t_fun_prime_stock_J_holds_iff[
        OF q, of "[True]"]
      pp_t_fun_prime_stabilizes[OF q, of "[True]"]
      Jq by blast
  obtain u v where future_u: "prefix [True] u"
    and true_u: "pp_t_eqv Prop u q (pp_zf_truth True)"
    and "prefix [True] v"
    and "pp_t_eqv Prop v q (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF q fun_prime] by blast
  let ?r = "u @ [False]"
  have future_r: "prefix [True] ?r"
    using future_u by (auto simp: prefix_def append_assoc)
  have image_r:
      "pp_t_holds pp_t_right_tip ?r =
       pp_t_holds (pp_t_identity_operator \<acute> q) ?r"
    using pp_t_prop_eqv_at[OF image, of ?r] future_r .
  have q_r: "pp_t_holds q ?r"
    using pp_t_prop_eqv_at[OF true_u, of ?r]
    by simp
  have identity_q:
      "pp_t_identity_operator \<acute> q = q"
    using q by (simp add: pp_t_identity_operator_def Lambda_app)
  show False
    using pp_t_right_tip_false_below[OF future_u]
      image_r q_r unfolding identity_q by blast
qed

lemma pp_t_right_tip_not_truth_image:
  assumes q: "Elem q (pp_t_domain Prop)"
    and image:
      "pp_t_eqv Prop [True] pp_t_right_tip
        (pp_t_constant_operator True \<acute> q)"
  shows False
proof -
  have at_child:
      "pp_t_holds pp_t_right_tip [True, False] =
       pp_t_holds
        (pp_t_constant_operator True \<acute> q) [True, False]"
    using pp_t_prop_eqv_at[
      OF image, of "[True, False]"] by simp
  show False
    using pp_t_right_tip_false_below[of "[True]"]
      at_child pp_t_constant_operator_holds[
        OF q, of True "[True, False]"]
    by simp
qed

lemma pp_t_right_tip_not_possibility_image_of_J:
  assumes q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
    and image:
      "pp_t_eqv Prop [True] pp_t_right_tip
        (pp_t_possibility_operator \<acute> q)"
  shows False
proof -
  have fun_prime:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure [True] q"
    using pp_t_fun_prime_stock_J_holds_iff[
        OF q, of "[True]"]
      pp_t_fun_prime_stabilizes[OF q, of "[True]"]
      Jq by blast
  obtain u v where future_u: "prefix [True] u"
    and true_u: "pp_t_eqv Prop u q (pp_zf_truth True)"
    and "prefix [True] v"
    and "pp_t_eqv Prop v q (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF q fun_prime] by blast
  let ?r = "u @ [False]"
  have future_r: "prefix [True] ?r"
    using future_u by (auto simp: prefix_def append_assoc)
  have image_r:
      "pp_t_holds pp_t_right_tip ?r =
       pp_t_holds (pp_t_possibility_operator \<acute> q) ?r"
    using pp_t_prop_eqv_at[OF image, of ?r] future_r .
  have q_r: "pp_t_holds q ?r"
    using pp_t_prop_eqv_at[OF true_u, of ?r]
    by simp
  have possible_r:
      "pp_t_holds (pp_t_possibility_operator \<acute> q) ?r"
    unfolding pp_t_possibility_operator_holds[OF q]
    using q_r by blast
  show False
    using pp_t_right_tip_false_below[OF future_u]
      image_r possible_r by blast
qed

lemma pp_t_right_tip_not_possible_falsity_image_of_J:
  assumes q: "Elem q (pp_t_domain Prop)"
    and Jq:
      "pp_t_holds
        (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
    and image:
      "pp_t_eqv Prop [True] pp_t_right_tip
        (pp_t_possible_falsity_operator \<acute> q)"
  shows False
proof -
  have fun_prime:
      "pp_t_fun_prime_predicate
        pp_t_quantified_unary_pure [True] q"
    using pp_t_fun_prime_stock_J_holds_iff[
        OF q, of "[True]"]
      pp_t_fun_prime_stabilizes[OF q, of "[True]"]
      Jq by blast
  obtain u v where "prefix [True] u"
    and "pp_t_eqv Prop u q (pp_zf_truth True)"
    and future_v: "prefix [True] v"
    and false_v: "pp_t_eqv Prop v q (pp_zf_truth False)"
    using pp_t_base_injective_has_homogeneous_cones[
      OF q fun_prime] by blast
  let ?r = "v @ [False]"
  have future_r: "prefix [True] ?r"
    using future_v by (auto simp: prefix_def append_assoc)
  have image_r:
      "pp_t_holds pp_t_right_tip ?r =
       pp_t_holds
        (pp_t_possible_falsity_operator \<acute> q) ?r"
    using pp_t_prop_eqv_at[OF image, of ?r] future_r .
  have false_r:
      "pp_t_eqv Prop ?r q (pp_zf_truth False)"
    by (rule pp_t_eqv_persistent[OF false_v])
      simp
  have possible_false_r:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute> q) ?r"
    using pp_t_settled_operator_values(4)[OF q false_r]
    by simp
  show False
    using pp_t_right_tip_false_below[OF future_v]
      image_r possible_false_r by blast
qed

theorem pp_t_right_tip_T6_holds:
  "pp_t_holds
    (pp_t_fun_prime_T6_operator \<acute> pp_t_right_tip) [True]"
proof -
  have p: "Elem pp_t_right_tip (pp_t_domain Prop)"
    by (rule pp_t_right_tip_in_domain)
  show ?thesis
    unfolding pp_t_fun_prime_T6_operator_holds[OF p]
  proof (intro allI impI)
    fix X q
    assume X:
        "Elem X (pp_t_domain pp_t_constants_unary_type)"
      and q: "Elem q (pp_t_domain Prop)"
      and antecedent:
        "pp_t_fun_prime_unary_pure [True] X
          \<and> pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute> q) [True]
          \<and> pp_t_eqv Prop [True] pp_t_right_tip (X \<acute> q)"
    have pure_X: "pp_t_fun_prime_unary_pure [True] X"
      using antecedent by blast
    have Jq:
        "pp_t_holds
          (pp_t_quantified_fun_prime_operator \<acute> q) [True]"
      using antecedent by blast
    have p_Xq:
        "pp_t_eqv Prop [True] pp_t_right_tip (X \<acute> q)"
      using antecedent by blast
    from pure_X consider
        (old) "pp_t_quantified_unary_pure [True] X"
      | (added)
          "pp_t_eqv pp_t_constants_unary_type [True]
            pp_t_quantified_fun_prime_operator X"
      unfolding pp_t_fun_prime_unary_pure_def by blast
    then show "\<not> pp_t_holds (X \<acute> pp_t_right_tip) [True]"
    proof cases
      case added
      have J_p_collision:
          "pp_t_eqv Prop [True]
            (pp_t_quantified_fun_prime_operator \<acute> pp_t_right_tip)
            (X \<acute> pp_t_right_tip)"
        by (rule pp_t_app_respects[
          OF added p p pp_t_eqv_reflexive[OF p]])
      have not_Jp:
          "\<not> pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute>
              pp_t_right_tip) [True]"
      proof
        assume Jp:
            "pp_t_holds
              (pp_t_quantified_fun_prime_operator \<acute>
                pp_t_right_tip) [True]"
        have base:
            "pp_t_fun_prime_predicate
              pp_t_quantified_unary_pure [True] pp_t_right_tip"
          using pp_t_fun_prime_stock_J_holds_iff[
              OF p, of "[True]"]
            pp_t_fun_prime_stabilizes[OF p, of "[True]"]
            Jp by blast
        obtain u v where future_u: "prefix [True] u"
          and true_u:
            "pp_t_eqv Prop u pp_t_right_tip
              (pp_zf_truth True)"
          and "prefix [True] v"
          and "pp_t_eqv Prop v pp_t_right_tip
            (pp_zf_truth False)"
          using pp_t_base_injective_has_homogeneous_cones[
            OF p base] by blast
        have tip_child:
            "\<not> pp_t_holds pp_t_right_tip (u @ [False])"
          by (rule pp_t_right_tip_false_below[OF future_u])
        have tip_child_true:
            "pp_t_holds pp_t_right_tip (u @ [False])"
          using pp_t_prop_eqv_at[
            OF true_u, of "u @ [False]"] by simp
        show False using tip_child tip_child_true by blast
      qed
      have at_w:
          "pp_t_holds
            (pp_t_quantified_fun_prime_operator \<acute>
              pp_t_right_tip) [True]
          =
          pp_t_holds (X \<acute> pp_t_right_tip) [True]"
        using pp_t_prop_eqv_at[
          OF J_p_collision, of "[True]"] by simp
      show ?thesis using not_Jp at_w by blast
    next
      case old
      obtain A where A_rep:
          "A \<in> pp_t_fun_prime_probe_representatives"
        and AX:
          "pp_t_eqv pp_t_constants_unary_type [True] A X"
        using pp_t_fun_prime_probe_representative[OF old]
        by blast
      have A_domain:
          "Elem A (pp_t_domain pp_t_constants_unary_type)"
        by (rule pp_t_fun_prime_probe_representative_in_domain[
          OF A_rep])
      have Aq_Xq:
          "pp_t_eqv Prop [True] (A \<acute> q) (X \<acute> q)"
        by (rule pp_t_app_respects[
          OF AX q q pp_t_eqv_reflexive[OF q]])
      have p_Aq:
          "pp_t_eqv Prop [True] pp_t_right_tip (A \<acute> q)"
        using p q A_domain X
          pp_t_app_closed[OF A_domain q]
          pp_t_app_closed[OF X q]
          p_Xq Aq_Xq
        by (meson pp_t_eqv_symmetric pp_t_eqv_transitive)
      have Ap_Xp:
          "pp_t_eqv Prop [True]
            (A \<acute> pp_t_right_tip)
            (X \<acute> pp_t_right_tip)"
        by (rule pp_t_app_respects[
          OF AX p p pp_t_eqv_reflexive[OF p]])
      have output_transfer:
          "pp_t_holds (A \<acute> pp_t_right_tip) [True] =
           pp_t_holds (X \<acute> pp_t_right_tip) [True]"
        using pp_t_prop_eqv_at[
          OF Ap_Xp, of "[True]"] by simp
      from A_rep consider
          (identity) "A = pp_t_identity_operator"
        | (negation) "A = pp_t_negation_operator"
        | (truth) "A = pp_t_constant_operator True"
        | (falsity) "A = pp_t_constant_operator False"
        | (necessity) "A = pp_t_necessity_operator"
        | (possibility) "A = pp_t_possibility_operator"
        | (necessary_falsity)
            "A = pp_t_necessary_falsity_operator"
        | (possible_falsity)
            "A = pp_t_possible_falsity_operator"
        unfolding pp_t_fun_prime_probe_representatives_def
        by auto
      then show ?thesis
      proof cases
        case identity
        show ?thesis
          using pp_t_right_tip_not_identity_image_of_J[
            OF q Jq, unfolded identity[symmetric], OF p_Aq]
          by blast
      next
        case truth
        show ?thesis
          using pp_t_right_tip_not_truth_image[
            OF q, unfolded truth[symmetric], OF p_Aq]
          by blast
      next
        case possibility
        show ?thesis
          using pp_t_right_tip_not_possibility_image_of_J[
            OF q Jq, unfolded possibility[symmetric], OF p_Aq]
          by blast
      next
        case possible_falsity
        show ?thesis
          using pp_t_right_tip_not_possible_falsity_image_of_J[
            OF q Jq,
              unfolded possible_falsity[symmetric], OF p_Aq]
          by blast
      next
        case negation
        have not_Ap:
            "\<not> pp_t_holds
              (A \<acute> pp_t_right_tip) [True]"
          using pp_t_fun_prime_probe_signatures(2)[of "[]"]
          unfolding pp_t_fun_prime_probe_signature_def
            pp_t_right_tip_def negation by simp
        show ?thesis using not_Ap output_transfer by blast
      next
        case falsity
        have not_Ap:
            "\<not> pp_t_holds
              (A \<acute> pp_t_right_tip) [True]"
          using pp_t_fun_prime_probe_signatures(4)[of "[]"]
          unfolding pp_t_fun_prime_probe_signature_def
            pp_t_right_tip_def falsity by simp
        show ?thesis using not_Ap output_transfer by blast
      next
        case necessity
        have not_Ap:
            "\<not> pp_t_holds
              (A \<acute> pp_t_right_tip) [True]"
          using pp_t_fun_prime_probe_signatures(5)[of "[]"]
          unfolding pp_t_fun_prime_probe_signature_def
            pp_t_right_tip_def necessity by simp
        show ?thesis using not_Ap output_transfer by blast
      next
        case necessary_falsity
        have not_Ap:
            "\<not> pp_t_holds
              (A \<acute> pp_t_right_tip) [True]"
          using pp_t_fun_prime_probe_signatures(7)[of "[]"]
          unfolding pp_t_fun_prime_probe_signature_def
            pp_t_right_tip_def necessary_falsity by simp
        show ?thesis using not_Ap output_transfer by blast
      qed
    qed
  qed
qed

lemma pp_t_right_tip_necessary_falsity_fails:
  "\<not> pp_t_holds
    (pp_t_necessary_falsity_operator \<acute> pp_t_right_tip) [True]"
  using pp_t_fun_prime_probe_signatures(7)[of "[]"]
  unfolding pp_t_fun_prime_probe_signature_def pp_t_right_tip_def
  by simp

theorem pp_t_T6_not_necessary_falsity:
  "\<not> pp_t_eqv pp_t_constants_unary_type []
    pp_t_fun_prime_T6_operator
    pp_t_necessary_falsity_operator"
proof
  assume operators:
      "pp_t_eqv pp_t_constants_unary_type []
        pp_t_fun_prime_T6_operator
        pp_t_necessary_falsity_operator"
  have p: "Elem pp_t_right_tip (pp_t_domain Prop)"
    by (rule pp_t_right_tip_in_domain)
  have applications:
      "pp_t_eqv Prop []
        (pp_t_fun_prime_T6_operator \<acute> pp_t_right_tip)
        (pp_t_necessary_falsity_operator \<acute> pp_t_right_tip)"
    by (rule pp_t_app_respects[
      OF operators p p pp_t_eqv_reflexive[OF p]])
  have at_right:
      "pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute> pp_t_right_tip) [True]
      =
      pp_t_holds
        (pp_t_necessary_falsity_operator \<acute> pp_t_right_tip)
        [True]"
    using pp_t_prop_eqv_at[
      OF applications, of "[True]"] by simp
  show False
    using pp_t_right_tip_T6_holds
      pp_t_right_tip_necessary_falsity_fails at_right
    by blast
qed

theorem pp_t_recurrent_no_negation_collision:
  "\<not> pp_t_eqv Prop []
    (pp_t_fun_prime_T6_operator \<acute>
      pp_t_recurrent_fun_prime)
    (pp_t_negation_operator \<acute>
      pp_t_recurrent_fun_prime)"
proof
  assume collision:
      "pp_t_eqv Prop []
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime)
        (pp_t_negation_operator \<acute>
          pp_t_recurrent_fun_prime)"
  have at_root:
      "pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime) []
      =
      pp_t_holds
        (pp_t_negation_operator \<acute>
          pp_t_recurrent_fun_prime) []"
    using pp_t_prop_eqv_at[OF collision, of "[]"] by simp
  have not_D:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime) []"
    using pp_t_recurrent_T6_false_on_spine[of 0] by simp
  have negation:
      "pp_t_holds
        (pp_t_negation_operator \<acute>
          pp_t_recurrent_fun_prime) []"
    using pp_t_negation_operator_holds[
        OF pp_t_recurrent_fun_prime_in_domain, of "[]"]
      pp_t_recurrent_fun_prime_spine_values(1)[of 0]
    by simp
  show False using at_root not_D negation by blast
qed

theorem pp_t_recurrent_no_possible_falsity_collision:
  "\<not> pp_t_eqv Prop []
    (pp_t_fun_prime_T6_operator \<acute>
      pp_t_recurrent_fun_prime)
    (pp_t_possible_falsity_operator \<acute>
      pp_t_recurrent_fun_prime)"
proof
  assume collision:
      "pp_t_eqv Prop []
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime)
        (pp_t_possible_falsity_operator \<acute>
          pp_t_recurrent_fun_prime)"
  have at_root:
      "pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime) []
      =
      pp_t_holds
        (pp_t_possible_falsity_operator \<acute>
          pp_t_recurrent_fun_prime) []"
    using pp_t_prop_eqv_at[OF collision, of "[]"] by simp
  have not_D:
      "\<not> pp_t_holds
        (pp_t_fun_prime_T6_operator \<acute>
          pp_t_recurrent_fun_prime) []"
    using pp_t_recurrent_T6_false_on_spine[of 0] by simp
  have possible_falsity:
      "pp_t_holds
        (pp_t_possible_falsity_operator \<acute>
          pp_t_recurrent_fun_prime) []"
    using pp_t_recurrent_modal_values(4)[of 0] by simp
  show False using at_root not_D possible_falsity by blast
qed

theorem pp_t_T6_diagonal_does_not_absorb_fun_prime:
  "\<not> pp_t_T6_diagonal_absorbs_fun_prime"
proof -
  have witness:
      "\<exists>w p.
        Elem p (pp_t_domain Prop)
        \<and> pp_t_fun_prime_predicate
          pp_t_fun_prime_unary_pure w p
        \<and>
        ((pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_negation_operator \<acute> p)
          \<and> \<not> pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator pp_t_negation_operator)
        \<or>
        (pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_necessary_falsity_operator \<acute> p)
          \<and> \<not> pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator
              pp_t_necessary_falsity_operator)
        \<or>
        (pp_t_eqv Prop w
            (pp_t_fun_prime_T6_operator \<acute> p)
            (pp_t_possible_falsity_operator \<acute> p)
          \<and> \<not> pp_t_eqv pp_t_constants_unary_type
            w pp_t_fun_prime_T6_operator
              pp_t_possible_falsity_operator))"
  proof (intro exI[of _ "[]"]
      exI[of _ pp_t_recurrent_fun_prime] conjI)
    show "Elem pp_t_recurrent_fun_prime (pp_t_domain Prop)"
      by (rule pp_t_recurrent_fun_prime_in_domain)
    show "pp_t_fun_prime_predicate
        pp_t_fun_prime_unary_pure [] pp_t_recurrent_fun_prime"
      using pp_t_recurrent_is_fun_prime[of 0] by simp
    show "(pp_t_eqv Prop []
          (pp_t_fun_prime_T6_operator \<acute>
            pp_t_recurrent_fun_prime)
          (pp_t_negation_operator \<acute>
            pp_t_recurrent_fun_prime)
        \<and> \<not> pp_t_eqv pp_t_constants_unary_type []
          pp_t_fun_prime_T6_operator pp_t_negation_operator)
      \<or>
      (pp_t_eqv Prop []
          (pp_t_fun_prime_T6_operator \<acute>
            pp_t_recurrent_fun_prime)
          (pp_t_necessary_falsity_operator \<acute>
            pp_t_recurrent_fun_prime)
        \<and> \<not> pp_t_eqv pp_t_constants_unary_type []
          pp_t_fun_prime_T6_operator
            pp_t_necessary_falsity_operator)
      \<or>
      (pp_t_eqv Prop []
          (pp_t_fun_prime_T6_operator \<acute>
            pp_t_recurrent_fun_prime)
          (pp_t_possible_falsity_operator \<acute>
            pp_t_recurrent_fun_prime)
        \<and> \<not> pp_t_eqv pp_t_constants_unary_type []
          pp_t_fun_prime_T6_operator
            pp_t_possible_falsity_operator)"
      using pp_t_recurrent_T6_necessary_falsity_collision
        pp_t_T6_not_necessary_falsity by blast
  qed
  show ?thesis
    using pp_t_T6_diagonal_absorption_failure_iff
      witness by blast
qed

corollary pp_t_T6_diagonal_fun_prime_operator_does_not_stabilize:
  "pp_t_T6_diagonal_fun_prime_operator
    \<noteq> pp_t_quantified_fun_prime_operator"
  using pp_t_T6_diagonal_fun_prime_operator_stabilizes_iff
    pp_t_T6_diagonal_does_not_absorb_fun_prime
  by blast

corollary pp_t_T6_diagonal_no_joint_fixed_point:
  "\<not> pp_t_T6_diagonal_joint_fixed_point"
  unfolding pp_t_T6_diagonal_joint_fixed_point_def
  using pp_t_T6_diagonal_fun_prime_operator_does_not_stabilize
  by blast

end
