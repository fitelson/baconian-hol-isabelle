theory Bacon_PP_ZF_Goodman_L2_Higher_Order_Quantifiers
  imports Bacon_PP_ZF_Goodman_L2_Composition_Fragment
begin

section \<open>Closed logical operators with higher-order quantifiers\<close>

text \<open>
  We now inspect closed logical unary terms whose outer construction is not a
  composition word.  The first reduction is a semantic Leibniz theorem at
  every object-language type.  Quantifying over the full domain of predicates
  of type \<open>\<sigma> \<rightarrow> Prop\<close> recovers Bacon's world-relative identity at
  type \<open>\<sigma>\<close>.
\<close>

lemma pp_t_eqv_classifier_admissible:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
  shows "pp_t_predicate_admissible \<sigma>
    (\<lambda>w y. pp_t_eqv \<sigma> w x y)"
proof (unfold pp_t_predicate_admissible_def,
    intro allI impI)
  fix w y z v
  assume y: "Elem y (pp_t_domain \<sigma>)"
    and z: "Elem z (pp_t_domain \<sigma>)"
    and yz: "pp_t_eqv \<sigma> w y z"
    and future: "prefix w v"
  have yz_v: "pp_t_eqv \<sigma> v y z"
    using yz future by (rule pp_t_eqv_persistent)
  have zy_v: "pp_t_eqv \<sigma> v z y"
    using y z yz_v by (rule pp_t_eqv_symmetric)
  show "pp_t_eqv \<sigma> v x y \<longleftrightarrow>
      pp_t_eqv \<sigma> v x z"
  proof
    assume xy: "pp_t_eqv \<sigma> v x y"
    show "pp_t_eqv \<sigma> v x z"
      using x y z xy yz_v by (rule pp_t_eqv_transitive)
  next
    assume xz: "pp_t_eqv \<sigma> v x z"
    show "pp_t_eqv \<sigma> v x y"
      using x z y xz zy_v by (rule pp_t_eqv_transitive)
  qed
qed

theorem pp_t_leibniz_imp_iff_eqv:
  assumes x: "Elem x (pp_t_domain \<sigma>)"
    and y: "Elem y (pp_t_domain \<sigma>)"
  shows "(\<forall>F.
      Elem F (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      (pp_t_holds (F \<acute> x) w \<longrightarrow>
       pp_t_holds (F \<acute> y) w))
    \<longleftrightarrow> pp_t_eqv \<sigma> w x y"
proof
  assume predicates:
      "\<forall>F.
        Elem F (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
        (pp_t_holds (F \<acute> x) w \<longrightarrow>
         pp_t_holds (F \<acute> y) w)"
  let ?E = "pp_t_classifier \<sigma>
    (\<lambda>v z. pp_t_eqv \<sigma> v x z)"
  have E_domain:
      "Elem ?E (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_t_eqv_classifier_admissible[OF x]
    by (rule pp_t_classifier_in_domain)
  have E_x: "pp_t_holds (?E \<acute> x) w"
    using pp_t_classifier_holds[OF x,
      of "\<lambda>v z. pp_t_eqv \<sigma> v x z" w]
      pp_t_eqv_reflexive[OF x]
    by simp
  have E_y: "pp_t_holds (?E \<acute> y) w"
    using predicates E_domain E_x by blast
  show "pp_t_eqv \<sigma> w x y"
    using E_y
      pp_t_classifier_holds[OF y,
        of "\<lambda>v z. pp_t_eqv \<sigma> v x z" w]
    by simp
next
  assume xy: "pp_t_eqv \<sigma> w x y"
  show "\<forall>F.
      Elem F (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
      (pp_t_holds (F \<acute> x) w \<longrightarrow>
       pp_t_holds (F \<acute> y) w)"
  proof (intro allI impI)
    fix F
    assume F: "Elem F (pp_t_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      and at_x: "pp_t_holds (F \<acute> x) w"
    have outputs:
        "pp_t_eqv Prop w (F \<acute> x) (F \<acute> y)"
      using F x y xy by (rule pp_t_arrow_member_respects)
    have at_w:
        "pp_t_holds (F \<acute> x) w \<longleftrightarrow>
         pp_t_holds (F \<acute> y) w"
      using pp_t_prop_eqv_at[OF outputs, of w] by simp
    show "pp_t_holds (F \<acute> y) w"
      using at_x at_w by blast
  qed
qed

lemma pp_t_eval_ObjFalse:
  "pp_t_eval C \<rho> ObjFalse = pp_zf_truth False"
proof (rule pp_t_prop_ext)
  show "Elem (pp_t_eval C \<rho> ObjFalse) (pp_t_domain Prop)"
    unfolding ObjFalse_def
    by (simp only: pp_t_eval.simps; rule pp_t_prop_in_domain)
  show "Elem (pp_zf_truth False) (pp_t_domain Prop)"
    by (rule pp_t_truth_in_domain)
  fix w
  show "pp_t_holds (pp_t_eval C \<rho> ObjFalse) w \<longleftrightarrow>
      pp_t_holds (pp_zf_truth False) w"
    by (simp add: ObjFalse_def pp_t_eval_ObjTrue)
qed

subsection \<open>Leibniz tests of truth and falsity\<close>

definition pp_t_HO_leibniz_truth_term :: oterm where
  "pp_t_HO_leibniz_truth_term =
    Lam Prop
      (Forall (Prop \<rightarrow>\<^sub>o Prop)
        (Imp
          (App (Var 0) ObjTrue)
          (App (Var 0) (Var 1))))"

definition pp_t_HO_leibniz_false_term :: oterm where
  "pp_t_HO_leibniz_false_term =
    Lam Prop
      (Forall (Prop \<rightarrow>\<^sub>o Prop)
        (Imp
          (App (Var 0) ObjFalse)
          (App (Var 0) (Var 1))))"

definition pp_t_HO_not_leibniz_truth_term :: oterm where
  "pp_t_HO_not_leibniz_truth_term =
    Lam Prop
      (Neg
        (Forall (Prop \<rightarrow>\<^sub>o Prop)
          (Imp
            (App (Var 0) ObjTrue)
            (App (Var 0) (Var 1)))))"

definition pp_t_HO_not_leibniz_false_term :: oterm where
  "pp_t_HO_not_leibniz_false_term =
    Lam Prop
      (Neg
        (Forall (Prop \<rightarrow>\<^sub>o Prop)
          (Imp
            (App (Var 0) ObjFalse)
            (App (Var 0) (Var 1)))))"

lemma pp_t_HO_leibniz_terms_typed:
  "[] \<turnstile> pp_t_HO_leibniz_truth_term :
    (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_HO_leibniz_false_term :
    (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_HO_not_leibniz_truth_term :
    (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_HO_not_leibniz_false_term :
    (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound;
      simp add: pp_t_HO_leibniz_truth_term_def
        pp_t_HO_leibniz_false_term_def
        pp_t_HO_not_leibniz_truth_term_def
        pp_t_HO_not_leibniz_false_term_def
        ObjFalse_def ObjTrue_def lookup_def)+

lemma pp_t_HO_leibniz_terms_logical:
  "pp_logical_vocabulary pp_t_HO_leibniz_truth_term"
  "pp_logical_vocabulary pp_t_HO_leibniz_false_term"
  "pp_logical_vocabulary pp_t_HO_not_leibniz_truth_term"
  "pp_logical_vocabulary pp_t_HO_not_leibniz_false_term"
  by (simp_all add: pp_logical_vocabulary_def
      pp_t_HO_leibniz_truth_term_def
      pp_t_HO_leibniz_false_term_def
      pp_t_HO_not_leibniz_truth_term_def
      pp_t_HO_not_leibniz_false_term_def
      ObjFalse_def ObjTrue_def)

lemma pp_t_HO_leibniz_truth_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_HO_leibniz_truth_term) \<acute> p) w
    \<longleftrightarrow>
      pp_t_eqv Prop w p (pp_zf_truth True)"
proof -
  have raw:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_leibniz_truth_term) \<acute> p) w
      \<longleftrightarrow>
        (\<forall>F.
          Elem F (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
          (pp_t_holds (F \<acute> pp_zf_truth True) w \<longrightarrow>
           pp_t_holds (F \<acute> p) w))"
    using p
    by (simp add: pp_t_closed_den_def
        pp_t_HO_leibniz_truth_term_def
        pp_t_eval_ObjTrue Lambda_app)
  have leibniz:
      "(\<forall>F.
          Elem F (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
          (pp_t_holds (F \<acute> pp_zf_truth True) w \<longrightarrow>
           pp_t_holds (F \<acute> p) w))
      \<longleftrightarrow>
        pp_t_eqv Prop w (pp_zf_truth True) p"
    using pp_t_truth_in_domain p
    by (rule pp_t_leibniz_imp_iff_eqv)
  have symmetry:
      "pp_t_eqv Prop w (pp_zf_truth True) p
      \<longleftrightarrow>
       pp_t_eqv Prop w p (pp_zf_truth True)"
    using pp_t_truth_in_domain p
      pp_t_eqv_symmetric by blast
  show ?thesis
    using raw leibniz symmetry by blast
qed

lemma pp_t_HO_leibniz_false_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_HO_leibniz_false_term) \<acute> p) w
    \<longleftrightarrow>
      pp_t_eqv Prop w p (pp_zf_truth False)"
proof -
  have raw:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_leibniz_false_term) \<acute> p) w
      \<longleftrightarrow>
        (\<forall>F.
          Elem F (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
          (pp_t_holds (F \<acute> pp_zf_truth False) w \<longrightarrow>
           pp_t_holds (F \<acute> p) w))"
    using p
    by (simp add: pp_t_closed_den_def
        pp_t_HO_leibniz_false_term_def
        pp_t_eval_ObjFalse Lambda_app)
  have leibniz:
      "(\<forall>F.
          Elem F (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
          (pp_t_holds (F \<acute> pp_zf_truth False) w \<longrightarrow>
           pp_t_holds (F \<acute> p) w))
      \<longleftrightarrow>
        pp_t_eqv Prop w (pp_zf_truth False) p"
    using pp_t_truth_in_domain p
    by (rule pp_t_leibniz_imp_iff_eqv)
  have symmetry:
      "pp_t_eqv Prop w (pp_zf_truth False) p
      \<longleftrightarrow>
       pp_t_eqv Prop w p (pp_zf_truth False)"
    using pp_t_truth_in_domain p
      pp_t_eqv_symmetric by blast
  show ?thesis
    using raw leibniz symmetry by blast
qed

lemma pp_t_HO_not_leibniz_truth_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_HO_not_leibniz_truth_term) \<acute> p) w
    \<longleftrightarrow>
      \<not> pp_t_eqv Prop w p (pp_zf_truth True)"
proof -
  have negation:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_not_leibniz_truth_term)
          \<acute> p) w
      \<longleftrightarrow>
        \<not> pp_t_holds
          ((pp_t_closed_den pp_t_HO_leibniz_truth_term)
            \<acute> p) w"
    using p
    by (simp add: pp_t_closed_den_def
        pp_t_HO_not_leibniz_truth_term_def
        pp_t_HO_leibniz_truth_term_def Lambda_app)
  show ?thesis
    using negation pp_t_HO_leibniz_truth_holds[OF p, of w]
    by blast
qed

lemma pp_t_HO_not_leibniz_false_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      ((pp_t_closed_den pp_t_HO_not_leibniz_false_term) \<acute> p) w
    \<longleftrightarrow>
      \<not> pp_t_eqv Prop w p (pp_zf_truth False)"
proof -
  have negation:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_not_leibniz_false_term)
          \<acute> p) w
      \<longleftrightarrow>
        \<not> pp_t_holds
          ((pp_t_closed_den pp_t_HO_leibniz_false_term)
            \<acute> p) w"
    using p
    by (simp add: pp_t_closed_den_def
        pp_t_HO_not_leibniz_false_term_def
        pp_t_HO_leibniz_false_term_def Lambda_app)
  show ?thesis
    using negation pp_t_HO_leibniz_false_holds[OF p, of w]
    by blast
qed

subsection \<open>Unrestricted application quantifiers\<close>

definition pp_t_HO_forall_application_term :: oterm where
  "pp_t_HO_forall_application_term =
    Lam Prop
      (Forall (Prop \<rightarrow>\<^sub>o Prop)
        (App (Var 0) (Var 1)))"

definition pp_t_HO_exists_application_term :: oterm where
  "pp_t_HO_exists_application_term =
    Lam Prop
      (Exists (Prop \<rightarrow>\<^sub>o Prop)
        (App (Var 0) (Var 1)))"

lemma pp_t_HO_application_terms_typed:
  "[] \<turnstile> pp_t_HO_forall_application_term :
    (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_t_HO_exists_application_term :
    (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound;
      simp add: pp_t_HO_forall_application_term_def
        pp_t_HO_exists_application_term_def lookup_def)+

lemma pp_t_HO_application_terms_logical:
  "pp_logical_vocabulary pp_t_HO_forall_application_term"
  "pp_logical_vocabulary pp_t_HO_exists_application_term"
  by (simp_all add: pp_logical_vocabulary_def
      pp_t_HO_forall_application_term_def
      pp_t_HO_exists_application_term_def)

lemma pp_t_HO_forall_application_never_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "\<not> pp_t_holds
    ((pp_t_closed_den pp_t_HO_forall_application_term) \<acute> p) w"
proof
  assume universal:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_forall_application_term) \<acute> p) w"
  have raw:
      "\<forall>F.
        Elem F (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<longrightarrow>
        pp_t_holds (F \<acute> p) w"
    using universal p
    by (simp add: pp_t_closed_den_def
        pp_t_HO_forall_application_term_def Lambda_app)
  have default:
      "Elem (pp_t_default (Prop \<rightarrow>\<^sub>o Prop))
        (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
    by (rule pp_t_default_in_domain)
  have "pp_t_holds
      ((pp_t_default (Prop \<rightarrow>\<^sub>o Prop)) \<acute> p) w"
    using raw default by blast
  then have at_empty:
      "Elem (nat2Nat (pp_t_encode w)) Empty"
    using p
    by (simp add: Lambda_app pp_t_holds_def)
  have no_empty:
      "\<not> Elem (nat2Nat (pp_t_encode w)) Empty"
    by (rule Empty)
  show False
    using at_empty no_empty by contradiction
qed

lemma pp_t_HO_exists_application_always_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
    ((pp_t_closed_den pp_t_HO_exists_application_term) \<acute> p) w"
proof -
  let ?T =
      "Lambda (pp_t_domain Prop) (\<lambda>_. pp_zf_truth True)"
  have T_domain:
      "Elem ?T (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop))"
  proof (rule pp_t_lambda_closed)
    show "\<And>x. Elem x (pp_t_domain Prop) \<Longrightarrow>
        Elem (pp_zf_truth True) (pp_t_domain Prop)"
      by (rule pp_t_truth_in_domain)
    show "\<And>v x y.
        Elem x (pp_t_domain Prop) \<Longrightarrow>
        Elem y (pp_t_domain Prop) \<Longrightarrow>
        pp_t_eqv Prop v x y \<Longrightarrow>
        pp_t_eqv Prop v (pp_zf_truth True) (pp_zf_truth True)"
      using pp_t_truth_in_domain
      by (rule pp_t_eqv_reflexive)
  qed
  have witness: "pp_t_holds (?T \<acute> p) w"
    using p by (simp add: Lambda_app)
  have raw:
      "pp_t_holds
        ((pp_t_closed_den pp_t_HO_exists_application_term) \<acute> p) w
      \<longleftrightarrow>
        (\<exists>F.
          Elem F (pp_t_domain (Prop \<rightarrow>\<^sub>o Prop)) \<and>
          pp_t_holds (F \<acute> p) w)"
    using p
    by (simp add: pp_t_closed_den_def
        pp_t_HO_exists_application_term_def Lambda_app)
  show ?thesis
    using raw T_domain witness by blast
qed

subsection \<open>Boolean denotations and the L2 search\<close>

definition pp_b_necessary_false :: pp_b_operator where
  "pp_b_necessary_false P = pp_b_box (- P)"

definition pp_b_possible_false :: pp_b_operator where
  "pp_b_possible_false P = pp_b_diamond (- P)"

lemma pp_b_operator_of_HO_terms:
  "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_leibniz_truth_term) = pp_b_box"
  "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_leibniz_false_term) =
        pp_b_necessary_false"
  "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_not_leibniz_truth_term) =
        pp_b_possible_false"
  "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_not_leibniz_false_term) =
        pp_b_diamond"
  "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_forall_application_term) =
        pp_b_const_false"
  "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_exists_application_term) =
        pp_b_const_true"
proof -
  show "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_leibniz_truth_term) = pp_b_box"
  proof (rule ext, rule set_eqI)
    fix P w
    have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    show "w \<in> pp_b_operator_of
          (pp_t_closed_den pp_t_HO_leibniz_truth_term) P
        \<longleftrightarrow> w \<in> pp_b_box P"
      unfolding pp_b_operator_of_def pp_b_of_zf_def
      using pp_t_HO_leibniz_truth_holds[OF p, of w]
        pp_t_zf_of_b_eqv_true_iff[of w P]
      by simp
  qed
next
  show "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_leibniz_false_term) =
        pp_b_necessary_false"
  proof (rule ext, rule set_eqI)
    fix P w
    have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    show "w \<in> pp_b_operator_of
          (pp_t_closed_den pp_t_HO_leibniz_false_term) P
        \<longleftrightarrow> w \<in> pp_b_necessary_false P"
      unfolding pp_b_operator_of_def pp_b_of_zf_def
        pp_b_necessary_false_def
      using pp_t_HO_leibniz_false_holds[OF p, of w]
        pp_t_zf_of_b_eqv_false_iff[of w P]
      by simp
  qed
next
  show "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_not_leibniz_truth_term) =
        pp_b_possible_false"
  proof (rule ext, rule set_eqI)
    fix P w
    have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    have term_semantics:
        "pp_t_holds
          ((pp_t_closed_den pp_t_HO_not_leibniz_truth_term) \<acute>
            pp_zf_of_b P) w
        \<longleftrightarrow>
          (\<exists>v. prefix w v \<and> v \<notin> P)"
      using pp_t_HO_not_leibniz_truth_holds[OF p, of w]
        pp_t_zf_of_b_eqv_true_iff[of w P]
      by simp
    have future_not:
        "(\<exists>v. prefix w v \<and> v \<notin> P)
        \<longleftrightarrow> w \<notin> pp_b_box P"
    proof
      assume "\<exists>v. prefix w v \<and> v \<notin> P"
      then have "\<exists>u. w @ u \<notin> P"
        using pp_t_future_not_mem_iff[of w P] by blast
      then show "w \<notin> pp_b_box P"
        unfolding pp_b_box_def by blast
    next
      assume "w \<notin> pp_b_box P"
      then have "\<exists>u. w @ u \<notin> P"
        unfolding pp_b_box_def by blast
      then show "\<exists>v. prefix w v \<and> v \<notin> P"
        using pp_t_future_not_mem_iff[of w P] by blast
    qed
    have not_box_is_possible_false:
        "w \<notin> pp_b_box P
        \<longleftrightarrow> w \<in> pp_b_diamond (- P)"
      using pp_b_not_box_neg_iff_diamond[of w "- P"]
      by simp
    show "w \<in> pp_b_operator_of
          (pp_t_closed_den pp_t_HO_not_leibniz_truth_term) P
        \<longleftrightarrow> w \<in> pp_b_possible_false P"
      unfolding pp_b_operator_of_def pp_b_of_zf_def
        pp_b_possible_false_def
      using term_semantics future_not not_box_is_possible_false
      by blast
  qed
next
  show "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_not_leibniz_false_term) =
        pp_b_diamond"
  proof (rule ext, rule set_eqI)
    fix P w
    have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    have term_semantics:
        "pp_t_holds
          ((pp_t_closed_den pp_t_HO_not_leibniz_false_term) \<acute>
            pp_zf_of_b P) w
        \<longleftrightarrow>
          \<not> pp_t_eqv Prop w
            (pp_zf_of_b P) (pp_zf_truth False)"
      using pp_t_HO_not_leibniz_false_holds[OF p, of w] .
    have false_equivalence_is_box:
        "pp_t_eqv Prop w
          (pp_zf_of_b P) (pp_zf_truth False)
        \<longleftrightarrow> w \<in> pp_b_box (- P)"
      by (rule pp_t_zf_of_b_eqv_false_iff)
    have not_box_is_possible:
        "w \<notin> pp_b_box (- P)
        \<longleftrightarrow> w \<in> pp_b_diamond P"
      by (rule pp_b_not_box_neg_iff_diamond)
    show "w \<in> pp_b_operator_of
          (pp_t_closed_den pp_t_HO_not_leibniz_false_term) P
        \<longleftrightarrow> w \<in> pp_b_diamond P"
      unfolding pp_b_operator_of_def pp_b_of_zf_def
      using term_semantics false_equivalence_is_box
        not_box_is_possible
      by blast
  qed
next
  show "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_forall_application_term) =
        pp_b_const_false"
  proof (rule ext, rule set_eqI)
    fix P w
    have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    show "w \<in> pp_b_operator_of
          (pp_t_closed_den pp_t_HO_forall_application_term) P
        \<longleftrightarrow> w \<in> pp_b_const_false P"
      unfolding pp_b_operator_of_def pp_b_of_zf_def
        pp_b_const_false_def
      using pp_t_HO_forall_application_never_holds[OF p, of w]
      by simp
  qed
next
  show "pp_b_operator_of
      (pp_t_closed_den pp_t_HO_exists_application_term) =
        pp_b_const_true"
  proof (rule ext, rule set_eqI)
    fix P w
    have p: "Elem (pp_zf_of_b P) (pp_t_domain Prop)"
      by (rule pp_zf_of_b_in_domain)
    show "w \<in> pp_b_operator_of
          (pp_t_closed_den pp_t_HO_exists_application_term) P
        \<longleftrightarrow> w \<in> pp_b_const_true P"
      unfolding pp_b_operator_of_def pp_b_of_zf_def
        pp_b_const_true_def
      using pp_t_HO_exists_application_always_holds[OF p, of w]
      by simp
  qed
qed

lemma pp_b_necessary_false_composition:
  "pp_b_necessary_false = pp_b_box \<circ> pp_b_complement"
  by (rule ext)
    (simp add: pp_b_necessary_false_def pp_b_complement_def)

lemma pp_b_possible_false_composition:
  "pp_b_possible_false = pp_b_diamond \<circ> pp_b_complement"
  by (rule ext)
    (simp add: pp_b_possible_false_def pp_b_complement_def)

lemma pp_b_HO_leibniz_terms_in_exact_stock:
  "pp_b_box \<in> pp_b_exact_stock"
  "pp_b_necessary_false \<in> pp_b_exact_stock"
  "pp_b_possible_false \<in> pp_b_exact_stock"
  "pp_b_diamond \<in> pp_b_exact_stock"
  "pp_b_const_false \<in> pp_b_exact_stock"
  "pp_b_const_true \<in> pp_b_exact_stock"
proof -
  show "pp_b_box \<in> pp_b_exact_stock"
    by (rule pp_b_exact_base_operators(4))
next
  have "pp_b_box \<circ> pp_b_complement \<in> pp_b_exact_stock"
    using pp_b_exact_base_operators(4) pp_b_exact_complement
    by (rule pp_b_exact_stock_compose)
  then show "pp_b_necessary_false \<in> pp_b_exact_stock"
    using pp_b_necessary_false_composition by simp
next
  have "pp_b_diamond \<circ> pp_b_complement \<in> pp_b_exact_stock"
    using pp_b_exact_base_operators(5) pp_b_exact_complement
    by (rule pp_b_exact_stock_compose)
  then show "pp_b_possible_false \<in> pp_b_exact_stock"
    using pp_b_possible_false_composition by simp
next
  show "pp_b_diamond \<in> pp_b_exact_stock"
    by (rule pp_b_exact_base_operators(5))
next
  show "pp_b_const_false \<in> pp_b_exact_stock"
    by (rule pp_b_exact_base_operators(3))
next
  show "pp_b_const_true \<in> pp_b_exact_stock"
    by (rule pp_b_exact_base_operators(2))
qed

theorem pp_b_HO_leibniz_terms_not_right_cancellative:
  "\<not> pp_b_exact_right_cancellative pp_b_box"
  "\<not> pp_b_exact_right_cancellative pp_b_necessary_false"
  "\<not> pp_b_exact_right_cancellative pp_b_possible_false"
  "\<not> pp_b_exact_right_cancellative pp_b_diamond"
proof -
  show "\<not> pp_b_exact_right_cancellative pp_b_box"
    by (rule pp_b_exact_box_not_right_cancellative)
next
  show "\<not> pp_b_exact_right_cancellative pp_b_necessary_false"
    unfolding pp_b_necessary_false_composition
    using pp_b_exact_complement
    by (rule pp_b_exact_box_left_composition_not_right_cancellative)
next
  show "\<not> pp_b_exact_right_cancellative pp_b_possible_false"
    unfolding pp_b_possible_false_composition
    using pp_b_exact_complement
    by (rule pp_b_exact_diamond_left_composition_not_right_cancellative)
next
  show "\<not> pp_b_exact_right_cancellative pp_b_diamond"
    by (rule pp_b_exact_diamond_not_right_cancellative)
qed

lemma pp_b_HO_quantified_terms_modally_factorable:
  "pp_b_exact_modally_factorable pp_b_box"
  "pp_b_exact_modally_factorable pp_b_necessary_false"
  "pp_b_exact_modally_factorable pp_b_possible_false"
  "pp_b_exact_modally_factorable pp_b_diamond"
  "pp_b_exact_modally_factorable pp_b_const_false"
  "pp_b_exact_modally_factorable pp_b_const_true"
proof -
  show "pp_b_exact_modally_factorable pp_b_box"
  proof (unfold pp_b_exact_modally_factorable_def,
      rule bexI[of _ id], rule bexI[of _ id])
    show "pp_b_box =
        id \<circ> (pp_b_box \<circ> id) \<or>
        pp_b_box =
        id \<circ> (pp_b_diamond \<circ> id)"
      by simp
    show "id \<in> pp_b_exact_stock"
      by (rule pp_b_exact_base_operators(1))
    show "id \<in> pp_b_exact_G"
      by (rule pp_b_exact_G_id)
  qed
next
  show "pp_b_exact_modally_factorable pp_b_necessary_false"
  proof (unfold pp_b_exact_modally_factorable_def,
      rule bexI[of _ id], rule bexI[of _ pp_b_complement])
    show "pp_b_necessary_false =
        id \<circ> (pp_b_box \<circ> pp_b_complement) \<or>
        pp_b_necessary_false =
        id \<circ> (pp_b_diamond \<circ> pp_b_complement)"
      using pp_b_necessary_false_composition by simp
    show "pp_b_complement \<in> pp_b_exact_stock"
      by (rule pp_b_exact_complement)
    show "id \<in> pp_b_exact_G"
      by (rule pp_b_exact_G_id)
  qed
next
  show "pp_b_exact_modally_factorable pp_b_possible_false"
  proof (unfold pp_b_exact_modally_factorable_def,
      rule bexI[of _ id], rule bexI[of _ pp_b_complement])
    show "pp_b_possible_false =
        id \<circ> (pp_b_box \<circ> pp_b_complement) \<or>
        pp_b_possible_false =
        id \<circ> (pp_b_diamond \<circ> pp_b_complement)"
      using pp_b_possible_false_composition by simp
    show "pp_b_complement \<in> pp_b_exact_stock"
      by (rule pp_b_exact_complement)
    show "id \<in> pp_b_exact_G"
      by (rule pp_b_exact_G_id)
  qed
next
  show "pp_b_exact_modally_factorable pp_b_diamond"
  proof (unfold pp_b_exact_modally_factorable_def,
      rule bexI[of _ id], rule bexI[of _ id])
    show "pp_b_diamond =
        id \<circ> (pp_b_box \<circ> id) \<or>
        pp_b_diamond =
        id \<circ> (pp_b_diamond \<circ> id)"
      by simp
    show "id \<in> pp_b_exact_stock"
      by (rule pp_b_exact_base_operators(1))
    show "id \<in> pp_b_exact_G"
      by (rule pp_b_exact_G_id)
  qed
next
  show "pp_b_exact_modally_factorable pp_b_const_false"
  proof (unfold pp_b_exact_modally_factorable_def,
      rule bexI[of _ id], rule bexI[of _ pp_b_const_false])
    show "pp_b_const_false =
        id \<circ> (pp_b_box \<circ> pp_b_const_false) \<or>
        pp_b_const_false =
        id \<circ> (pp_b_diamond \<circ> pp_b_const_false)"
      by (rule disjI1, rule ext)
        (simp add: pp_b_const_false_def pp_b_box_def)
    show "pp_b_const_false \<in> pp_b_exact_stock"
      by (rule pp_b_exact_base_operators(3))
    show "id \<in> pp_b_exact_G"
      by (rule pp_b_exact_G_id)
  qed
next
  show "pp_b_exact_modally_factorable pp_b_const_true"
  proof (unfold pp_b_exact_modally_factorable_def,
      rule bexI[of _ id], rule bexI[of _ pp_b_const_true])
    show "pp_b_const_true =
        id \<circ> (pp_b_box \<circ> pp_b_const_true) \<or>
        pp_b_const_true =
        id \<circ> (pp_b_diamond \<circ> pp_b_const_true)"
      by (rule disjI1, rule ext)
        (simp add: pp_b_const_true_def pp_b_box_def)
    show "pp_b_const_true \<in> pp_b_exact_stock"
      by (rule pp_b_exact_base_operators(2))
    show "id \<in> pp_b_exact_G"
      by (rule pp_b_exact_G_id)
  qed
qed

corollary pp_b_HO_application_terms_not_right_cancellative:
  "\<not> pp_b_exact_right_cancellative pp_b_const_false"
  "\<not> pp_b_exact_right_cancellative pp_b_const_true"
  using pp_b_HO_quantified_terms_modally_factorable(5,6)
    pp_b_exact_modally_factorable_not_right_cancellative
  by blast+

text \<open>
  These genuinely higher-order quantified terms therefore produce no new
  candidate against L2.  Four collapse to necessity, possibility, or their
  compositions with negation; the two unrestricted application quantifiers
  collapse to constant falsity and constant truth.  The generic Leibniz
  theorem explains the first four collapses uniformly and applies at every
  object-language type.
\<close>

end
